import * as fs from "fs";
import * as path from "path";
import { execSync } from "child_process";

import { fileURLToPath } from 'url';
const __dirname = path.dirname(fileURLToPath(import.meta.url));

import { Assembly } from "../frontend/assembly.js";
import { checkAssembly, parseArgv } from "./workflows.js";
import { Monomorphizer } from "../backend/asmprocess/monomorphize.js";
import { ASMToIRConverter } from "../backend/asmprocess/flatten.js";
import { CPPEmitter } from "../backend/ircemit/cppemit.js";
import { Status } from "./status_output.js"

const runcppdir = path.join(__dirname, "../../runcpp/");

const [fullargs, mainns, outdir] = parseArgv("cppout", ...process.argv);

function buildExeCode(assembly: Assembly, rootasm: string, outname: string) {
    Status.output("Monomorphizing code...\n");
    const iim = Monomorphizer.computeExecutableInstantiations(assembly, [rootasm]);

    Status.output("Generating IR code...\n");
    const ircode = ASMToIRConverter.generateIR(assembly, iim, undefined);

    Status.output("Emitting CPP code...\n");
    const cppcode = CPPEmitter.createEmitter(ircode);
    const maincode = cppcode.emitForCommandLine(`${mainns}::main`);

    Status.output("    Writing CPP code to disk...\n");
    const nndir = path.normalize(outname);
    try {
        const hname = path.join(nndir, `app.h`);
        fs.writeFileSync(hname, maincode[0]);

        const cname = path.join(nndir, `app.cpp`);
        fs.writeFileSync(cname, maincode[1]);
    }
    catch(e) {      
        Status.error("Failed to write output files!\n");
    }

    Status.output(`    Code generation successful -- CPP emitted to ${nndir}\n\n`);
}

function moveRuntimeFiles(buildlevel: "testing" | "release", outname: string) {
    Status.output("    Copying CPP runtime support...\n");
    const nndir = path.normalize(outname);

    const makefile = emitCommandLineMakefile(buildlevel);
    try {
        const dstpath = path.join(nndir, "runcpp/");

        fs.mkdirSync(dstpath, {recursive: true});
        execSync(`cp -R ${runcppdir}* ${dstpath}`);

        fs.writeFileSync(path.join(nndir, "Makefile"), makefile);
    }
    catch(e) {
        Status.error("Failed to copy runtime files!\n");
    }
}

function emitCommandLineMakefile(optlevel: "testing" | "release"): string {
    return 'MAKE_PATH=$(realpath $(dir $(lastword $(MAKEFILE_LIST))))\n' +
        'SRC_DIR=$(MAKE_PATH)/runcpp/\n' + 
        'CORE_SRC_DIR=$(SRC_DIR)core/\n' +
        'RUNTIME_SRC_DIR=$(SRC_DIR)runtime/\n' +
        'ALLOC_SRC_DIR=$(RUNTIME_SRC_DIR)allocator/\n' +
        'BSQIR_SRC_DIR=$(RUNTIME_SRC_DIR)bsqir/\n' +
        '\n' +
        '#testing is default, for another flavor : make BUILD=release or debug\n' +
        `BUILD := ${optlevel}\n\n` + 
        'CPP_STDFLAGS=-Wall -Wextra -Wno-unused-parameter -Wno-unused-variable -Wno-unused-but-set-variable -Wuninitialized -Werror -std=gnu++20 -fno-omit-frame-pointer -fno-exceptions -fno-rtti -fno-strict-aliasing -fno-stack-protector\n' + 
        'CPPFLAGS_OPT.testing=-O0 -g -ggdb -fsanitize=address --param asan-stack=0\n' +
        'CPPFLAGS_OPT.testingopt=-O1 -g -ggdb -fsanitize=address --param asan-stack=0\n' +
        'CPPFLAGS_OPT.release=-O2 -g -ggdb -flto -ftree-vectorize -march=native -Wno-array-bounds -Wno-stringop-overflow\n' +
        'CPPFLAGS=${CPPFLAGS_OPT.${BUILD}} ${CPP_STDFLAGS}\n\n' +
        'HEADERS=$(wildcard $(SRC_DIR)*.h) $(wildcard $(CORE_SRC_DIR)*.h) $(wildcard $(RUNTIME_SRC_DIR)*.h) $(wildcard $(ALLOC_SRC_DIR)*.h) $(wildcard $(BSQIR_SRC_DIR)*.h)\n' +
        'CPP=$(wildcard $(SRC_DIR)*.cpp) $(wildcard $(CORE_SRC_DIR)*.cpp) $(wildcard $(RUNTIME_SRC_DIR)*.cpp) $(wildcard $(ALLOC_SRC_DIR)*.cpp) $(wildcard $(BSQIR_SRC_DIR)*.cpp)\n' +
        '\n' +
        'all: $(MAKE_PATH)/app\n\n' +
        '$(MAKE_PATH)/app: $(HEADERS) $(CPP) $(MAKE_PATH)/app.h $(MAKE_PATH)/app.cpp\n' +
        '\tg++ $(CPPFLAGS) -o $(MAKE_PATH)/app $(CPP) $(MAKE_PATH)/app.cpp\n' +
        'clean:\n' +
	    '\trm $(MAKE_PATH)/app';
}

//////////////////////////////
Status.enable();

const asm = checkAssembly(fullargs, "cpp");
if(asm === undefined) {
    process.exit(1);
}

Status.output(`-- CPP output directory: ${outdir}\n\n`);

fs.rmSync(outdir, { recursive: true, force: true });
fs.mkdirSync(outdir);

buildExeCode(asm, mainns, outdir);
moveRuntimeFiles("testing", outdir);

Status.output("All done!\n");