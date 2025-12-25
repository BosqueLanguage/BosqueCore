import * as fs from "fs";
import * as path from "path";
import { execSync } from "child_process";

import { fileURLToPath } from 'url';
const __dirname = path.dirname(fileURLToPath(import.meta.url));

import { Assembly } from "../frontend/assembly.js";
import { PackageConfig } from "../frontend/build_decls.js";
import { generateASM, workflowLoadUserSrc, setStatusEnabled } from "./workflows.js";
import { Monomorphizer } from "../backend/asmprocess/monomorphize.js";
import { ASMToIRConverter } from "../backend/asmprocess/flatten.js";
import { CPPEmitter } from "../backend/ircemit/cppemit.js";

const runcppdir = path.join(__dirname, "../../runcpp/");

let statusenabled = true;
const Status = {
    output: (msg: string) => {
        if(statusenabled) {
            process.stdout.write(msg);
        }
    },
    error: (msg: string) => {
        if(statusenabled) {
            process.stderr.write(msg);
        }
    }
};

function enableStatus() {
    statusenabled = true;
    setStatusEnabled(true);
}

let fullargs = [...process.argv].slice(2);
if(fullargs.length === 0) {
    Status.error("No input files specified!\n");
    process.exit(1);
}

let mainns = "Main";
let mainnsidx = fullargs.findIndex((v) => v === "--namespace");
if(mainnsidx !== -1) {
    mainns = fullargs[mainnsidx + 1];
    fullargs = fullargs.slice(0, mainnsidx).concat(fullargs.slice(mainnsidx + 2));
}

let outdir = path.join(path.dirname(path.resolve(fullargs[0])), "cppout");
let outdiridx = fullargs.findIndex((v) => v === "--output");
if(outdiridx !== -1) {
    outdir = fullargs[outdiridx + 1];
    fullargs = fullargs.slice(0, outdiridx).concat(fullargs.slice(outdiridx + 2));
}

function buildExeCode(assembly: Assembly, rootasm: string, outname: string) {
    Status.output("Monomorphizing code...\n");
    const iim = Monomorphizer.computeExecutableInstantiations(assembly, [rootasm]);

    Status.output("Generating IR code...\n");
    const ircode = ASMToIRConverter.generateIR(assembly, iim, undefined);

    Status.output("Emitting CPP code...\n");
    const cppcode = CPPEmitter.createEmitter(ircode);
    const maincode = cppcode.emitForCommandLine([`${mainns}::main`]);

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

function moveRuntimeFiles(buildlevel: "debug" | "test" | "release", outname: string) {
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

function emitCommandLineMakefile(optlevel: "debug" | "test" | "release"): string {
    return 'MAKE_PATH=$(realpath $(dir $(lastword $(MAKEFILE_LIST))))\n' +
        'RUNTIME_DIR=$(MAKE_PATH)/runcpp/\n' + 
        'OUT_OBJS=$(MAKE_PATH)/output/obj/\n\n' +
        'JSON_INCLUDES=-I $(BUILD_DIR)include/json/\n\n' +
        '#dev is default, for another flavor : make BUILD=release or debug\n' +
        `BUILD := ${optlevel}\n\n` + 
        'CPP_STDFLAGS=-Wall -Wextra -Wno-unused-parameter -Wuninitialized -Werror -std=gnu++20 -fno-exceptions -fno-rtti -fno-strict-aliasing -fno-stack-protector -fPIC\n' + 
        'CPPFLAGS_OPT.debug=-O0 -g -ggdb -fno-omit-frame-pointer -fsanitize=address\n' +
        'CPPFLAGS_OPT.test=-O0 -g -ggdb -fno-omit-frame-pointer\n' +
        'CPPFLAGS_OPT.release=-O3 -march=x86-64-v3\n' +
        'CPPFLAGS=${CPPFLAGS_OPT.${BUILD}} ${CPP_STDFLAGS}\n\n' +
        'HEADERS=$(wildcard $(SRC_DIR)*.h) $(wildcard $(CORE_SRC_DIR)*.h) $(wildcard $(RUNTIME_SRC_DIR)*.h) $(wildcard $(ALLOC_SRC_DIR)*.h) $(wildcard $(BSQIR_SRC_DIR)*.h)\n' +
        '#MAKEFLAGS += -j4\n\n' +
        'all: $(MAKE_PATH)/app\n\n' +
        '$(MAKE_PATH)/app: $(MAKE_PATH)/app.h $(MAKE_PATH)/app.cpp\n' +
        '\t@make -f $(RUNTIME_DIR)makefile BUILD=$(BUILD) all\n' +
        '\tg++ $(CPPFLAGS) -o $(MAKE_PATH)/app $(OUT_OBJS)* $(JSON_INCLUDES) $(MAKE_PATH)/app.cpp\n';
}

function getSimpleFilename(fn: string): string {
    return path.basename(fn);
}

function checkAssembly(srcfiles: string[]): Assembly | undefined {
    const lstart = Date.now();
    Status.output("Loading user sources...\n");
    const usersrcinfo = workflowLoadUserSrc(srcfiles);
    if(usersrcinfo === undefined) {
        Status.error("Failed to load user sources!\n");
        return;
    }
    const dend = Date.now();
    Status.output(`    User sources loaded [${(dend - lstart) / 1000}s]\n\n`);

    const userpackage = new PackageConfig([], usersrcinfo)
    const [asm, perrors, terrors] = generateASM(userpackage);

    if(perrors.length === 0 && terrors.length === 0) {
        return asm;
    }
    else {
        Status.error("Failed to generate assembly!\n");

        //TODO -- need to do filename in error and sort nicely
        perrors.sort((a, b) => (a.srcfile !== b.srcfile) ? a.srcfile.localeCompare(b.srcfile) : a.sinfo.line - b.sinfo.line);
        for(let i = 0; i < perrors.length; ++i) {
            Status.error(`Parser Error @ ${getSimpleFilename(perrors[i].srcfile)}#${perrors[i].sinfo.line}: ${perrors[i].message}\n`);
        }

        terrors.sort((a, b) => (a.file !== b.file) ? a.file.localeCompare(b.file) : a.line - b.line);
        if(terrors.length !== 0) {
            for(let i = 0; i < terrors.length; ++i) {
                Status.error(`Type Error @ ${getSimpleFilename(terrors[i].file)}#${terrors[i].line}: ${terrors[i].msg}\n`);
            }
        }

        return undefined;
    }
}

//////////////////////////////
enableStatus();

const asm = checkAssembly(fullargs);
if(asm === undefined) {
    process.exit(1);
}

Status.output(`-- CPP output directory: ${outdir}\n\n`);

fs.rmSync(outdir, { recursive: true, force: true });
fs.mkdirSync(outdir);

buildExeCode(asm, mainns, outdir);
moveRuntimeFiles("debug", outdir);

Status.output("All done!\n");
