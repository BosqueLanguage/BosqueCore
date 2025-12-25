import * as fs from "fs";
import * as path from "path";
import { execSync } from "child_process";
import { tmpdir } from 'node:os';

import { fileURLToPath } from 'url';
const __dirname = path.dirname(fileURLToPath(import.meta.url));

import assert from "node:assert";

import { PackageConfig } from "../../src/frontend/build_decls.js";
import { generateASM } from '../../src/cmd/workflows.js';
import { Assembly } from '../../src/frontend/assembly.js';
import { Monomorphizer } from "../../src/backend/asmprocess/monomorphize.js";
import { ASMToIRConverter } from "../../src/backend/asmprocess/flatten.js";
import { CPPEmitter } from "../../src/backend/ircemit/cppemit.js";

const runcppdir = path.join(__dirname, "../../runcpp/");

function buildAssembly(srcfile: string): Assembly | undefined {
    const userpackage = new PackageConfig(["EXEC_LIBS", "STRIPPED_CORE"], [{ srcpath: "test.bsq", filename: "test.bsq", contents: srcfile }]);
    const [asm, perrors, terrors] = generateASM(userpackage);

    if(perrors.length === 0 && terrors.length === 0) {
        return asm;
    }
    else {
        return undefined;
    }
}

function buildMainCode(assembly: Assembly, outname: string): boolean {
    const iim = Monomorphizer.computeExecutableInstantiations(assembly, ["Main"]);
    const ircode = ASMToIRConverter.generateIR(assembly, iim, undefined);

    const cppcode = CPPEmitter.createEmitter(ircode);
    const maincode = cppcode.emitForCommandLine([`Main::main`]);
    
    const nndir = path.normalize(outname);
    try {
        const hname = path.join(nndir, `app.h`);
        fs.writeFileSync(hname, maincode[0]);
    
        const cname = path.join(nndir, `app.cpp`);
        fs.writeFileSync(cname, maincode[1]);
    }
    catch(e) {      
        return false;
    }

    return true;
}

function emitCommandLineMakefile(): string {
    return 'MAKE_PATH=$(realpath $(dir $(lastword $(MAKEFILE_LIST))))\n' +
        'RUNTIME_DIR=$(MAKE_PATH)/runcpp/\n' + 
        'OUT_OBJS=$(MAKE_PATH)/output/obj/\n\n' +
        'JSON_INCLUDES=-I $(BUILD_DIR)include/json/\n\n' +
        '#dev is default, for another flavor : make BUILD=release or debug\n' +
        `BUILD := debug\n\n` + 
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

function moveRuntimeFiles(outname: string): boolean {
    const nndir = path.normalize(outname);

    const makefile = emitCommandLineMakefile();
    try {
        const dstpath = path.join(nndir, "runcpp/");

        fs.mkdirSync(dstpath, {recursive: true});
        execSync(`cp -R ${runcppdir}* ${dstpath}`);

        fs.writeFileSync(path.join(nndir, "Makefile"), makefile);
    }
    catch(e) {
        return false;
    }

    return true;
}

function runCPPBuild(code: string, nndir: string): string | undefined {
    let result: string | undefined = undefined;
    try {
        const asm = buildAssembly("declare namespace Main;\n\n" + code);
        if(asm === undefined) {
            result = `[FAILED TO BUILD ASSEMBLY] \n\n ${code}`;
        }
        else {
            if(!buildMainCode(asm, nndir)) {
                result = `[FAILED TO BUILD MAIN CODE] \n\n ${code}`;
            }
            else {
                if(!moveRuntimeFiles(nndir)) {
                    result = `[FAILED TO MOVE RUNTIME FILES] \n\n ${code}`;
                }
                else {
                    const mfpath = path.join(nndir, "Makefile");
                    execSync(`make -f ${mfpath} all`);
                }
            }
        }
    }
    catch(e) {
        result = `[Unexpected error ${e}]`;
    }
    
    return result;
}

function runNormal(exepath: string, input: string | undefined, expected: string): void {
    try {
        const cmd = input === undefined ? `${exepath}` : `${exepath} '${input}'`;
        const result = execSync(cmd).toString();
        assert.equal(result.trim(), expected);
    }
    catch(e) {
        assert.fail(`Execution got error: ${e}`);
    }
}

function runError(exepath: string, input: string | undefined, errstr: string): void {
    try {
        const cmd = input === undefined ? `${exepath}` : `${exepath} '${input}'`;
        const result = execSync(cmd).toString();
        assert(result.trim().includes(errstr), `Expected error containing '${errstr}' but got: ${result}`);
    }
    catch(e) {
        assert.fail(`Execution got error: ${e}`);
    }
}

function runTestSet(code: string, normalexecs: [string | undefined, string][], errorexecs: [string | undefined, string][]): void {
    const nndir = fs.mkdtempSync(path.join(tmpdir(), "bosque-test-"));

    try {
        const emssg = runCPPBuild(code, nndir);
        assert.equal(emssg, undefined);

        const exepath = path.join(nndir, "app");

        for(let i = 0; i < normalexecs.length; ++i) {
            const [input, expected] = normalexecs[i];
            runNormal(exepath, input, expected);
        }
    
        for(let i = 0; i < errorexecs.length; ++i) {
            const [input, errstr] = errorexecs[i];
            runError(exepath, input, errstr);
        }
    }
    finally {
        fs.rmSync(nndir, { recursive: true });
    }
}

export {
    runTestSet
};
