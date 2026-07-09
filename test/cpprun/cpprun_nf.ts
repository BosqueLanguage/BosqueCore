import * as fs from "fs";
import * as path from "path";
import { execSync } from "child_process";
import { tmpdir } from 'node:os';

import { fileURLToPath } from 'url';
const __dirname = path.dirname(fileURLToPath(import.meta.url));

import assert from "node:assert";

import { PackageConfig } from "../../src/frontend/build_decls.js";
import { generateASMTest } from '../../src/cmd/workflows.js';
import { Assembly } from '../../src/frontend/assembly.js';
import { Monomorphizer } from "../../src/backend/asmprocess/monomorphize.js";
import { ASMToIRConverter } from "../../src/backend/asmprocess/flatten.js";
import { CPPEmitter } from "../../src/backend/ircemit/cppemit.js";

const runcppdir = path.join(__dirname, "../../runcpp/");

function buildAssembly(srcfile: string): Assembly | undefined {
    const userpackage = new PackageConfig(["EXEC_LIBS", "STRIPPED_CORE"], [{ srcpath: "test.bsq", filename: "test.bsq", contents: srcfile }]);
    const [asm, perrors, terrors] = generateASMTest(userpackage);

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
    const maincode = cppcode.emitForCommandLine(`Main::main`);
    
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
        'SRC_DIR=$(MAKE_PATH)/runcpp/\n' + 
        'CORE_SRC_DIR=$(SRC_DIR)core/\n' +
        'RUNTIME_SRC_DIR=$(SRC_DIR)runtime/\n' +
        'ALLOC_SRC_DIR=$(RUNTIME_SRC_DIR)allocator/\n' +
        'BSQIR_SRC_DIR=$(RUNTIME_SRC_DIR)bsqir/\n' +
        '\n' +
        'CPPFLAGS=-O0 -g -ggdb -fsanitize=address --param asan-stack=0 -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable -Wno-unused-but-set-variable -Wuninitialized -Werror -std=gnu++23 -fno-omit-frame-pointer -fno-exceptions -fno-rtti -fno-strict-aliasing -fno-stack-protector\n' + 
        'HEADERS=$(wildcard $(SRC_DIR)*.h) $(wildcard $(CORE_SRC_DIR)*.h) $(wildcard $(RUNTIME_SRC_DIR)*.h) $(wildcard $(ALLOC_SRC_DIR)*.h) $(wildcard $(BSQIR_SRC_DIR)*.h)\n' +
        'CPP=$(wildcard $(SRC_DIR)*.cpp) $(wildcard $(CORE_SRC_DIR)*.cpp) $(wildcard $(RUNTIME_SRC_DIR)*.cpp) $(wildcard $(ALLOC_SRC_DIR)*.cpp) $(wildcard $(BSQIR_SRC_DIR)*.cpp)\n' +
        '\n' +
        'all: $(MAKE_PATH)/app\n\n' +
        '$(MAKE_PATH)/app: $(HEADERS) $(CPP) $(MAKE_PATH)/app.h $(MAKE_PATH)/app.cpp\n' +
        '\tg++ $(CPPFLAGS) -o $(MAKE_PATH)/app $(CPP) $(MAKE_PATH)/app.cpp\n'
        ;
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

function runError(exepath: string, input: string | undefined): void {
    try {
        const cmd = input === undefined ? `${exepath}` : `${exepath} '${input}'`;
        const result = execSync(cmd).toString();
        assert.fail(`Execution did not trigger error as expected -- ${result}`);
    }
    catch(e: any) {
        //console.log(e["stderr"].toString());
        //assert(e["stderr"].toString().trim().includes("xx"), `Expected error containing '${errstr}' but got: ${e}`);        
    }
}

function runTestSet(code: string, normalexecs: [string | undefined, string][], errorexecs: (string | undefined)[]): void {
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
            const input = errorexecs[i];
            runError(exepath, input);
        }
    }
    finally {
        fs.rmSync(nndir, { recursive: true });
    }
}

export {
    runTestSet
};
