import assert from "node:assert";

import { PackageConfig } from "../../src/frontend/build_decls.js";
import { generateASM } from '../../src/cmd/workflows.js';
import { Assembly } from '../../src/frontend/assembly.js';
import { Monomorphizer } from "../../src/backend/asmprocess/monomorphize.js";
import { ASMToIRConverter } from "../../src/backend/asmprocess/flatten.js";
import { CPPEmitter } from "../../src/backend/ircemit/cppemit.js";

function wsnorm(s: string): string {
    return s.trim().replace(/\s+/g, " ");
}

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

function buildMainCode(assembly: Assembly): string {
    const iim = Monomorphizer.computeExecutableInstantiations(assembly, ["Main"]);
    const ircode = ASMToIRConverter.generateIR(assembly, iim, undefined);

    const cppcode = CPPEmitter.createEmitter(ircode);
    const maincode = cppcode.emitInvokeForKey("Main::main");

    return wsnorm(maincode);
}

function checkTestEmitMainFunction(code: string, expected: string) {
    const asm = buildAssembly(code);
    if(asm === undefined) {
        assert.fail("Assembly generation failed");
    }
        
    const ccode = buildMainCode(asm);
    assert.equal(ccode, expected);
}

export {
    checkTestEmitMainFunction
};
