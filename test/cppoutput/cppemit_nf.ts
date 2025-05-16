import * as fs from "fs";
import * as path from "path";

import assert from "node:assert"

import { generateASMCPP } from '../../src/cmd/workflows.js';
import { Assembly } from '../../src/frontend/assembly.js';
import { InstantiationPropagator } from "../../src/frontend/closed_terms.js";

import { fileURLToPath } from 'url';
import { PackageConfig } from "../../src/frontend/build_decls.js";
import { execSync } from "child_process";
const __dirname = path.dirname(fileURLToPath(import.meta.url));

const bosque_dir: string = path.join(__dirname, "../../../");
const cpp_transform_bin_path = path.join(bosque_dir, "bin/cppemit/CPPEmitter.mjs");

// We WILL need this to be able to check results when we exec our emitted cpp
// const cpp_runtime_code_path = path.join(bosque_dir, "bin/cppruntime/emit.cpp");

import { tmpdir } from 'node:os';
import { BSQIREmitter } from "../../src/frontend/bsqir_emit.js";
import { validateCStringLiteral } from "@bosque/jsbrex";

// Just so if we change the namespace our tests dont break
const cppns: string = "__CoreCpp::";

//
// We will first do our tests by simply comparing the spat out result (after running our cpp emit)
// and ensure it matches the anticipated cpp output.
//
// Then once this is functional we will add another parameter where we can check the anticipated result
// after executing the generatec cpp code. Likely will want to make this optional.
// (we may not care about what the result is, just that the emitted cpp matches what we anticipate.)
//

function buildMainCode(assembly: Assembly, outname: string): string | undefined {
    const iim = InstantiationPropagator.computeInstantiations(assembly, "Main");
    const tinfo = BSQIREmitter.emitAssembly(assembly, iim);

    const nndir = path.normalize(outname);
    const fname = path.join(nndir, "bsqir.bsqon");

    try {
        fs.writeFileSync(fname, tinfo);
    }
    catch(e) {      
        return undefined;
    }

    let res = "";
    try {
        res = execSync(`node ${cpp_transform_bin_path} --file ${fname}`).toString();
    }
    catch(e) {      
        return undefined;
    }

    return validateCStringLiteral(res.slice(1, -1));
}

function buildCppAssembly(srcfile: string): Assembly | undefined {
    const userpackage = new PackageConfig([], [{ srcpath: "test.bsq", filename: "test.bsq", contents: srcfile }]);
    const [asm, perrors, terrors] = generateASMCPP(userpackage);

    if(perrors.length === 0 && terrors.length === 0) {
        return asm;
    }
    else {
        return undefined;
    }
}

//
// Remove extra fluff and grab only body of main 
//
function formatOutputCpp(cpp: string) {
    let formatted = cpp.replace(/(\r\n|\n|\r)/gm, "");
    
    const body = formatted.match(/\{([\s\S]*)\}/);
    if (body && body[1]) {
        formatted = body[1].trim();
        
        const inner = formatted.match(/\{([\s\S]*)\}/);
        if(inner && inner[1]) {
            formatted = inner[1].trim();
        }
    }
    
    return formatted;
}

//
// Not sure if we need cpp_output here
//
function execMainCode(bsqcode: string, cpp_output: string) {
    const nndir = fs.mkdtempSync(path.join(tmpdir(), "bosque-cpptest-"));

    let result = "";
    try {
        const cppasm = buildCppAssembly("declare namespace Main;\n\n" + bsqcode);
        if(cppasm === undefined) {
            result = `[FAILED TO BUILD CPP ASSEMBLY] \n\n ${bsqcode}`;
        }
        else {
            const cpp = buildMainCode(cppasm, nndir);
            if(cpp === undefined) {
                result = `[FAILED TO BUILD MAIN CODE] \n\n ${bsqcode}`;
            }
            else {
                // We will want to eventually be able to exec the code here
                // For now we just assign result to be the emitted cpp code for comparisons
                result = cpp;
            }
        }
    }
    catch(e) {
        result = `[Unexpected error ${e}]`;
    }
    finally {
        fs.rmSync(nndir, { recursive: true});
    }
    return formatOutputCpp(result);
}

function runMainCode(bsqcode: string, cpp_output: string) {
    const emitted_cpp = execMainCode(bsqcode, cpp_output);

    //
    // Need to do some cleanup with what it spits out, we are only interested
    // in what main contains.
    //

    // See if emitted cpp matches what we expect
    assert.equal(cpp_output, emitted_cpp);
}

export { cppns, runMainCode};