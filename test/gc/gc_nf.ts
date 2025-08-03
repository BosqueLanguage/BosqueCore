import * as fs from "fs";
import * as path from "path";

const gc_test_path = "bin/cppruntime/gc/test/";

import assert from "node:assert";

// import { runMainCode } from "../cppoutput/cppemit_nf.js";
import { generateASMCPP } from '../../src/cmd/workflows.js';
import { Assembly } from '../../src/frontend/assembly.js';
import { InstantiationPropagator } from "../../src/frontend/closed_terms.js";

import { fileURLToPath } from 'url';
import { PackageConfig } from "../../src/frontend/build_decls.js";
import { execSync } from "child_process";
const __dirname = path.dirname(fileURLToPath(import.meta.url));

const bosque_dir: string = path.join(__dirname, "../../../");
const cpp_transform_bin_path = path.join(bosque_dir, "bin/cppemit/CPPEmitter.mjs");
const cpp_emit_runtime_path = path.join(bosque_dir, "bin/cppruntime/");
const cpp_emit_runtime_src_path = path.join(cpp_emit_runtime_path, "emit.cpp");
const cpp_emit_runtime_header_path = path.join(cpp_emit_runtime_path, "emit.hpp");
const cpp_runtime_header_path = path.join(cpp_emit_runtime_path, "cppruntime.hpp");
const makefile_path = path.join(cpp_emit_runtime_path, "makefile");
const gc_path = path.join(bosque_dir, "bin/cppruntime/gc/");
const output_path = path.join(bosque_dir, "bin/cppruntime/output/");

import { tmpdir } from 'node:os';
import { BSQIREmitter } from "../../src/frontend/bsqir_emit.js";
import { validateStringLiteral } from "@bosque/jsbrex";

function buildMainCode(assembly: Assembly, outname: string): [string, string] | undefined{
    const iim = InstantiationPropagator.computeExecutableInstantiations(assembly, ["Main"]);
    const tinfo = BSQIREmitter.emitAssembly(assembly, iim);

    const nndir = path.normalize(outname);
    const fname = path.join(nndir, "bsqir.bsqon");

    try {
        fs.writeFileSync(fname, tinfo);
    }
    catch(e) {      
        return undefined;
    }

    let res = ["", ""];
    try {
        const fname = path.join(nndir, "bsqir.bsqon");
        let exec = execSync(`node ${cpp_transform_bin_path} --file ${fname}`).toString();
        const boldstr = "𝐬𝐫𝐜";
        const boldidx = exec.indexOf(boldstr);
        
        res[0] = exec.substring(0, boldidx);
        res[1] = exec.substring(boldidx + boldstr.length);
    }
    catch(e) {      
        return undefined;
    }

    return [validateStringLiteral(res[0].slice(1)), validateStringLiteral(res[1].slice(0, -2))];
}

function copyGC(src: string, dst: string) {
    if (!fs.existsSync(dst)) {
        fs.mkdirSync(dst, { recursive: true });
    }
    
    const files = fs.readdirSync(src);

    files.forEach(file => {
        const currentPath = path.join(src, file);
        const newPath = path.join(dst, file);
        if(fs.statSync(currentPath).isDirectory()) {
            copyGC(currentPath, newPath);
        }
        else {
            fs.copyFileSync(currentPath, newPath);
        }
    });
}

function copyFile(src: string, dst: string) {
    const dir = path.normalize(dst);
    if (!fs.existsSync(dir)) {
        fs.mkdirSync(dir, { recursive: true });
    }

    const runtimeDstPath = path.join(dir, path.basename(src));
    fs.copyFileSync(src, runtimeDstPath); 
}

function generateCPPFiles(header: string, src: string, cppmain: string, outdir: string): boolean {
    const dir = path.normalize(outdir);

    let srcbase: string = "";
    let headerbase: string = "";
    try {
        srcbase = fs.readFileSync(cpp_emit_runtime_src_path).toString();
        headerbase = fs.readFileSync(cpp_emit_runtime_header_path).toString();
    }
    catch(e) {
        return false;
    }
    
    try {
        const headername = path.join(dir, "emit.hpp");
        const updated = headerbase.concat(header);
        fs.writeFileSync(headername, updated);
    }
    catch(e) {
        return false;
    }

    try {
        const srcname = path.join(dir, "emit.cpp");
        let updated = srcbase.replace("//CODE", src);
        let insert = updated.replace(/__CoreCpp::\w+ Main::main\([^)]*\)\s*\{[^}]*\}/gs, cppmain);
        fs.writeFileSync(srcname, insert);
    }
    catch(e) {
        return false;
    }

    try {
        copyFile(cpp_runtime_header_path, outdir);
        copyFile(makefile_path, outdir);
        copyGC(gc_path, path.join(outdir, "gc/"));
        copyGC(output_path, path.join(outdir, "output/"));
    }
    catch(e) {
        return false;
    }
    return true;
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

function execMainCode(bsqcode: string, cppmain: string, expect_err: boolean) {
    const nndir = fs.mkdtempSync(path.join(tmpdir(), "bosque-cpptest-"));

    let result = "";
    try {
        const cppasm = buildCppAssembly("declare namespace Main;\n\n" + bsqcode);
        if(cppasm === undefined) {
            return `[FAILED TO BUILD CPP ASSEMBLY] \n\n ${cppasm}`;
        }
        else {
            const build = buildMainCode(cppasm, nndir);
            if(build === undefined) {
                return `[FAILED TO BUILD MAIN CODE] \n\n ${cppasm}`;
            }
            else {
                const [header, src] = build;
                if(!generateCPPFiles(header, src, cppmain, nndir)) {
                    return `[FAILED TO GENERATE CPP FILE] \n\n ${header} ${src}`;
                }
                else {
                    const output_path = path.join(nndir, "output/memex");
                    
                    try {
                        execSync(`make`, {cwd: nndir});
                    }
                    catch {
                        return `[CPP COMPILATION ERROR] \n\n ${header} ${src} `
                    }

                    try {
                        result = execSync(output_path).toString().trim();
                    }
                    catch(e) {
                        if(expect_err) {
                            result = (e as any).stdout.toString();
                        }
                        else {
                            return `[C++ RUNTIME ERROR] \n\n ${header} ${src}`;
                        }
                    }
                } 
            }
        }
    }
    catch(e) {
        result = `[Unexpected error ${e}]`;
    }
    finally {
        fs.rmSync(nndir, { recursive: true});
    }
    return result;
}

//
// TODO: Once we get this up and running we should go through and find the functions
// that are same on cppemit_nf.ts and remove
//

function runMainCodeGC(testname: string, cppmain: string, expected_output: string) {
    const test_contents = fs.readFileSync(path.join(gc_test_path, testname.concat(".bsq"))).toString();

    const results = execMainCode(test_contents, cppmain, false);
    assert.equal(results, expected_output)
}

export { runMainCodeGC };