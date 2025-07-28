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
const cpp_emit_runtime_path = path.join(bosque_dir, "bin/cppruntime/");
const cpp_emit_runtime_src_path = path.join(cpp_emit_runtime_path, "emit.cpp");
const cpp_emit_runtime_header_path = path.join(cpp_emit_runtime_path, "emit.hpp");
const cpp_runtime_header_path = path.join(cpp_emit_runtime_path, "cppruntime.hpp");
const makefile_path = path.join(cpp_emit_runtime_path, "makefile");
const gc_path = path.join(bosque_dir, "bin/cppruntime/gc/");
const output_path = path.join(bosque_dir, "bin/cppruntime/output/");

const bsq_max_int: string = "4611686018427387903";
const bsq_min_int: string = "-4611686018427387903";
const bsq_max_nat: string = "4611686018427387903";
const bsq_max_bignat: string = "85070591730234615865843651857942052863";
const bsq_max_bigint: string = "85070591730234615865843651857942052863";
const bsq_min_bigint: string = "-85070591730234615865843651857942052863";

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

function generateCPPFiles(header: string, src: string, outdir: string): boolean {
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
        fs.writeFileSync(srcname, updated);
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

function execMainCode(bsqcode: string, expect_err: boolean) {
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
                if(!generateCPPFiles(header, src, nndir)) {
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

function runMainCode(bsqcode: string, expected_output: string) {
    const cpp_output = execMainCode(bsqcode, false);
    assert.equal(cpp_output, expected_output);
}

function runMainCodeError(bsqcode: string, error_msg: string) {
    const cpp_err_msg = execMainCode(bsqcode, true);
    assert.equal(cpp_err_msg, error_msg);   
}

export {runMainCode, runMainCodeError, bsq_max_int, bsq_max_nat, bsq_max_bigint, bsq_max_bignat, bsq_min_int, bsq_min_bigint};