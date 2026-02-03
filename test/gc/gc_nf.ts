import * as fs from "fs";
import * as path from "path";

import assert from "node:assert";

import { buildMainCode, copyGC, copyFile, buildCppAssembly } from "../cppoutput/cppemit_nf.js"

import { fileURLToPath } from 'url';
import { execSync } from "child_process";
import { tmpdir } from 'node:os';

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const bosque_dir: string = path.join(__dirname, "../../../");
const cpp_emit_runtime_path = path.join(bosque_dir, "bin/cppruntime/");
const cpp_emit_runtime_src_path = path.join(cpp_emit_runtime_path, "emit.cpp");
const cpp_emit_runtime_header_path = path.join(cpp_emit_runtime_path, "emit.hpp");
const cpp_runtime_header_path = path.join(cpp_emit_runtime_path, "cppruntime.hpp");
const cpp_runtime_source_path = path.join(cpp_emit_runtime_path, "cppruntime.cpp");
const makefile_path = path.join(cpp_emit_runtime_path, "makefile");
const gc_path = path.join(bosque_dir, "bin/cppruntime/gc/");
const output_path = path.join(bosque_dir, "bin/cppruntime/output/");
const gc_test_path = "bin/cppruntime/gc/test/";

// set up global array, disable stack refs
const base = `__CoreCpp::Bool main() {\n
	\tGlobalDataStorage::g_global_data.initialize(sizeof(garray), (void**)garray);\n
	\tg_disable_stack_refs = true;\n`;
const end = "\n\treturn true;}"

function generateCPPFiles(header: string, src: string, cppmain: string, cpp_testcode: string, outdir: string): boolean {
    const dir = path.normalize(outdir);

    // We concat our tests into the source file
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
        //
        // We may need more slots for heavy testing!
        //
        let garray = "void* garray[15] { nullptr };\n";
        let tests = garray.concat(cpp_testcode).concat(src);
        const srcname = path.join(dir, "emit.cpp");
        let updated = srcbase.replace("//CODE", tests);
        let insert = updated.replace(/__CoreCpp::\w+\s+main\s*\([^)]*\)\s*\w*\s*\{[^}]*\}/gs, cppmain);

        fs.writeFileSync(srcname, insert);
    }
    catch(e) {
        return false;
    }

    try {
        copyFile(cpp_runtime_header_path, outdir);
        copyFile(cpp_runtime_source_path, outdir);
        copyFile(makefile_path, outdir);
		copyGC(gc_path, path.join(outdir, "gc/"));
        copyGC(output_path, path.join(outdir, "output/"));
    }
    catch(e) {
        return false;
    }
    return true;
}

function execMainCode(bsqcode: string, cpp_testcode: string, cppmain: string, expect_err: boolean) {
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
                if(!generateCPPFiles(header, src, cppmain, cpp_testcode, nndir)) {
                    return `[FAILED TO GENERATE CPP FILE] \n\n ${header} ${src}`;
                }
                else {
                    const output_path = path.join(nndir, "output/memex");
                    
                    try {
						execSync(`make BUILD=test`, {cwd: nndir});
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

function runMainCodeGC(testname: string, cppmain: string, expected_output: string) {
    const test_dir = path.join(gc_test_path, `${testname}/`);
    const test_contents = fs.readFileSync(path.join(test_dir, testname.concat(".bsq"))).toString();
    const cpp_test_contents = fs.readFileSync(path.join(test_dir, testname.concat(".cpp"))).toString();

    const results = execMainCode(test_contents, cpp_test_contents, cppmain, false);
    assert.equal(results, expected_output)
}

export { runMainCodeGC, base, end };
