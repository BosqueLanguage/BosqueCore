import * as fs from "fs";
import * as path from "path";

import assert from "node:assert";

import { generateASMSMT } from '../../src/cmd/workflows.js';
import { Assembly } from '../../src/frontend/assembly.js';
import { InstantiationPropagator } from '../../src/frontend/closed_terms.js';

import { fileURLToPath } from 'url';
import { PackageConfig } from "../../src/frontend/build_decls.js";
import { execSync } from "child_process";
const __dirname = path.dirname(fileURLToPath(import.meta.url));

const bosque_dir: string = path.join(__dirname, "../../../");
const z3bin = path.join(bosque_dir, "build/include/z3/bin/z3");
const smt_transform_bin_path = path.join(bosque_dir, "bin/smtemit/SMTEmitter.mjs");
const smt_runtime_code_path = path.join(bosque_dir, "bin/smtruntime/formula.smt2");

import { tmpdir } from 'node:os';
import { BSQIREmitter } from "../../src/frontend/bsqir_emit.js";
import { validateCStringLiteral } from "@bosque/jsbrex";

function wsnorm(s: string): string {
    return s.trim().replace(/\s+/g, " ");
}

function buildAssembly(srcfile: string): Assembly | undefined {
    const userpackage = new PackageConfig([], [{ srcpath: "test.bsq", filename: "test.bsq", contents: srcfile }]);
    const [asm, perrors, terrors] = generateASMSMT(userpackage);

    if(perrors.length === 0 && terrors.length === 0) {
        return asm;
    }
    else {
        return undefined;
    }
}

function buildMainCode(assembly: Assembly, outname: string): string | undefined {
    const iim = InstantiationPropagator.computeExecutableInstantiations(assembly, ["Main"]);
    const tinfo = BSQIREmitter.emitAssembly(assembly, iim);

    const nndir = path.normalize(outname);
    const fname = path.join(nndir, "bsqir.bsqon");

    try {
        fs.writeFileSync(fname, "'smtgen'" + " " + tinfo);
    }
    catch(e) {      
        return undefined;
    }

    let res = "";
    try {
        res = execSync(`node ${smt_transform_bin_path} --file ${fname}`).toString();
    }
    catch(e) {      
        return undefined;
    }

    return validateCStringLiteral(res.slice(1, -1));
}

function processSingleComponent(formula: string, smtcomponents: string, rterm: string): string {
    const sstr = `#BEGIN ${rterm}`;
    const estr = `#END ${rterm}`;

    const sidx = smtcomponents.indexOf(sstr) + sstr.length;
    const eidx = smtcomponents.indexOf(estr);
    const repl = smtcomponents.substring(sidx, eidx).trim();

    if(repl === "") {
        return formula.replace(rterm, `;;no content -- ${rterm}`);
    }
    else {
        return formula.replace(rterm, repl);
    }
}

function extractSingleComponent(smtcomponents: string, rterm: string): string {
    const sstr = `#BEGIN ${rterm}`;
    const estr = `#END ${rterm}`;

    const sidx = smtcomponents.indexOf(sstr) + sstr.length;
    const eidx = smtcomponents.indexOf(estr);
    const repl = smtcomponents.substring(sidx, eidx).trim();

    if(repl === "") {
        return `;;no content -- ${rterm}`;
    }
    else {
        return repl;
    }
}

const smtcomponenttags = [
    ";;--GLOBAL_DECLS--;;",
    ";;--GLOBAL_IMPLS--;;",
    ";;--PRE_FUNCS--;;",
    ";;--FUNCTION_DECLS--;;",
    ";;--ENUM_DECLS--;;",
    ";;--TYPEDECL_DECLS--;;",
    ";;--SPECIAL_DECLS--;;",
    ";;--COLLECTION_DECLS--;;",
    ";;--ENTITY_DECLS--;;",
    ";;--DATATYPE_DECLS--;;",
    ";;--SPECIAL_CONSTRUCTORS--;;",
    ";;--COLLECTION_CONSTRUCTORS--;;",
    ";;--ENTITY_CONSTRUCTORS--;;",
    ";;--DATATYPE_CONSTRUCTORS--;;",
    ";;--TYPEDECL_TERM_CONSTRUCTORS--;;",
    ";;--SPECIAL_TERM_CONSTRUCTORS--;;",
    ";;--ENTITY_TERM_CONSTRUCTORS--;;",
    ";;--DATATYPE_TERM_CONSTRUCTORS--;;",
    ";;--SUBTYPE_PREDICATES--;;",
    ";;--VFIELD_ACCESS--;;",
    ";;--VALIDATE_PREDICATES--;;"
];

function generateFormulaFile(smtcomponents: string, smtop: string, outname: string): boolean {
    const nndir = path.normalize(outname);

    let formula: string = "";
    try {
        formula = fs.readFileSync(smt_runtime_code_path).toString();
    }
    catch(e) {
        return false;
    }

    for(let i = 0; i < smtcomponenttags.length; ++i) {
        const rterm = smtcomponenttags[i];
        formula = processSingleComponent(formula, smtcomponents, rterm);
    }

    //set the constants for SMV -- right now just defaults
    const smv_constants = [
        "(declare-const SMV_I_RANGE Int) (assert (= SMV_I_RANGE 32))",
        "(declare-const SMV_STR_LENGTH Int) (assert (= SMV_STR_LENGTH 16))"
    ];
    formula = formula.replace(";;--SMV_CONSTANTS--;;", smv_constants.join("\n"));

    try {
        const fname = path.join(nndir, "formula.smt2");
        fs.writeFileSync(fname, formula + "\n;;;;;;;;;;;;;;;;\n\n" + smtop);
    }
    catch(e) {
        return false;
    }

    return true;
}

function generatePropertiesObject(smtcomponents: string, properties: {pkey: string, expected: string}[]): {pkey: string, expected: string}[] {
    return properties.map((p) => {
        const res = extractSingleComponent(smtcomponents, p.pkey);
        return { pkey: p.pkey, expected: res.replace(/\s+/g, ' ') };
    });
}

function execishMainCode(code: string, smtop: string) {
    const nndir = fs.mkdtempSync(path.join(tmpdir(), "bosque-smttest-"));

    let result = "";
    try {
        const asm = buildAssembly("declare namespace Main;\n\n" + code);
        if(asm === undefined) {
            result = `[FAILED TO BUILD ASSEMBLY] \n\n ${code}`;
        }
        else {
            const smtcomponents = buildMainCode(asm, nndir);
            if(smtcomponents === undefined) {
                result = `[FAILED TO BUILD MAIN CODE] \n\n ${code}`;
            }
            else {
                if(!generateFormulaFile(smtcomponents, smtop + "\n(check-sat)\n", nndir)) {
                    result = `[FAILED TO GENERATE FORMULA] \n\n ${code}`;
                }
                else {
                    try {
                        const formula = path.join(nndir, "formula.smt2");
                        result = execSync(`${z3bin} ${formula}`).toString();
                    }
                    catch(e) {
                        result = `[FAILED TO RUN MAIN CODE] -- ${e} \n\n ${code}`;
                    }
                }
            }
        }
    }
    catch(e) {
        result = `[Unexpected error ${e}]`;
    }
    finally {
        fs.rmSync(nndir, { recursive: true });
    }

    return wsnorm(result);
}

function checkAllProperties(code: string, properties: {pkey: string, expected: string}[]) {
    const nndir = fs.mkdtempSync(path.join(tmpdir(), "bosque-smttest-"));

    let result: any = undefined;
    try {
        const asm = buildAssembly("declare namespace Main;\n\n" + code);
        if(asm === undefined) {
            result = `[FAILED TO BUILD ASSEMBLY] \n\n ${code}`;
        }
        else {
            const smtcomponents = buildMainCode(asm, nndir);
            if(smtcomponents === undefined) {
                result = `[FAILED TO BUILD MAIN CODE] \n\n ${code}`;
            }
            else {
                result = generatePropertiesObject(smtcomponents, properties);
            }
        }
    }
    catch(e) {
        result = `[Unexpected error ${e}]`;
    }
    finally {
        fs.rmSync(nndir, { recursive: true });
    }

    return result;
}

function runishMainCodeUnsat(code: string, smtop: string) {
    const result = execishMainCode(code, smtop);

    assert.equal(wsnorm(result), "unsat");
}

function runishMainCodeSat(code: string, smtop: string) {
    const result = execishMainCode(code, smtop);

    assert.equal(wsnorm(result), "sat");
}

function checkProperties(code: string, eproperties: {pkey: string, expected: string}[]) {
    const result = checkAllProperties(code, eproperties);

    assert.equal(JSON.stringify(result), JSON.stringify(eproperties));
}

export {
    runishMainCodeUnsat, runishMainCodeSat, checkProperties
};
