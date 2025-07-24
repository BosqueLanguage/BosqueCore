import * as fs from "fs";
import { BSQIREmitter } from "../frontend/bsqir_emit.js";
import { Assembly } from "../frontend/assembly.js";
import { InstantiationPropagator } from "../frontend/closed_terms.js";
import { Status } from "./status_output.js";
import { generateASMSMT, workflowLoadUserSrc } from "./workflows.js";
import * as path from "path";

import { fileURLToPath } from 'url';
import { PackageConfig } from "../frontend/build_decls.js";
import { execSync } from "child_process";
import { validateCStringLiteral } from "@bosque/jsbrex";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const bosque_dir: string = path.join(__dirname, "../../../");
const smt_transform_bin_path = path.join(bosque_dir, "bin/smtemit/SMTEmitter.mjs");
const smt_runtime_code_path = path.join(bosque_dir, "bin/smtruntime/formula.smt2");

const z3bin = path.join(bosque_dir, "build/include/z3/bin/z3");

let fullargs = [...process.argv].slice(2);
if(fullargs.length === 0) {
    Status.error("No input files specified!\n");
    process.exit(1);
}

let ischktest = false;
let ischktestidx = fullargs.findIndex((v) => v === "--chktest");
if(ischktestidx !== -1) {
    ischktest = true;
    fullargs = fullargs.slice(0, ischktestidx).concat(fullargs.slice(ischktestidx + 1));
}

let mainns = "Main";
let mainnsidx = fullargs.findIndex((v) => v === "--namespace");
if(mainnsidx !== -1) {
    mainns = fullargs[mainnsidx + 1];
    fullargs = fullargs.slice(0, mainnsidx).concat(fullargs.slice(mainnsidx + 2));
}

let outdir = path.join(path.dirname(path.resolve(fullargs[0])), "smtout");
let outdiridx = fullargs.findIndex((v) => v === "--output");
if(outdiridx !== -1) {
    outdir = fullargs[outdiridx + 1];
    fullargs = fullargs.slice(0, outdiridx).concat(fullargs.slice(outdiridx + 2));
}

function getSimpleFilename(fn: string): string {
    return path.basename(fn);
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

function processSingleComponentAppend(formula: string, smtcomponents: string, rterm: string): string {
    const sstr = `#BEGIN ${rterm}`;
    const estr = `#END ${rterm}`;

    const sidx = smtcomponents.indexOf(sstr) + sstr.length;
    const eidx = smtcomponents.indexOf(estr);
    const repl = smtcomponents.substring(sidx, eidx).trim();

    if(repl === "") {
        return formula;
    }
    else {
        return formula + "\n\n" + repl;
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

function generateFormulaFile(smtcomponents: string, outname: string, chksat?: boolean, getres?: boolean) {
    Status.output("Processing SMT Formula...\n");
    const nndir = path.normalize(outname);

    Status.output("    Reading SMT Formula Template File...\n");
    let formula: string = "";
    try {
        formula = fs.readFileSync(smt_runtime_code_path).toString();
    }
    catch(e) {
        Status.error("Failed to read SMT runtime file!\n");
    }

    Status.output("    Processing Formula Template File...\n");
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


    formula = processSingleComponentAppend(formula, smtcomponents, ";;--SMT_OPERATION--;;");
    if(chksat) {
        formula = formula + "\n\n" + "(check-sat)\n";

        if(getres) {
            formula = formula + "\n" + "(get-model)\n";
        }
    }

    Status.output("    Writing SMT Formula File...\n");
    try {
        const fname = path.join(nndir, "formula.smt2");
        fs.writeFileSync(fname, formula);
    }
    catch(e) {
        Status.error("Failed to write SMT formula file!\n");
    }

    Status.output(`SMT Formula generation successful -- emitted to ${nndir}\n\n`);
}

function runSMTEmit(outname: string): string {
    Status.output("Processing IR into SMT Components...\n");
   
    const nndir = path.normalize(outname);
    let res = "";
    try {
        const fname = path.join(nndir, "bsqir.bsqon");
        res = execSync(`node ${smt_transform_bin_path} --file ${fname}`, { maxBuffer: 16777216 }).toString();
    }
    catch(e) {      
        Status.error("Failed to write bsqir info file!\n");
    }

    return validateCStringLiteral(res.slice(1, -1));
}

function processTestFile(assembly: Assembly, rootasm: string, testfile: string, outname: string) {
    Status.output("Generating Type Info assembly...\n");
    const iim = InstantiationPropagator.computeTestInstantiations(assembly, [rootasm]);
    const bsqir = BSQIREmitter.emitAssembly(assembly, iim, [testfile])

    Status.output("    Writing BSQIR to disk...\n");
    const nndir = path.normalize(outname);
    try {
        const fname = path.join(nndir, "bsqir.bsqon");
        fs.writeFileSync(fname, (ischktest ? "'--chktest'" : "'--errtest'") + " " + bsqir);
    }
    catch(e) {      
        Status.error("Failed to write bsqir info file!\n");
    }
}

function checkAssembly(srcfiles: string[]): Assembly | undefined {
    Status.enable();

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
    const [asm, perrors, terrors] = generateASMSMT(userpackage);

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

function checkSMTFormula(smtcomponents: string, outname: string) {
    generateFormulaFile(smtcomponents, outname, true, false);

    Status.output("Running SMT Solver...\n");
    const nndir = path.normalize(outname);

    let rr = "";
    try {
        rr = execSync(`${z3bin} ${path.join(nndir, "formula.smt2")}`).toString();
    }
    catch(e) {
        Status.error("Failed to run SMT solver!\n");
        return;
    }

    Status.output("Result is -- " + rr.replace("\n", " ") + "\n");
}

const asm = checkAssembly(fullargs);
if(asm === undefined) {
    process.exit(1);
}

Status.output(`-- SMT output directory: ${outdir}\n\n`);

fs.rmSync(outdir, { recursive: true, force: true });
fs.mkdirSync(outdir);

const testfile = fullargs.find((v) => v.endsWith(".bsqtest"));
if(testfile === undefined) {
    Status.error("No test file specified!\n");
    process.exit(1);
}

processTestFile(asm, mainns, testfile, outdir);
const smtcomponents = runSMTEmit(outdir);

if(ischktest) {
    checkSMTFormula(smtcomponents, outdir);
}
else {
    const opts = smtcomponents.split("#### CHECK ####").map((opt) => opt.trim()).filter((opt) => opt !== "");
    for(let i = 0; i < opts.length; ++i) {
        const opt = opts[i]
        let opterr = opt.split("\n")[0].trim();

        Status.output(`Processing Possible Error ${i + 1} of ${opts.length}...\n`);
        Status.output(opterr + "\n");

        checkSMTFormula(opt, outdir);
    }
}
