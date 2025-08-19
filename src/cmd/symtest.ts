import * as fs from "fs";
import { BSQIREmitter } from "../frontend/bsqir_emit.js";
import { Assembly } from "../frontend/assembly.js";
import { InstantiationPropagator } from "../frontend/closed_terms.js";
import { Status } from "./status_output.js";
import { generateASMSMT, workflowLoadUserSrc } from "./workflows.js";
import * as path from "path";

import { fileURLToPath } from 'url';
import { PackageConfig } from "../frontend/build_decls.js";
import { exec, execSync } from "child_process";
import { validateCStringLiteral } from "@bosque/jsbrex";
import chalk from "chalk";

import { tmpdir } from 'node:os';
import { rmSync } from "node:fs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const bosque_dir: string = path.join(__dirname, "../../../");
const smt_transform_bin_path = path.join(bosque_dir, "bin/smtemit/SMTEmitter.mjs");
const smt_runtime_code_path = path.join(bosque_dir, "bin/smtruntime/formula.smt2");

const z3bin = path.join(bosque_dir, "build/include/z3/bin/z3");

////////////////////////////////////////////////////
Status.enable();
////////////////////////////////////////////////////


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

class PendingCompnentInfo {
    readonly idx: number;
    readonly errinfo: string;

    readonly smtcomponents: string;
    readonly smt2file: string;

    readonly starttime: number;

    constructor(idx: number, errinfo: string, smtcomponents: string, smt2file: string) {
        this.idx = idx;
        this.errinfo = errinfo;

        this.smtcomponents = smtcomponents;
        this.smt2file = smt2file;

        this.starttime = Date.now();
    }
}

let smt_components: {errinfo: string, smtinfo: string}[] = [];
let current_component = 0;
let completed_count = 0;

let async_errct = 0;
let pending_count = 0;
const max_components = 16;

function checkSMTFormulaAsync() {
    if(completed_count === smt_components.length) {
        completeRun();
    }
    else {
        if(pending_count < max_components && current_component < smt_components.length) {
            startSMTComponent();
        }
    }
}

function startSMTComponent() {
    const cc = smt_components[current_component++];
    pending_count++;

    //process.stdout.write(`\nChecking Possible Error ${current_component} of ${smt_components.length}...\n`);

    const nndir = fs.mkdtempSync(path.join(tmpdir(), "bosque-symtest-"));
    generateFormulaFile(cc.smtinfo, nndir, true, false);

    let cinfo = new PendingCompnentInfo(current_component, cc.errinfo, cc.smtinfo, nndir);
    exec(`${z3bin} -T:60 ${path.join(nndir, "formula.smt2")}`, (err, stdout, stderr) => {
        const rr = stdout.toString().trim();
        completeSMTComponent(cinfo, err, rr);
    });
}

function completeSMTComponent(cinfo: PendingCompnentInfo, err: any, result: string) {
    const end = Date.now();

    process.stdout.write(`Completed test #${cinfo.idx} for ${cinfo.errinfo} -- `);
    rmSync(cinfo.smt2file, { recursive: true });

    if(err) { 
        Status.error("Failed to run SMT solver!\n");
    }
    else {
        if(result === "unsat") {
            process.stdout.write(chalk.green("Pass") + "!\n");
            if(PRINT_TIMING) {
                process.stdout.write(`    Solve Time ${end - cinfo.starttime}ms\n`);
            }
        }
        else if(result === "sat") {
            process.stdout.write(chalk.red("Violation Found") + "!\n");
            if(PRINT_TIMING) {
                process.stdout.write(`    Solve Time ${end - cinfo.starttime}ms\n`);
            }
            async_errct++;
        }
        else {
            process.stdout.write(chalk.yellow("Exhausted Checking") + "...\n");
            if(PRINT_TIMING) {
                process.stdout.write(`    Solve Time ${end - cinfo.starttime}ms\n`);
            }
        }
    }

    pending_count--;
    completed_count++;
    checkSMTFormulaAsync();
}

function completeRun() {
    if(async_errct === 0) {
        process.stdout.write("\n----\nNo Violations Found.\n\n");
    }
    else {
        process.stdout.write(`\n----\n${async_errct} Issues Found!\n\n`);
    }
}

function checkSMTFormula(smtcomponents: string, outname: string): boolean {
    generateFormulaFile(smtcomponents, outname, true, false);

    process.stdout.write("    Running SMT Solver...\n");
    const nndir = path.normalize(outname);

    let rr = "";
    let start = Date.now();
    try {
        rr = execSync(`${z3bin} -T:60 ${path.join(nndir, "formula.smt2")}`).toString().trim();
    }
    catch(e) {
        Status.error("Failed to run SMT solver!\n");
        return false;
    }
    let end = Date.now();

    if(rr === "unsat") {
        process.stdout.write("    Pass!\n");
        if(PRINT_TIMING) {
            process.stdout.write(`    Solve Time ${end - start}ms\n`);
        }
        return false;
    }
    else if(rr === "sat") {
        process.stdout.write("    Violation Found!\n");
        if(PRINT_TIMING) {
            process.stdout.write(`    Solve Time ${end - start}ms\n`);
        }
        return true;
    }
    else {
        process.stdout.write("    Exhausted Checking...\n");
        if(PRINT_TIMING) {
            process.stdout.write(`    Solve Time ${end - start}ms\n`);
        }
        return false;
    }
}

const asm = checkAssembly(fullargs);
if(asm === undefined) {
    process.exit(1);
}

Status.output(`-- SMT output directory: ${outdir}\n\n`);

///////////////////////////////////////////////////////
Status.statusDisable();
///////////////////////////////////////////////////////

const ENABLE_ASYNC = true;
const PRINT_TIMING = true;

fs.rmSync(outdir, { recursive: true, force: true });
fs.mkdirSync(outdir);

const testfile = fullargs.find((v) => v.endsWith(".bsqtest"));
if(testfile === undefined) {
    Status.error("No test file specified!\n");
    process.exit(1);
}

processTestFile(asm, mainns, path.normalize(testfile), outdir);
const smtcomponents = runSMTEmit(outdir);

if(ischktest) {
    process.stdout.write(`Checking for Property Violation...\n`);
    checkSMTFormula(smtcomponents, outdir);
}
else {
    const opts = smtcomponents.split("#### CHECK ####").map((opt) => opt.trim()).filter((opt) => opt !== "");

    if(ENABLE_ASYNC) {
        process.stdout.write(`Checking ${opts.length} possible errors...\n`);
        for(let i = 0; i < opts.length; ++i) {
            const opt = opts[i]
            let opterr = opt.split("\n")[0].trim().slice(2);

            smt_components.push({ errinfo: opterr, smtinfo: opt });
        }

        for(let j = 0; j < max_components; ++j) {
            checkSMTFormulaAsync();
        }
    }
    else {
        let errct = 0;
        for(let i = 0; i < opts.length; ++i) {
            const opt = opts[i]
            let opterr = opt.split("\n")[0].trim().slice(2);

            process.stdout.write(`\nChecking Possible Error ${i + 1} of ${opts.length}...\n`);
            process.stdout.write("    " + opterr + "\n");

            let err = checkSMTFormula(opt, outdir);
            if(err) {
                errct++;
            }
        }

        if(errct === 0) {
            process.stdout.write("\n----\nNo Violations Found.\n\n");
        }
        else {
            process.stdout.write(`\n----\n${errct} Issues Found!\n\n`);
        }
    }
}
