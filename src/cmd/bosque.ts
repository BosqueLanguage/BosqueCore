import * as fs from "fs";
import { JSEmitter } from "../backend/jsemitter/jsemitter.js";
import { Assembly } from "../frontend/assembly.js";
import { BuildLevel, PackageConfig } from "../frontend/build_decls.js";
import { InstantiationPropagator } from "../frontend/closed_terms.js";
import { Status } from "./status_output.js";
import { generateASM, workflowLoadUserSrc } from "./workflows.js";
import * as path from "path";

import { fileURLToPath } from 'url';
import { BSQONTypeInfoEmitter } from "../backend/bsqon/bsqonemitter.js";
const __dirname = path.dirname(fileURLToPath(import.meta.url));

const bosque_dir: string = path.join(__dirname, "../../../");
const runtime_code_path = path.join(bosque_dir, "bin/jsruntime/runtime.mjs");
const modules_path = path.join(bosque_dir, "node_modules");

let fullargs = [...process.argv].slice(2);
if(fullargs.length === 0) {
    Status.error("No input files specified!\n");
    process.exit(1);
}

let mainns = "Main";
let mainnsidx = fullargs.findIndex((v) => v === "--namespace");
if(mainnsidx !== -1) {
    mainns = fullargs[mainnsidx + 1];
    fullargs = fullargs.slice(0, mainnsidx).concat(fullargs.slice(mainnsidx + 2));
}

let testgen = false;
let testgenidx = fullargs.findIndex((v) => v === "--testgen");
if(testgenidx !== -1) {
    testgen = true;
    fullargs = fullargs.slice(0, testgenidx).concat(fullargs.slice(testgenidx + 1));
}

let outdir = path.join(path.dirname(path.resolve(fullargs[0])), "jsout");
let outdiridx = fullargs.findIndex((v) => v === "--output");
if(outdiridx !== -1) {
    outdir = fullargs[outdiridx + 1];
    fullargs = fullargs.slice(0, outdiridx).concat(fullargs.slice(outdiridx + 2));
}

function getSimpleFilename(fn: string): string {
    return path.basename(fn);
}

function buildExeCode(assembly: Assembly, mode: "release" | "debug", buildlevel: BuildLevel, rootasm: string, outname: string) {
    Status.output("Generating JS code...\n");
    const iim = InstantiationPropagator.computeInstantiations(assembly, rootasm);
    const jscode = JSEmitter.emitAssembly(assembly, mode, buildlevel, mainns, iim);

    Status.output("    Writing JS code to disk...\n");
    const nndir = path.normalize(outname);
    try {
        fs.cpSync(runtime_code_path, path.join(nndir, "runtime.mjs"));
        fs.cpSync(modules_path, path.join(nndir, "node_modules"), { recursive: true });

        for(let i = 0; i < jscode.length; ++i) {
            const fname = path.join(nndir, `${jscode[i].ns.ns[0]}.mjs`);
            fs.writeFileSync(fname, jscode[i].contents);
        }
    }
    catch(e) {      
        Status.error("Failed to write output files!\n");
    }

    Status.output(`    Code generation successful -- JS emitted to ${nndir}\n\n`);
}

function buildTypeInfo(assembly: Assembly, rootasm: string, outname: string) {
    Status.output("Generating Type Info assembly...\n");
    const iim = InstantiationPropagator.computeInstantiations(assembly, rootasm);
    const tinfo = BSQONTypeInfoEmitter.emitAssembly(assembly, iim, true);

    Status.output("    Writing Type Info to disk...\n");
    const nndir = path.normalize(outname);
    try {
        const fname = path.join(nndir, "typeinfo.json");
        fs.writeFileSync(fname, JSON.stringify(tinfo, undefined, 4));
    }
    catch(e) {      
        Status.error("Failed to write type info file!\n");
    }

    Status.output(`    Code generation successful -- Type Info emitted to ${nndir}\n\n`);
}


function buildExeCodeTest(assembly: Assembly, outname: string) {
    Status.output("Generating JS code...\n");
    const iim = InstantiationPropagator.computeInstantiations(assembly, undefined);
    const [jscode, testasm] = JSEmitter.emitTestAssembly(assembly, iim, undefined, undefined);

    Status.output("    Writing JS code to disk...\n");
    const nndir = path.normalize(outname);
    try {
        fs.cpSync(runtime_code_path, path.join(nndir, "runtime.mjs"));
        fs.cpSync(modules_path, path.join(nndir, "node_modules"), { recursive: true });

        for(let i = 0; i < jscode.length; ++i) {
            const fname = path.join(nndir, `${jscode[i].ns.ns[0]}.mjs`);
            fs.writeFileSync(fname, jscode[i].contents);
        }

        const testfname = path.join(nndir, "test.mjs");
        fs.writeFileSync(testfname, testasm);
    }
    catch(e) {      
        Status.error("Failed to write output files!\n");
    }

    Status.output(`    Code generation successful -- JS emitted to ${nndir}\n\n`);
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
    const [asm, perrors, terrors] = generateASM(userpackage);

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

const asm = checkAssembly(fullargs);
if(asm === undefined) {
    process.exit(1);
}

Status.output(`-- JS output directory: ${outdir}\n\n`);

fs.rmSync(outdir, { recursive: true, force: true });
fs.mkdirSync(outdir);

if(testgen) {
    buildExeCodeTest(asm, outdir);
}
else {
    buildTypeInfo(asm, mainns, outdir);
    buildExeCode(asm, "debug", "debug", mainns, outdir);
}

