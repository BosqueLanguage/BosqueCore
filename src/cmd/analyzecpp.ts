import * as fs from "fs";
import { BSQIREmitter } from "../frontend/bsqir_emit.js";
import { Assembly } from "../frontend/assembly.js";
import { InstantiationPropagator } from "../frontend/closed_terms.js";
import { Status } from "./status_output.js";
import { generateASMCPP, workflowLoadUserSrc } from "./workflows.js";
import * as path from "path";

import { fileURLToPath } from 'url';
import { PackageConfig } from "../frontend/build_decls.js";
import { execSync } from "child_process";
import { validateStringLiteral } from "@bosque/jsbrex";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const bosque_dir: string = path.join(__dirname, "../../../");
const cpp_runtime_dir_path = path.join(bosque_dir, "bin/cppruntime/");
const cpp_transform_bin_path = path.join(bosque_dir, "bin/cppemit/CPPEmitter.mjs");
const cpp_runtime_src_path = path.join(bosque_dir, "bin/cppruntime/emit.cpp");

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

let outdir = path.join(path.dirname(path.resolve(fullargs[0])), "cppout");
let outdiridx = fullargs.findIndex((v) => v === "--output");
if(outdiridx !== -1) {
    outdir = fullargs[outdiridx + 1];
    fullargs = fullargs.slice(0, outdiridx).concat(fullargs.slice(outdiridx + 2));
}

function getSimpleFilename(fn: string): string {
    return path.basename(fn);
}

function generateCPPFiles(header: string, src: string, outdir: string) {
    Status.output("Processing existing contents of emit.cpp...\n");
    const dir = path.normalize(outdir);

    Status.output("    Reading Contents of Base emit.cpp File...\n");
    let srcbase: string = "";
    try {
        srcbase = fs.readFileSync(cpp_runtime_src_path).toString() + `\n\n`;
    }
    catch(e) {
        Status.error("Failed to Read Base emit.cpp File!\n");
    }
    const runtime_header: string = `#include "${cpp_runtime_dir_path}cppruntime.hpp"\n\n`;
    const src_header: string = `#include "emit.hpp"\n\n`;
    const nheader_contents: string = runtime_header.concat( header ); 
    const nsrc_contents: string = src_header.concat(src, srcbase);

    Status.output("    Writing to emit.hpp...\n");
    try {
        const headername = path.join(dir, "emit.hpp");
        fs.writeFileSync(headername, nheader_contents);
    }
    catch(e) {
        Status.error("Failed to write to emit.hpp!\n");
    }

    Status.output("    Writing to emit.cpp...\n");
    try {
        const srcname = path.join(dir, "emit.cpp");
        fs.writeFileSync(srcname, nsrc_contents);
    }
    catch(e) {
        Status.error("Failed to write to emit.cpp!\n");
    }

    Status.output(`    CPP emission successful -- emitted to ${dir}\n\n`);
}

function runCPPEmit(outname: string): [string, string] {
    Status.output("Processing IR into CPP Code...\n");
   
    const nndir = path.normalize(outname);
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
        Status.error("Failed to write bsqir info file!\n");
    }

    return [validateStringLiteral(res[0].slice(1)), validateStringLiteral(res[1].slice(0, -2))];
}

function buildBSQONAssembly(assembly: Assembly, rootasm: string, outname: string) {
    Status.output("Generating Type Info assembly...\n");
    const iim = InstantiationPropagator.computeInstantiations(assembly, rootasm);
    const tinfo = BSQIREmitter.emitAssembly(assembly, iim);

    Status.output("    Writing BSQIR to disk...\n");
    const nndir = path.normalize(outname);
    try {
        const fname = path.join(nndir, "bsqir.bsqon");
        fs.writeFileSync(fname, tinfo);
    }
    catch(e) {      
        Status.error("Failed to write bsqir info file!\n");
    }

    Status.output(`    IR generation successful -- emitted to ${nndir}\n\n`);
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
    const [asm, perrors, terrors] = generateASMCPP(userpackage);

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

Status.output(`-- CPP output directory: ${outdir}\n\n`);

fs.rmSync(outdir, { recursive: true, force: true });
fs.mkdirSync(outdir);

buildBSQONAssembly(asm, mainns, outdir);

const cpp = runCPPEmit(outdir);
generateCPPFiles(cpp[0], cpp[1], outdir);