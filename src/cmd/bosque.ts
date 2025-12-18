import * as fs from "fs";
import * as path from "path";

import { Assembly } from "../frontend/assembly.js";
import { PackageConfig } from "../frontend/build_decls.js";
import { generateASM, workflowLoadUserSrc, setStatusEnabled } from "./workflows.js";
import { Monomorphizer } from "../backend/asmprocess/monomorphize.js";
import { ASMToIRConverter } from "../backend/asmprocess/flatten.js";
import { CPPEmitter } from "../backend/ircemit/cppemit.js";

let statusenabled = true;
const Status = {
    output: (msg: string) => {
        if(statusenabled) {
            process.stdout.write(msg);
        }
    },
    error: (msg: string) => {
        if(statusenabled) {
            process.stderr.write(msg);
        }
    }
};

function enableStatus() {
    statusenabled = true;
    setStatusEnabled(true);
}

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

let outdir = path.join(path.dirname(path.resolve(fullargs[0])), "jsout");
let outdiridx = fullargs.findIndex((v) => v === "--output");
if(outdiridx !== -1) {
    outdir = fullargs[outdiridx + 1];
    fullargs = fullargs.slice(0, outdiridx).concat(fullargs.slice(outdiridx + 2));
}

function buildExeCode(assembly: Assembly, rootasm: string, outname: string) {
    Status.output("Monomorphizing code...\n");
    const iim = Monomorphizer.computeExecutableInstantiations(assembly, [rootasm]);

    Status.output("Generating IR code...\n");
    const ircode = ASMToIRConverter.generateIR(assembly, iim, undefined);

    Status.output("Emitting CPP code...\n");
    const cppcode = CPPEmitter.createEmitter(ircode);
    const maincode = cppcode.emitInvokeForKey(`${mainns}::main`);

    Status.output("    Writing CPP code to disk...\n");
    const nndir = path.normalize(outname);
    try {
        const fname = path.join(nndir, `main.cpp`);
        fs.writeFileSync(fname, maincode);
    }
    catch(e) {      
        Status.error("Failed to write output files!\n");
    }

    Status.output(`    Code generation successful -- CPP emitted to ${nndir}\n\n`);
}

function getSimpleFilename(fn: string): string {
    return path.basename(fn);
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

//////////////////////////////
enableStatus();

const asm = checkAssembly(fullargs);
if(asm === undefined) {
    process.exit(1);
}

Status.output(`-- JS output directory: ${outdir}\n\n`);

fs.rmSync(outdir, { recursive: true, force: true });
fs.mkdirSync(outdir);

buildExeCode(asm, mainns, outdir);

