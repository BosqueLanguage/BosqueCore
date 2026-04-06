import * as fs from "fs";
import * as path from "path";

import { Assembly } from "../frontend/assembly.js";
import { PackageConfig } from "../frontend/build_decls.js";
import { generateASM, workflowLoadUserSrc } from "./workflows.js";
import { Monomorphizer } from "../backend/asmprocess/monomorphize.js";
import { ASMToIRConverter } from "../backend/asmprocess/flatten.js";

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

let outdir = path.join(path.dirname(path.resolve(fullargs[0])), "smtout");
let outdiridx = fullargs.findIndex((v) => v === "--output");
if(outdiridx !== -1) {
    outdir = fullargs[outdiridx + 1];
    fullargs = fullargs.slice(0, outdiridx).concat(fullargs.slice(outdiridx + 2));
}

// TODO: We should place this in a generic file and import it
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

function buildBAPIAssembly(assembly: Assembly, rootasm: string, outname: string) { 
    Status.output("Monomorphizing code...\n");
    const iim = Monomorphizer.computeExecutableInstantiations(assembly, [rootasm]);

    Status.output("Generating IR code...\n");
    const irasm = ASMToIRConverter.generateIR(assembly, iim, undefined);
  
    Status.output("Emitting IR code...\n");
    const tinfo = irasm.emitBAPI();

    Status.output("    Writing BSQIR to disk...\n");
    const nndir = path.normalize(outname);
    try {
        const fname = path.join(nndir, "bsqir.bsqon");
        fs.writeFileSync(fname, "'smtgen'" + " " + tinfo);
    }
    catch(e) {      
        Status.error("Failed to write bsqir info file!\n");
    }

    Status.output(`    IR generation successful -- emitted to ${nndir}\n\n`);
}

const asm = checkAssembly(fullargs);
if(asm === undefined) {
    process.exit(1);
}

fs.rmSync(outdir, { recursive: true, force: true });
fs.mkdirSync(outdir);

buildBAPIAssembly(asm, mainns, outdir);