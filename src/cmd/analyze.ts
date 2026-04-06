import * as fs from "fs";
import * as path from "path";

import { Assembly } from "../frontend/assembly.js";
import { checkAssembly, parseArgv } from "./workflows.js";
import { Monomorphizer } from "../backend/asmprocess/monomorphize.js";
import { ASMToIRConverter } from "../backend/asmprocess/flatten.js";
import { Status } from "./status_output.js"

const [fullargs, mainns, outdir] = parseArgv("smtout", ...process.argv);
Status.enable();

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
        const fname = path.join(nndir, "bsqir.bapi");
        fs.writeFileSync(fname, "'smtgen'" + " " + tinfo);
    }
    catch(e) {      
        Status.error("Failed to write bsqir info file!\n");
    }

    Status.output(`    IR generation successful -- emitted to ${nndir}\n\n`);
}

//////////////////////////////
Status.enable();

const asm = checkAssembly(fullargs, "smt");
if(asm === undefined) {
    process.exit(1);
}

Status.output(`-- SMT output directory: ${outdir}\n\n`);

fs.rmSync(outdir, { recursive: true, force: true });
fs.mkdirSync(outdir);

buildBAPIAssembly(asm, mainns, outdir);