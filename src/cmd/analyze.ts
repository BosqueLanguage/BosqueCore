import * as fs from "fs";
import * as path from "path";

import { Assembly } from "../frontend/assembly.js";
import { checkAssembly, parseArgv, Status } from "./workflows.js";
import { Monomorphizer } from "../backend/asmprocess/monomorphize.js";
import { ASMToIRConverter } from "../backend/asmprocess/flatten.js";

const [fullargs, mainns, outdir] = parseArgv("smtout", ...process.argv);
let status = new Status();

function buildBAPIAssembly(assembly: Assembly, rootasm: string, outname: string) { 
    status.output("Monomorphizing code...\n");
    const iim = Monomorphizer.computeExecutableInstantiations(assembly, [rootasm]);

    status.output("Generating IR code...\n");
    const irasm = ASMToIRConverter.generateIR(assembly, iim, undefined);
  
    status.output("Emitting IR code...\n");
    const tinfo = irasm.emitBAPI();

    status.output("    Writing BSQIR to disk...\n");
    const nndir = path.normalize(outname);
    try {
        const fname = path.join(nndir, "bsqir.bapi");
        fs.writeFileSync(fname, "'smtgen'" + " " + tinfo);
    }
    catch(e) {      
        status.error("Failed to write bsqir info file!\n");
    }

    status.output(`    IR generation successful -- emitted to ${nndir}\n\n`);
}

const asm = checkAssembly(fullargs, true);
if(asm === undefined) {
    process.exit(1);
}

status.output(`-- SMT output directory: ${outdir}\n\n`);

fs.rmSync(outdir, { recursive: true, force: true });
fs.mkdirSync(outdir);

buildBAPIAssembly(asm, mainns, outdir);