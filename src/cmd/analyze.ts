import * as fs from "fs";
import * as path from "path";
import { execSync } from "child_process";

import { emitAssembly } from "../backend/irdefs/iremit.js";
import { IRAssembly } from "../backend/irdefs/irassembly.js";


function buildBSQONAssembly(assembly: IRAssembly, rootasm: string, outname: string) {
    Status.output("Generating Type Info assembly...\n");
    //const iim = InstantiationPropagator.computeExecutableInstantiations(assembly, [rootasm]);
    const tinfo = BSQIREmitter.emitAssembly(assembly, iim);

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