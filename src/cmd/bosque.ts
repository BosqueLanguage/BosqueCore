import * as fs from "fs";
import { JSEmitter } from "../backend/jsemitter.js";
import { Assembly } from "../frontend/assembly.js";
import { BuildLevel, PackageConfig } from "../frontend/build_decls.js";
import { InstantiationPropagator } from "../frontend/closed_terms.js";
import { Status } from "./status_output.js";
import { generateASM, workflowLoadUserSrc } from "./workflows.js";
import * as path from "path";

let fullargs = [...process.argv].slice(2);

function buildExeCode(assembly: Assembly, mode: "release" | "testing" | "debug", buildlevel: BuildLevel, rootasm: string, outname: string) {
    Status.output("generating JS code...\n");
    const iim = InstantiationPropagator.computeInstantiations(assembly, rootasm);
    const [jscode, _] = JSEmitter.emitAssembly(assembly, mode, buildlevel, iim);

    Status.output("writing JS code to disk...\n");
    const nndir = path.normalize(outname);
    try {
        for(let i = 0; i < jscode.length; ++i) {
            const fname = path.join(nndir, `${jscode[i].ns}.mjs`);
            fs.writeFileSync(fname, jscode[i].contents);
        }
    }
    catch(e) {      
        Status.error("Failed to write output files!\n");
    }

    Status.output(`Code generation successful -- JS emitted to ${nndir}\n`);
}

function checkAssembly(srcfiles: string[]): Assembly | undefined {
    Status.enable();

    process.stdout.write("loading user sources...\n");
    const usersrcinfo = workflowLoadUserSrc(srcfiles);
    if(usersrcinfo === undefined) {
        Status.error("Failed to load user sources!\n");
        return;
    }

    const userpackage = new PackageConfig([], usersrcinfo)
    const [asm, perrors, terrors] = generateASM(userpackage);

    if(perrors.length === 0 && terrors.length === 0) {
        Status.output("Assembly generation successful!\n");
    }
    else {
        Status.error("Failed to generate assembly!\n");

        //TODO -- need to do filename in error and sort nicely
        perrors.sort((a, b) => a.sinfo.line - b.sinfo.line);
        for(let i = 0; i < perrors.length; ++i) {
            Status.error(`Parser Error: ${perrors[i].message}\n`);
        }

        terrors.sort((a, b) => (a.file !== b.file) ? a.file.localeCompare(b.file) : a.line - b.line);
        for(let i = 0; i < terrors.length; ++i) {
            Status.error(`Type Error: ${terrors[i].msg}\n`);
        }
    }

    return asm;
}

const asm = checkAssembly(fullargs);
if(asm !== undefined) {
    const outdir = path.join(path.dirname(path.normalize(fullargs[0])), "jsout");
    Status.output(`JS output directory: ${outdir}\n`);

    fs.rmSync(outdir, { recursive: true, force: true });
    fs.mkdirSync(outdir);

    buildExeCode(asm, "debug", "debug", "Main", outdir);
}

