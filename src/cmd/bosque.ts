import { PackageConfig } from "../frontend/build_decls.js";
import { Status } from "./status_output.js";
import { generateASM, workflowLoadUserSrc } from "./workflows.js";

let fullargs = [...process.argv].slice(2);

function checkAssembly(srcfiles: string[]) {
    Status.enable();

    process.stdout.write("loading user sources...\n");
    const usersrcinfo = workflowLoadUserSrc(srcfiles);
    if(usersrcinfo === undefined) {
        Status.error("Failed to load user sources!\n");
        return;
    }

    const userpackage = new PackageConfig([], usersrcinfo)
    const [asm, perrors, terrors] = generateASM(userpackage);

    if(asm !== undefined) {
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
}

checkAssembly(fullargs);

