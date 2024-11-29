import * as fs from "fs";
import * as path from "path";

import { fileURLToPath } from 'url';
const __dirname = path.dirname(fileURLToPath(import.meta.url));

import { CodeFileInfo, PackageConfig } from "../frontend/build_decls.js";
import { Status } from "./status_output.js";
import { Assembly } from "../frontend/assembly.js";
import { Parser, ParserError } from "../frontend/parser.js";
import { TypeChecker, TypeError } from "../frontend/checker.js";

const bosque_dir: string = path.join(__dirname, "../../../");

function workflowLoadUserSrc(files: string[]): CodeFileInfo[] | undefined {
    try {
        let code: CodeFileInfo[] = [];

        for (let i = 0; i < files.length; ++i) {
            const realpath = path.resolve(files[i]);
            Status.output(`    ++ loading ${realpath}...\n`);

            code.push({ srcpath: realpath, filename: path.basename(files[i]), contents: fs.readFileSync(realpath).toString() });
        }

        return code;
    }
    catch (ex) {
        Status.error(`Failed to load user src file!\n`);
        return undefined;
    }
}

function workflowLoadCoreSrc(): CodeFileInfo[] | undefined {
    try {
        let code: CodeFileInfo[] = [];

        const coredir = path.join(bosque_dir, "bin/core");
        const corefiles = fs.readdirSync(coredir);
        for (let i = 0; i < corefiles.length; ++i) {
            const cfpath = path.join(coredir, corefiles[i]);
            code.push({ srcpath: cfpath, filename: corefiles[i], contents: fs.readFileSync(cfpath).toString() });
        }

        return code;
    }
    catch (ex) {
        Status.error(`Failed to load core src file!\n`);
        return undefined;
    }
}

function workflowLoadAllSrc(files: string[]): CodeFileInfo[] | undefined {
    const core = workflowLoadCoreSrc();
    const user = workflowLoadUserSrc(files);

    if(core === undefined || user === undefined) {
        return undefined;
    }
    else {
        return [...core, ...user];
    }
}

function generateASM(usercode: PackageConfig): [Assembly | undefined, ParserError[], TypeError[]]{
    const corecode = workflowLoadCoreSrc() as CodeFileInfo[];

    const pstart = Date.now();
    Status.output(`Parsing...\n`);
    const parseres = Parser.parse(corecode, usercode.src, ["EXEC_LIBS"]);
    const pend = Date.now();

    let tasm: Assembly | undefined = undefined;
    let parseerrors: ParserError[] = [];
    let typeerrors: TypeError[] = [];

    if(Array.isArray(parseres)) {
        parseerrors = parseres;
    }
    else {
        Status.output(`    Parsing successful [${(pend - pstart) / 1000}s]\n\n`);

        const tcstart = Date.now();
        Status.output(`Type checking...\n`);
        tasm = parseres;
        typeerrors = TypeChecker.checkAssembly(tasm);
        const tcend = Date.now();

        if(typeerrors.length === 0) {
            Status.output(`    Type checking successful [${(tcend - tcstart) / 1000}s]\n\n`);
        }
    }

    return [tasm, parseerrors, typeerrors];
}

export { 
    workflowLoadUserSrc, workflowLoadCoreSrc, workflowLoadAllSrc, generateASM
};