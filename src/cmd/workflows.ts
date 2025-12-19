import * as fs from "fs";
import * as path from "path";

import { fileURLToPath } from 'url';
const __dirname = path.dirname(fileURLToPath(import.meta.url));

import { CodeFileInfo, PackageConfig } from "../frontend/build_decls.js";
import { Assembly } from "../frontend/assembly.js";
import { Parser, ParserError } from "../frontend/parser.js";
import { TypeChecker, TypeError } from "../frontend/checker.js";

const bosque_dir: string = path.join(__dirname, "../../../");

let statusenabled = false;
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

function workflowLoadUserSrc(files: string[]): CodeFileInfo[] | undefined {
    try {
        let code: CodeFileInfo[] = [];

        for (let i = 0; i < files.length; ++i) {
            const realpath = path.resolve(files[i]);
            Status.output(`    ++ loading ${realpath}...\n`);

            code.push({ srcpath: realpath, filename: path.basename(realpath), contents: fs.readFileSync(realpath).toString() });
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

function generateASMGeneral(usercode: PackageConfig, macrodefs: string[]): [Assembly | undefined, ParserError[], TypeError[]]{
    const corecode = workflowLoadCoreSrc() as CodeFileInfo[];

    const pstart = Date.now();
    Status.output(`Parsing...\n`);
    const parseres = Parser.parse(corecode, usercode.src, macrodefs);
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

function generateASM(usercode: PackageConfig): [Assembly | undefined, ParserError[], TypeError[]]{
    return generateASMGeneral(usercode, ["EXEC_LIBS", "STRIPPED_CORE"]);
}

function setStatusEnabled(enabled: boolean): void {
    statusenabled = enabled;
}

export { 
    workflowLoadUserSrc, workflowLoadCoreSrc, workflowLoadAllSrc, generateASM, setStatusEnabled
};
