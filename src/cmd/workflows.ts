import * as fs from "fs";
import * as path from "path";

import { CodeFileInfo, PackageConfig } from "../frontend/build_decls";
import { Status } from "./status_output";
import { Assembly } from "../frontend/assembly";
import { Parser, ParserError } from "../frontend/parser";
import { TypeChecker, TypeError } from "../frontend/checker";


const bosque_dir: string = path.join(__dirname, "../../../");

function workflowLoadUserSrc(files: string[]): CodeFileInfo[] | undefined {
    try {
        let code: CodeFileInfo[] = [];

        for (let i = 0; i < files.length; ++i) {
            const realpath = path.resolve(files[i]);
            Status.output(`loading ${realpath}...\n`);

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

    Status.output(`parsing...\n`);
    const parseres = Parser.parse(corecode, usercode.src, usercode.macrodefs);

    let tasm: Assembly | undefined = undefined;
    let parseerrors: ParserError[] = [];
    let typeerrors: TypeError[] = [];

    if(Array.isArray(parseres)) {
        parseerrors = parseres;
    }
    else {
        Status.output(`type checking...\n`);
        tasm = parseres;
        typeerrors = TypeChecker.checkAssembly(tasm);
    }

    return [tasm, parseerrors, typeerrors];
}

export { 
    workflowLoadUserSrc, workflowLoadCoreSrc, workflowLoadAllSrc, generateASM
};