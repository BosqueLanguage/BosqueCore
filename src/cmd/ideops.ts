
import * as path from "path";
import * as fs from "fs";

import { CodeFileInfo, PackageConfig } from "../frontend/build_decls.js";
import { Parser, ParserError } from "../frontend/parser.js";
import { TypeChecker, TypeError } from "../frontend/checker.js";
import { workflowLoadCoreSrc } from "./workflows.js";

const g_corecode: CodeFileInfo[] = workflowLoadCoreSrc() as CodeFileInfo[];

class IDEOpErrorInfo {
    readonly filename: string;
    readonly line: number;
    readonly msg: string;

    constructor(filename: string, line: number, msg: string) {
        this.filename = filename;
        this.line = line;
        this.msg = msg;
    }

    static fromParserError(err: ParserError): IDEOpErrorInfo {
        return new IDEOpErrorInfo(err.srcfile, err.sinfo.line, err.message);
    }

    static fromTypeError(err: TypeError): IDEOpErrorInfo {
        return new IDEOpErrorInfo(err.file, err.line, err.msg);
    }
}

function runIDETypeCheck(usercode: CodeFileInfo[]): [IDEOpErrorInfo[], string | undefined] {
    try {
        const userpackage = new PackageConfig([], usercode);
    
        const parseres = Parser.parse(g_corecode, userpackage.src, ["EXEC_LIBS"]);
        if(Array.isArray(parseres)) {
            return [parseres.map(e => IDEOpErrorInfo.fromParserError(e)), undefined];
        }
        else {
            const typeerrors = TypeChecker.checkAssembly(parseres);

            if(typeerrors.length !== 0) {
                return [typeerrors.map(e => IDEOpErrorInfo.fromTypeError(e)), undefined];
            }
        }

        return [[], undefined];
    } catch(e) {
        return [[], `IDE type check failed: ${e}`];
    }
}

let fullargs = process.argv.slice(2);
function workflowLoadUserSrc(files: string[]): CodeFileInfo[] | undefined {
    try {
        let code: CodeFileInfo[] = [];

        for (let i = 0; i < files.length; ++i) {
            if(!files[i].includes("BosqueCore/src/core") && !files[i].includes("BosqueCore/src/samples")) {
                code.push({ srcpath: files[i], filename: path.basename(files[i]), contents: fs.readFileSync(files[i]).toString() });
            }
        }

        return code;
    }
    catch (ex) {
        return undefined;
    }
}

const usrcode = workflowLoadUserSrc(fullargs);
if(usrcode === undefined) {
    console.error("Failed to load user src file(s)!\n");
    process.exit(1);
}

const chkinfo = runIDETypeCheck(usrcode);
if(chkinfo[1] !== undefined) {
    console.error(chkinfo[1]);
    process.exit(1);
}

console.log(JSON.stringify(chkinfo[0]));
process.exit(0);
