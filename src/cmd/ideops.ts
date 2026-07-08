
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

function runIDETypeCheck(srcfiles: { filename: string, contents: string} []): [IDEOpErrorInfo[], string | undefined] {
    try {
        const userpackage = new PackageConfig([], srcfiles.map(f => ({ srcpath: f.filename, filename: f.filename, contents: f.contents })));
    
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

export { IDEOpErrorInfo, runIDETypeCheck };
