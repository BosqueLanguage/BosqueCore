
class SourceInfo {
    readonly line: number;
    readonly column: number;
    readonly pos: number;
    readonly span: number;

    constructor(line: number, column: number, cpos: number, span: number) {
        this.line = line;
        this.column = column;
        this.pos = cpos;
        this.span = span;
    }

    static implicitSourceInfo(): SourceInfo {
        return new SourceInfo(-1, -1, -1, -1);
    }

    bsqemit(): any {
        return {line: this.line, column: this.column, pos: this.pos, span: this.span};
    }
    static bsqparse(jv: any): SourceInfo {
        return new SourceInfo(jv.line, jv.column, jv.pos, jv.span);
    }
}

type CodeFileInfo = { 
    srcpath: string, 
    filename: string, 
    contents: string
};

type LoggerLevel = number;
const LoggerLevel_fatal = 1;
const LoggerLevel_error = 2;
const LoggerLevel_warn = 3;
const LoggerLevel_info = 4;
const LoggerLevel_detail = 5;
const LoggerLevel_trace = 6;

function logLevelName(ll: LoggerLevel): string {
    return ["disabled", "fatal", "error", "warn", "info", "detail", "trace"][ll];
}


function logLevelNumber(ll: string): LoggerLevel {
    return ["disabled", "fatal", "error", "warn", "info", "detail", "trace"].indexOf(ll);
}

function unescapeString(ll: string): string {
    let ret = "";
    for (let i = 0; i < ll.length; i++) {
        if (ll[i] === "\\") {
            i++;
            if (ll[i] === "n") {
                ret += "\n";
            }
            else if (ll[i] === "r") {
                ret += "\r";
            }
            else if (ll[i] === "t") {
                ret += "\t";
            }
            else if (ll[i] === "0") {
                ret += "\0";
            }
            else if (ll[i] === "x") {
                const hex = ll.substring(i + 1, i + 3);
                ret += String.fromCharCode(parseInt(hex, 16));
                i += 2;
            }
            else {
                ret += ll[i];
            }
        }
        else {
            ret += ll[i];
        }
    }

    return ret;
}

function extractLiteralStringValue(str: string, unescape: boolean): string {
    return unescape ? unescapeString(str.substring(1, str.length - 1)) : str;
}

function extractLiteralASCIIStringValue(str: string, unescape: boolean): string {
    const ll = str.substring("ascii{".length + 1, str.length - (1 + "}".length));
    return unescape ? unescapeString(ll) : ("\"" + ll + "\"");
}

function cleanCommentsStringsFromFileContents(str: string): string {
    const commentRe = /(\/\/.*)|(\/\*(.|\s)*?\*\/)/ug;
    const stringRe = /"[^"\\\r\n]*(\\(.|\r?\n)[^"\\\r\n]*)*"/ug;
    const typedStringRe = /'[^'\\\r\n]*(\\(.|\r?\n)[^'\\\r\n]*)*'/ug;

    return str
        .replace(commentRe, "")
        .replace(stringRe, "\"\"")
        .replace(typedStringRe, "''");
}

type BuildLevel = "spec" | "debug" | "test" | "release";

function isBuildLevelEnabled(check: BuildLevel, enabled: BuildLevel): boolean {
    if(enabled === "spec") {
        return check === "spec" || check === "debug" || check === "test" || check === "release";
    }
    else if(enabled === "debug") {
        return check === "debug" || check === "test" || check === "release";
    }
    else if(enabled === "test") {
        return check === "test" || check === "release";
    }
    else {
        return check === "release";
    }
}

class PackageConfig {
    readonly macrodefs: string[]; 
    readonly src: CodeFileInfo[];

    constructor(macrodefs: string[], src: CodeFileInfo[]) {
        this.macrodefs = macrodefs;
        this.src = src;
    }

    jemit(): object {
        return { macrodefs: this.macrodefs, src: this.src };
    }

    static jparse(jobj: any): PackageConfig {
        return new PackageConfig(jobj.macrodefs, jobj.src);
    }
}

export {
    BuildLevel, isBuildLevelEnabled,
    SourceInfo, CodeFileInfo, PackageConfig,
    LoggerLevel, LoggerLevel_fatal, LoggerLevel_error, LoggerLevel_warn, LoggerLevel_info, LoggerLevel_detail, LoggerLevel_trace, logLevelName, logLevelNumber,
    extractLiteralStringValue, extractLiteralASCIIStringValue,
    cleanCommentsStringsFromFileContents
}