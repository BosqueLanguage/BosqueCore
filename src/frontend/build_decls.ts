

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
}

type CodeFileInfo = { 
    srcpath: string, 
    filename: string, 
    contents: string
};

type LoggerLevel = "fatal" | "error" | "warn" | "info" | "detail" | "debug" | "trace";

function extractLiteralStringValue(str: string): string {
    //
    //TODO: right now we assume there are not escaped values in the string
    //
    return str.substring(1, str.length - 1);
}

function extractLiteralASCIIStringValue(str: string): string {
    //
    //TODO: right now we assume there are not escaped values in the string
    //
    return str.substring("ascii{".length + 1, str.length - (1 + "}".length));
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
    LoggerLevel,
    extractLiteralStringValue, extractLiteralASCIIStringValue,
    cleanCommentsStringsFromFileContents
}