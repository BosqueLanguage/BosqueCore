

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

export {
    SourceInfo, CodeFileInfo,
    LoggerLevel,
    extractLiteralStringValue, extractLiteralASCIIStringValue,
    cleanCommentsStringsFromFileContents
}