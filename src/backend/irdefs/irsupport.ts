
function jsonEmitStrAsByteBuffer(str: string): number[] {
    return Array.from(Buffer.from(str, "utf8"));
}

function jsonParseByteBufferAsStr(str: number[]): string {
    return Buffer.from(str).toString("utf8");
}

class IRCodeFileInfo
{
    readonly srcpath: string;
    readonly filename: string;
    readonly contents: string;

    constructor(srcpath: string, filename: string, contents: string)
    {
        this.srcpath = srcpath;
        this.filename = filename;
        this.contents = contents;
    }

    jsonEmit(): object {
        return { srcpath: this.srcpath, filename: this.filename, contents: this.contents };
    }

    static jsonParse(obj: any): IRCodeFileInfo {
        return new IRCodeFileInfo(obj["srcpath"] as string, obj["filename"] as string, obj["contents"] as string);
    }
}

class IRSourceInfo
{
    readonly line: number;
    readonly column: number;

    constructor(line: number, column: number)
    {
        this.line = line;
        this.column = column;
    }

    jsonEmit(): object {
        return { line: this.line, column: this.column };
    }

    static jsonParse(obj: any): IRSourceInfo {
        return new IRSourceInfo(obj["line"] as number, obj["column"] as number);
    }
}

class IRCRegex
{
    readonly regexID: number;

    readonly bsqregex: string;
    readonly smtregex: string;
    readonly cppregex: string;

    constructor(regexID: number, bsqregex: string, smtregex: string, cppregex: string)
    {
        this.regexID = regexID;

        this.bsqregex = bsqregex;
        this.smtregex = smtregex;
        this.cppregex = cppregex;
    }

    jsonEmit(): object {
        return { regexid: this.regexID, bsqregex: jsonEmitStrAsByteBuffer(this.bsqregex), smtregex: jsonEmitStrAsByteBuffer(this.smtregex), cppregex: jsonEmitStrAsByteBuffer(this.cppregex) };
    }

    static jsonParse(obj: any): IRCRegex {
        return new IRCRegex(obj["regexid"] as number, jsonParseByteBufferAsStr(obj["bsqregex"] as number[]), jsonParseByteBufferAsStr(obj["smtregex"] as number[]), jsonParseByteBufferAsStr(obj["cppregex"] as number[]));
    }
}

class IRURegex
{
    readonly regexID: number;

    readonly bsqregex: string;
    readonly smtregex: string;
    readonly cppregex: string;

    constructor(regexID: number, bsqregex: string, smtregex: string, cppregex: string)
    {
        this.regexID = regexID;

        this.bsqregex = bsqregex;
        this.smtregex = smtregex;
        this.cppregex = cppregex;
    }

    jsonEmit(): object {
        return { regexID: this.regexID, bsqregex: jsonEmitStrAsByteBuffer(this.bsqregex), smtregex: jsonEmitStrAsByteBuffer(this.smtregex), cppregex: jsonEmitStrAsByteBuffer(this.cppregex) };
    }

    static jsonParse(obj: any): IRURegex {
        return new IRURegex(obj["regexID"] as number, jsonParseByteBufferAsStr(obj["bsqregex"] as number[]), jsonParseByteBufferAsStr(obj["smtregex"] as number[]), jsonParseByteBufferAsStr(obj["cppregex"] as number[]));
    }
}

export {
    jsonEmitStrAsByteBuffer, jsonParseByteBufferAsStr,

    IRCodeFileInfo,
    IRSourceInfo,
    IRCRegex,
    IRURegex
};
