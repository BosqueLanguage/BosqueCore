
class SourceInfo
{
    readonly line: number;
    readonly column: number;

    constructor(line: number, column: number)
    {
        this.line = line;
        this.column = column;
    }
}

class IRRegex
{
    readonly regexID: number;

    //TODO: we need to store the (resolved) regex AST and compile later

    constructor(regexID: number)
    {
        this.regexID = regexID;
    }
}

export {
    SourceInfo,
    IRRegex
};
