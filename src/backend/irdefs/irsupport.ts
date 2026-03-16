
class IRSourceInfo
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
}

export {
    IRSourceInfo,
    IRRegex
};
