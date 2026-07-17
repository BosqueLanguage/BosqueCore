
import type { BAPILexer } from "./irlexer.js";

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
}


function emitTypeKey(tkeystr: string): string {
    return `'${tkeystr}'<Assembly::TypeKey>`;
}

function parseTypeKey(lexer: BAPILexer): string {
    const sstr = lexer.parseCString();
    lexer.ensureAndConsumeSymbol('<');
        
    const typetag = lexer.parseTypeIdentifier();
    if(typetag !== "Assembly::TypeKey") {
        throw new Error(`Expected TypeKey 'Assembly::TypeKey' but got ${typetag}`);
    }
        
    lexer.ensureAndConsumeSymbol('>');

    return sstr;
}

function emitInvokeKey(tkeystr: string): string {
    return `'${tkeystr}'<Assembly::InvokeKey>`;
}

function parseInvokeKey(lexer: BAPILexer): string {
    const sstr = lexer.parseCString();
    lexer.ensureAndConsumeSymbol('<');
        
    const typetag = lexer.parseTypeIdentifier();
    if(typetag !== "Assembly::InvokeKey") {
        throw new Error(`Expected InvokeKey 'Assembly::InvokeKey' but got ${typetag}`);
    }
        
    lexer.ensureAndConsumeSymbol('>');

    return sstr;
}

function emitIdentifier(tkeystr: string): string {
    return `'${tkeystr}'<Assembly::Identifier>`;
}

function parseIdentifier(lexer: BAPILexer): string {
    const sstr = lexer.parseCString();
    lexer.ensureAndConsumeSymbol('<');
        
    const typetag = lexer.parseTypeIdentifier();
    if(typetag !== "Assembly::Identifier") {
        throw new Error(`Expected Identifier 'Assembly::Identifier' but got ${typetag}`);
    }
        
    lexer.ensureAndConsumeSymbol('>');

    return sstr;
}

function emitVarIdentifier(tkeystr: string): string {
    return `'${tkeystr}'<Assembly::VarIdentifier>`;
}

function parseVarIdentifier(lexer: BAPILexer): string {
    const sstr = lexer.parseCString();
    lexer.ensureAndConsumeSymbol('<');
        
    const typetag = lexer.parseTypeIdentifier();
    if(typetag !== "Assembly::VarIdentifier") {
        throw new Error(`Expected VarIdentifier 'Assembly::VarIdentifier' but got ${typetag}`);
    }
        
    lexer.ensureAndConsumeSymbol('>');

    return sstr;
}

export {
    emitTypeKey, emitInvokeKey, emitIdentifier, emitVarIdentifier,
    parseTypeKey, parseInvokeKey, parseIdentifier, parseVarIdentifier,

    IRSourceInfo,
    IRCRegex,
    IRURegex
};
