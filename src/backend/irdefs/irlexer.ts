import assert from "node:assert";

enum BAPITokenKind {
    EOS = "$EOS$",
    
    NoneLiteral = "none",
    TrueLiteral = "true",
    FalseLiteral = "false",
    NatLiteral = "NatLiteral",
    IntLiteral = "IntLiteral",
    ChkNatLiteral = "ChkNatLiteral",
    ChkIntLiteral = "ChkIntLiteral",
    RationalLiteral = "RationalLiteral",
    FloatLiteral = "FloatLiteral",
    DecimalLiteral = "DecimalLiteral",

    ByteBufferLiteral = "ByteBufferLiteral",

    CStringLiteral = "CStringLiteral",
    StringLiteral = "StringLiteral",
    
    CRegexLiteral = "CRegexLiteral",
    URegexLiteral = "URegexLiteral",
    
    Identifier = "Identifier",
    TypeIdentifier = "TypeIdentifier",
    
    OpenBrace = "{",
    CloseBrace = "}",
    Langle = "<",
    Rangle = ">",
    OpenParen = "(",
    CloseParen = ")",
    
    Comma = ",",
    Colon = ":",
    ColonColon = "::"
}

class BAPIToken {
    readonly kind: BAPITokenKind;
    readonly value: string;

    constructor(kind: BAPITokenKind, value: string) {
        this.kind = kind;
        this.value = value;
    }
}

const EOS_TOKEN = new BAPIToken(BAPITokenKind.EOS, "EOS");

class BAPILexer {
    readonly input: string;
    toks: BAPIToken[];
    pos: number;

    constructor(input: string) {
        this.input = input;
        this.toks = [];
        this.pos = 0;
    }

    lex(): void {
        assert(false, "Not implemented");
    }

    consumeToken(): BAPIToken {
        if(this.pos === this.toks.length) {
            return EOS_TOKEN;
        }
        else {
            return this.toks[this.pos++];
        }
    }

    peekToken(): BAPIToken {
        if(this.pos === this.toks.length) {
            return EOS_TOKEN;
        }
        else {
            return this.toks[this.pos];
        }
    }

    peekTokenKind(): BAPITokenKind {
        return this.peekToken().kind;
    }

    ensureAndConsumeToken(kind: BAPITokenKind): string {
        const tok = this.consumeToken();
        if(tok.kind !== kind) {
            throw new Error(`Expected token of kind ${kind} but got ${tok.kind}`);
        }
        
        return tok.value;
    }

    ensureAndConsumeSymbol(sym: string): void {
        const tok = this.consumeToken();
        if(tok.value !== sym) {
            throw new Error(`Expected token with value ${sym} but got ${tok.value}`);
        }
    }

    parseCString(): string {
        assert(false, "Not implemented");
    }

    ensureAndConsumeTaggedCString(tkeystr: string): string {
        assert(false, "Not implemented");
    }

    parseString(): string {
        assert(false, "Not implemented");
    }

    parseTypeIdentifier(): string {
        assert(false, "Not implemented");
    }
}

function parseListOf<T>(lexer: BAPILexer, lparen: string, rparen: string, separator: string, parseElement: (lexer: BAPILexer) => T): T[] {
    const elements: T[] = [];

    lexer.ensureAndConsumeSymbol(lparen);
    while(lexer.peekToken().value !== rparen) {
        const elem = parseElement(lexer);
        elements.push(elem);

        if(lexer.peekToken().value === separator) {
            lexer.consumeToken();
        }
        else {
            break;
        }
    }
    lexer.ensureAndConsumeSymbol(rparen);

    return elements;
}

export {
    BAPITokenKind,
    BAPIToken,
    BAPILexer,

    parseListOf
};
