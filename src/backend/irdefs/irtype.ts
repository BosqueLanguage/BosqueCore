import { BAPITokenKind, BAPILexer, parseListOf } from "./irlexer.js";
import { parseTypeKey, emitTypeKey } from "./irsupport.js";

import assert from "node:assert";

abstract class IRTypeSignature {
    readonly tkeystr: string;

    constructor(tkeystr: string) {
        this.tkeystr = tkeystr;
    }

    abstract getDirectDependencyTypes(): IRTypeSignature[];

    abstract toBAPI(): string;

    static parseBAPI(lexer: BAPILexer): IRTypeSignature {
        const tok = lexer.peekToken();
        if(tok.kind !== BAPITokenKind.TypeIdentifier) {
            throw new Error(`Expected TypeIdentifier token but got ${tok.kind}`);
        }

        if(tok.value === "Assembly::IRTypeSignatureVoid") {
            return IRVoidTypeSignature.parseBAPI_IRVoidTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRTypeSignatureNominal") {
            return IRNominalTypeSignature.parseBAPI_IRNominalTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRTypeSignatureEList") {
            return IREListTypeSignature.parseBAPI_IREListTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRTypeSignatureDashResult") {
            return IRDashResultTypeSignature.parseBAPI_IRDashResultTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRFormatCStringTypeSignature") {
            return IRFormatCStringTypeSignature.parseBAPI_IRFormatCStringTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRFormatStringTypeSignature") {
            return IRFormatStringTypeSignature.parseBAPI_IRFormatStringTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRFormatPathTypeSignature") {
            return IRFormatPathTypeSignature.parseBAPI_IRFormatPathTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRFormatPathFragmentTypeSignature") {
            return IRFormatPathFragmentTypeSignature.parseBAPI_IRFormatPathFragmentTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRFormatPathGlobTypeSignature") {
            return IRFormatPathGlobTypeSignature.parseBAPI_IRFormatPathGlobTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRLambdaParameterPackTypeSignature") {
            return IRLambdaParameterPackTypeSignature.parseBAPI_IRLambdaParameterPackTypeSignature(lexer);
        }
        else {
            throw new Error(`Unexpected TypeKey token value ${tok.value}`);
        }
    }
}

class IRVoidTypeSignature extends IRTypeSignature {
    constructor() {
        super("Void");
    }

    getDirectDependencyTypes(): IRTypeSignature[] {
        return [];
    }

    override toBAPI(): string {
        return `Assembly::IRTypeSignatureVoid{${emitTypeKey(this.tkeystr)}}`;
    }

    static parseBAPI_IRVoidTypeSignature(lexer: BAPILexer): IRTypeSignature {
        lexer.consumeToken();
        lexer.ensureAndConsumeSymbol('{');
        parseTypeKey(lexer);
        lexer.ensureAndConsumeSymbol('}');

        return new IRVoidTypeSignature();
    }
}

class IRNominalTypeSignature extends IRTypeSignature {
    constructor(tkeystr: string) {
        super(tkeystr);
    }

    getDirectDependencyTypes(): IRTypeSignature[] {
        return [];
    }

    override toBAPI(): string {
        return `Assembly::IRTypeSignatureNominal{${emitTypeKey(this.tkeystr)}}`;
    }

    static parseBAPI_IRNominalTypeSignature(lexer: BAPILexer): IRTypeSignature {
        lexer.consumeToken();
        lexer.ensureAndConsumeSymbol('{');
        const tkeystr = parseTypeKey(lexer);
        lexer.ensureAndConsumeSymbol('}');

        return new IRNominalTypeSignature(tkeystr);
    }
}

class IREListTypeSignature extends IRTypeSignature {
    readonly entries: IRTypeSignature[];

    constructor(tkeystr: string, entries: IRTypeSignature[]) {
        super(tkeystr);
        this.entries = entries;
    }

    getDirectDependencyTypes(): IRTypeSignature[] {
        return this.entries;
    }

    override toBAPI(): string {
        return `Assembly::IRTypeSignatureEList{${emitTypeKey(this.tkeystr)}, List<Assembly::IRTypeSignature>{${this.entries.map(e => e.toBAPI()).join(", ")}}}`;
    }

    static parseBAPI_IREListTypeSignature(lexer: BAPILexer): IRTypeSignature {
        lexer.consumeToken();
        lexer.ensureAndConsumeSymbol('{');
        const tkeystr = parseTypeKey(lexer);
        lexer.ensureAndConsumeSymbol(',');
        parseTypeKey(lexer);
        const entries = parseListOf<IRTypeSignature>(lexer, '{', '}', ',', IRTypeSignature.parseBAPI);
        lexer.ensureAndConsumeSymbol('}');

        return new IREListTypeSignature(tkeystr, entries);
    }
}

class IRDashResultTypeSignature extends IRTypeSignature {
    readonly entries: IRTypeSignature[];

    constructor(tkeystr: string, entries: IRTypeSignature[]) {
        super(tkeystr);
        this.entries = entries;
    }

    getDirectDependencyTypes(): IRTypeSignature[] {
        return this.entries;
    }

    override toBAPI(): string {
        return `Assembly::IRTypeSignatureDashResult{'${this.tkeystr}'<Assembly::TypeKey>, List<Assembly::IRTypeSignature>{${this.entries.map(e => e.toBAPI()).join(", ")}}}`;
    }

    static parseBAPI_IRDashResultTypeSignature(lexer: BAPILexer): IRTypeSignature {
        lexer.consumeToken();
        lexer.ensureAndConsumeSymbol('{');
        const tkeystr = parseTypeKey(lexer);
        lexer.ensureAndConsumeSymbol(',');
        parseTypeKey(lexer);
        const entries = parseListOf<IRTypeSignature>(lexer, '{', '}', ',', IRTypeSignature.parseBAPI);
        lexer.ensureAndConsumeSymbol('}');

        return new IRDashResultTypeSignature(tkeystr, entries);
    }
}

abstract class IRFormatTypeSignature extends IRTypeSignature {
    readonly rtype: IRTypeSignature;
    readonly terms: {argname: string, argtype: IRTypeSignature}[];

    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string, argtype: IRTypeSignature}[]) {
        super(tkeystr);
        this.rtype = rtype;
        this.terms = terms;
    }

    getDirectDependencyTypes(): IRTypeSignature[] {
        return [this.rtype, ...this.terms.map(t => t.argtype)];
    }

    toBAPI_IRFormatTypeSignature(): string {
        return `${this.rtype.toBAPI()}, List<Assembly::FormatTypeSignatureTerm>{${this.terms.map(t => `Assembly::FormatTypeSignatureTerm{'${t.argname}'<Assembly::Identifier>, ${t.argtype.toBAPI()}}`).join(", ")}}`;
    }

    static parseBAPI_IRFormatTypeSignature(lexer: BAPILexer): {rtype: IRTypeSignature, terms: {argname: string, argtype: IRTypeSignature}[]} {
        const rtype = IRTypeSignature.parseBAPI(lexer);
        lexer.ensureAndConsumeSymbol(',');
        const terms = parseListOf<{argname: string, argtype: IRTypeSignature}>(lexer, '{', '}', ',', (lexer) => {
            lexer.ensureAndConsumeToken(BAPITokenKind.TypeIdentifier);
            lexer.ensureAndConsumeSymbol('{');
            const argname = lexer.parseCString();
            lexer.ensureAndConsumeSymbol('<');
            const idtag = lexer.parseTypeIdentifier();
            if(idtag !== "Assembly::Identifier") {
                throw new Error(`Expected Identifier 'Assembly::Identifier' but got ${idtag}`);
            }
            lexer.ensureAndConsumeSymbol('>');
            lexer.ensureAndConsumeSymbol(',');
            const argtype = IRTypeSignature.parseBAPI(lexer);
            lexer.ensureAndConsumeSymbol('}');

            return {argname, argtype};
        });
        return {rtype, terms};
    }
}

class IRFormatCStringTypeSignature extends IRFormatTypeSignature {
    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string, argtype: IRTypeSignature}[]) {
        super(tkeystr, rtype, terms);
    }

    override toBAPI(): string {
        return `Assembly::IRFormatCStringTypeSignature{${emitTypeKey(this.tkeystr)}, ${this.toBAPI_IRFormatTypeSignature()}}`;
    }

    static parseBAPI_IRFormatCStringTypeSignature(lexer: BAPILexer): IRTypeSignature {
        lexer.consumeToken();
        lexer.ensureAndConsumeSymbol('{');
        const tkeystr = parseTypeKey(lexer);
        lexer.ensureAndConsumeSymbol(',');
        const {rtype, terms} = IRFormatTypeSignature.parseBAPI_IRFormatTypeSignature(lexer);
        lexer.ensureAndConsumeSymbol('}');

        return new IRFormatCStringTypeSignature(tkeystr, rtype, terms);
    }
}

class IRFormatStringTypeSignature extends IRFormatTypeSignature {
    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string, argtype: IRTypeSignature}[]) {
        super(tkeystr, rtype, terms);
    }

    override toBAPI(): string {
        return `Assembly::IRFormatStringTypeSignature{${emitTypeKey(this.tkeystr)}, ${this.toBAPI_IRFormatTypeSignature()}}`;
    }

    static parseBAPI_IRFormatStringTypeSignature(lexer: BAPILexer): IRTypeSignature {
        lexer.consumeToken();
        lexer.ensureAndConsumeSymbol('{');
        const tkeystr = parseTypeKey(lexer);
        lexer.ensureAndConsumeSymbol(',');
        const {rtype, terms} = IRFormatTypeSignature.parseBAPI_IRFormatTypeSignature(lexer);
        lexer.ensureAndConsumeSymbol('}');

        return new IRFormatStringTypeSignature(tkeystr, rtype, terms);
    }
}

class IRFormatPathTypeSignature extends IRFormatTypeSignature {
    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string, argtype: IRTypeSignature}[]) {
        super(tkeystr, rtype, terms);
    }

    override toBAPI(): string {
        assert(false, "IRFormatPathTypeSignature not implemented for serialization to BAPI");
    }

    static parseBAPI_IRFormatPathTypeSignature(lexer: BAPILexer): IRTypeSignature {
        assert(false, "IRFormatPathTypeSignature not implemented for deserialization from BAPI");
    }
}

class IRFormatPathFragmentTypeSignature extends IRFormatTypeSignature {
    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string, argtype: IRTypeSignature}[]) {
        super(tkeystr, rtype, terms);
    }

    override toBAPI(): string {
        assert(false, "IRFormatPathFragmentTypeSignature not implemented for serialization to BAPI");
    }

    static parseBAPI_IRFormatPathFragmentTypeSignature(lexer: BAPILexer): IRTypeSignature {
        assert(false, "IRFormatPathFragmentTypeSignature not implemented for deserialization from BAPI");
    }
}

class IRFormatPathGlobTypeSignature extends IRFormatTypeSignature {
    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string, argtype: IRTypeSignature}[]) {
        super(tkeystr, rtype, terms);
    }

    override toBAPI(): string {
        assert(false, "IRFormatPathGlobTypeSignature not implemented for serialization to BAPI");
    }

    static parseBAPI_IRFormatPathGlobTypeSignature(lexer: BAPILexer): IRTypeSignature {
        assert(false, "IRFormatPathGlobTypeSignature not implemented for deserialization from BAPI");
    }
}

class IRLambdaParameterPackTypeSignature extends IRTypeSignature {
    constructor(tkeystr: string) {
        super(tkeystr);
    }

    getDirectDependencyTypes(): IRTypeSignature[] {
        return [];
    }

    override toBAPI(): string {
        return `Assembly::IRLambdaParameterPackTypeSignature{${emitTypeKey(this.tkeystr)}}`;
    }

    static parseBAPI_IRLambdaParameterPackTypeSignature(lexer: BAPILexer): IRTypeSignature {
        lexer.consumeToken();
        lexer.ensureAndConsumeSymbol('{');
        const tkeystr = parseTypeKey(lexer);
        lexer.ensureAndConsumeSymbol('}');

        return new IRLambdaParameterPackTypeSignature(tkeystr);
    }
}

export {
    emitTypeKey, parseTypeKey,

    IRTypeSignature,
    IRVoidTypeSignature,
    IRNominalTypeSignature,
    IREListTypeSignature,
    IRDashResultTypeSignature,
    IRFormatTypeSignature,
    IRFormatCStringTypeSignature,
    IRFormatStringTypeSignature,
    IRFormatPathTypeSignature,
    IRFormatPathFragmentTypeSignature,
    IRFormatPathGlobTypeSignature,
    IRLambdaParameterPackTypeSignature
};
