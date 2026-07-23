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
            return IRVoidTypeSignature.parseBAPIAsIRVoidTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRTypeSignatureNominal") {
            return IRNominalTypeSignature.parseBAPIAsIRNominalTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRTypeSignatureEList") {
            return IREListTypeSignature.parseBAPIAsIREListTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRTypeSignatureDashResult") {
            return IRDashResultTypeSignature.parseBAPIAsIRDashResultTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRFormatCStringTypeSignature") {
            return IRFormatCStringTypeSignature.parseBAPIAsIRFormatCStringTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRFormatStringTypeSignature") {
            return IRFormatStringTypeSignature.parseBAPIAsIRFormatStringTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRFormatPathTypeSignature") {
            return IRFormatPathTypeSignature.parseBAPIAsIRFormatPathTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRFormatPathFragmentTypeSignature") {
            return IRFormatPathFragmentTypeSignature.parseBAPIAsIRFormatPathFragmentTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRFormatPathGlobTypeSignature") {
            return IRFormatPathGlobTypeSignature.parseBAPIAsIRFormatPathGlobTypeSignature(lexer);
        }
        else if(tok.value === "Assembly::IRLambdaParameterPackTypeSignature") {
            return IRLambdaParameterPackTypeSignature.parseBAPIAsIRLambdaParameterPackTypeSignature(lexer);
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

    static parseBAPIAsIRVoidTypeSignature(lexer: BAPILexer): IRVoidTypeSignature {
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

    static parseBAPIAsIRNominalTypeSignature(lexer: BAPILexer): IRNominalTypeSignature {
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

    static parseBAPIAsIREListTypeSignature(lexer: BAPILexer): IREListTypeSignature {
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

    static parseBAPIAsIRDashResultTypeSignature(lexer: BAPILexer): IRDashResultTypeSignature {
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

    static parseBAPIAsIRFormatCStringTypeSignature(lexer: BAPILexer): IRFormatCStringTypeSignature {
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

    static parseBAPIAsIRFormatStringTypeSignature(lexer: BAPILexer): IRFormatStringTypeSignature {
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

    static parseBAPIAsIRFormatPathTypeSignature(lexer: BAPILexer): IRFormatPathTypeSignature {
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

    static parseBAPIAsIRFormatPathFragmentTypeSignature(lexer: BAPILexer): IRFormatPathFragmentTypeSignature {
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

    static parseBAPIAsIRFormatPathGlobTypeSignature(lexer: BAPILexer): IRFormatPathGlobTypeSignature {
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

    static parseBAPIAsIRLambdaParameterPackTypeSignature(lexer: BAPILexer): IRLambdaParameterPackTypeSignature {
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
