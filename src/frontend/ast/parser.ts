
import { ParserEnvironment, ParserScope } from "./parser_env";
import { AndTypeSignature, AutoTypeSignature, FunctionParameter, LambdaTypeSignature, NominalTypeSignature, ErrorTypeSignature, RecordTypeSignature, TemplateTypeSignature, TupleTypeSignature, EListTypeSignature, TypeSignature, UnionTypeSignature } from "./type";
import { AbortStatement, AccessEnvValueExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, AssertStatement, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndxpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, BodyImplementation, ConstantExpressionValue, ConstructorPrimaryExpression, ConstructorRecordExpression, ConstructorTupleExpression, DebugStatement, EmptyStatement, Expression, IfStatement, IfExpression, ErrorExpression, ErrorStatement, LiteralExpressionValue, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, PostfixAccessFromIndex, PostfixAccessFromName, PostfixAsConvert, PostfixInvoke, PostfixIsTest, PostfixOp, PostfixOperation, PrefixNegateOp, PrefixNotOp, RecursiveAnnotation, ReturnStatement, SpecialConstructorExpression, Statement, TaskEventEmitStatement, VariableAssignmentStatement, VariableDeclarationStatement, IfTest, VariableRetypeStatement, ITest, ITestType, ITestLiteral, ITestNone, ITestNothing, ITestSomething, ITestOk, ITestErr, ITestSome, BSQONLiteralExpression } from "./body";
import { Assembly, ConceptTypeDecl, EntityTypeDecl, InvariantDecl, MemberFieldDecl, MethodDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, NamespaceTypedef, NamespaceUsing, PostConditionDecl, PreConditionDecl, ValidateDecl } from "./assembly";
import { BuildLevel, SourceInfo } from "../build_decls";

const { accepts, inializeLexer, lexFront } = require("@bosque/jsbrex");

const TokenStrings = {
    Clear: "[CLEAR]",
    Error: "[ERROR]",

    NumberinoInt: "[LITERAL_NUMBERINO_INT]",
    NumberinoFloat: "[LITERAL_NUMBERINO_FLOAT]",
    NumberinoRational: "[LITERAL_NUMBERINO_RATIONAL]",

    Nat: "[LITERAL_NAT]",
    Int: "[LITERAL_INT]",
    BigNat: "[LITERAL_BIGNAT]",
    BigInt: "[LITERAL_BIGINT]",
    Float: "[LITERAL_FLOAT]",
    Decimal: "[LITERAL_DECIMAL]",
    Rational: "[LITERAL_RATIONAL]",
    DecimalDegree: "[LITERAL_DECIMAL_DEGREE]",
    LatLong: "[LITERAL_LATLONG]",
    Complex: "[LITERAL_COMPLEX]",
    
    ByteBuffer: "[LITERAL_BYTEBUFFER]",
    UUIDValue: "[LITERAL_UUID]",
    ShaHashcode: "[LITERAL_SHA]",

    String: "[LITERAL_STRING]",
    ASCIIString: "[LITERAL_ASCII_STRING]",
    TemplateString: "[LITERAL_TEMPLATE_STRING]",
    TemplateASCIIString: "[LITERAL_TEMPLATE_ASCII_STRING]",

    Regex: "[LITERAL_REGEX]",
    PathItem: "[LITERAL_PATH_ITEM]",

    DateTime: "[LITERAL_DATETIME]",
    UTCDateTime: "[LITERAL_UTC_DATETIME]",
    PlainDate: "[LITERAL_PLAIN_DATE]",
    PlainTime: "[LITERAL_PLAIN_TIME]",
    TickTime: "[LITERAL_TICK_TIME]",
    LogicalTime: "[LITERAL_LOGICAL_TIME]",
    Timestamp: "[LITERAL_TIMESTAMP]",

    DeltaDateTime: "[LITERAL_DELTA_DATETIME]",
    DeltaUTCDateTime: "[LITERAL_DELTA_UTC_DATETIME]",
    DeltaPlainDate: "[LITERAL_DELTA_PLAIN_DATE]",
    DeltaPlainTime: "[LITERAL_DELTA_PLAIN_TIME]",
    DeltaSeconds: "[LITERAL_DELTA_SECONDS]",
    DeltaTickTime: "[LITERAL_DELTA_TICK_TIME]",
    DeltaLogicalTime: "[LITERAL_DELTA_LOGICAL_TIME]",
    DeltaTimestamp: "[LITERAL_DELTA_TIMESTAMP]",

    //Names
    NamespaceName: "[NAMESPACE]",
    TypeName: "[IDENTIFIER]",
    Template: "[TEMPLATE]",
    IdentifierName: "[IDENTIFIER]",
    ScopedName: "[SCOPE]",

    EndOfStream: "[EOS]"
};

class Token {
    readonly line: number;
    readonly column: number;
    readonly pos: number;
    readonly span: number;

    readonly kind: string;
    readonly data: string | undefined;

    constructor(line: number, column: number, cpos: number, span: number, kind: string, data?: string) {
        this.line = line;
        this.column = column;
        this.pos = cpos;
        this.span = span;

        this.kind = kind;
        this.data = data;
    }
}

class LexerState {
    readonly mode: string;

    cline: number;
    linestart: number;
    cpos: number;
    tokens: Token[];

    readonly symbols: string[];
    readonly attributes: string[];
    readonly keywords: string[];
    readonly namespaces: string[];
    readonly typenames: string[];

    constructor(mode: string, cline: number, linestart: number, cpos: number, tokens: Token[], symbols: string[], attributes: string[], keywords: string[], namespaces: string[], typenames: string[]) {
        this.cline = cline;
        this.linestart = linestart;
        this.cpos = cpos;
        this.tokens = [];

        this.symbols = symbols;
        this.attributes = attributes;
        this.keywords = keywords;

        this.namespaces = namespaces;
        this.typenames = typenames;
    }

    cloneForTry(mode: string): LexerState {
        return new LexerState(mode, this.cline, this.linestart, this.cpos, [...this.tokens], this.symbols, this.attributes, this.keywords, this.namespaces, this.typenames);
    }
}

class Lexer {
    readonly macrodefs: string[];
    readonly input: string;
    
    readonly stateStack: LexerState[];

    private currentState(): LexerState {
        return this.stateStack[this.stateStack.length - 1];
    }

    private findKeywordString(str: string): string | undefined {
        const kws = this.currentState().keywords;

        let imin = 0;
        let imax = kws.length;

        while (imin < imax) {
            const imid = Math.floor((imin + imax) / 2);

            const scmpval = (str.length !== kws[imid].length) ? (kws[imid].length - str.length) : ((str !== kws[imid]) ? (str < kws[imid] ? -1 : 1) : 0);
            if (scmpval === 0) {
                return kws[imid];
            }
            else if (scmpval < 0) {
                imax = imid;
            }
            else {
                imin = imid + 1;
            }
        }
        return undefined;
    }

    constructor(input: string, macrodefs: string[], istate: LexerState) {
        this.macrodefs = macrodefs;
        this.input = input;

        this.stateStack = [istate];
    }

    ////
    //Helpers
    private recordLexToken(epos: number, kind: string) {
        const cstate = this.currentState();

        cstate.tokens.push(new Token(cstate.cline, cstate.cpos - cstate.linestart, cstate.cpos, epos - cstate.cpos, kind, kind)); //set data to kind string
        cstate.cpos = epos;
    }

    private recordLexTokenWData(epos: number, kind: string, data: string) {
        const cstate = this.currentState();

        cstate.tokens.push(new Token(cstate.cline, cstate.cpos - cstate.linestart, cstate.cpos, epos - cstate.cpos, kind, data));
        cstate.cpos = epos;
    }

    private static readonly _s_whitespaceRe = '/[ %n;%v;%f;%r;%t;]/';
    private tryLexWS(): boolean {
        const cstate = this.currentState();
        const m = lexFront(Lexer._s_whitespaceRe, cstate.cpos);

        if (m === null) {
            return false;
        }

        for (let i = 0; i < m.length; ++i) {
            if (m[i] === "\n") {
                cstate.cline++;
                cstate.linestart = cstate.cpos + i + 1;
            }
        }

        cstate.cpos += m.length;
        return true;
    }

    private tryLexLineComment(): boolean {
        const cstate = this.currentState();
        const m = this.input.startsWith("%%", cstate.cpos);

        if (!m) {
            return false;
        }

        const epos = this.input.indexOf("\n", cstate.cpos);
        for (let i = 0; i < (epos - cstate.cpos); ++i) {
            if (this.input[cstate.cpos + i] === "\n") {
                cstate.cline++;
                cstate.linestart = this.m_cpos + i + 1;
            }
        }

        this.m_cpos += m[0].length;
        return true;
    }

    private static readonly _s_templateNameRe = "/[A-Z]/";
    private isTemplateName(str: string): boolean {
        return accepts(Lexer._s_templateNameRe, str);
    }

    private isIdentifierName(str: string): boolean {
        return /^([$]|([$]?([_a-z]|([_a-z][_a-zA-Z0-9]+))))$/.test(str);
    }

    private static readonly _s_intNumberinoRe = /0|[1-9][0-9]*/y;

    private static readonly _s_intRe = /(0|[1-9][0-9]*)i/y;
    private static readonly _s_natRe = /(0|[1-9][0-9]*)n/y;

    private static readonly _s_floatRe = /([0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?f/y;
    private static readonly _s_decimalRe = /([0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?d/y;

    private static readonly _s_bigintRe = /(0|[1-9][0-9]*)I/y;
    private static readonly _s_bignatRe = /(0|[1-9][0-9]*)N/y;
    private static readonly _s_rationalRe = /((0|[1-9][0-9]*)|(0|[1-9][0-9]*)\/([1-9][0-9]*))R/y;

    private tryLexNumber(): boolean {
        Lexer._s_rationalRe.lastIndex = this.m_cpos;
        const mr = Lexer._s_rationalRe.exec(this.m_input);
        if (mr !== null) {
            this.recordLexTokenWData(this.m_cpos + mr[0].length, TokenStrings.Rational, mr[0]);
            return true;
        }

        Lexer._s_bignatRe.lastIndex = this.m_cpos;
        const mbn = Lexer._s_bignatRe.exec(this.m_input);
        if (mbn !== null) {
            this.recordLexTokenWData(this.m_cpos + mbn[0].length, TokenStrings.BigNat, mbn[0]);
            return true;
        }

        Lexer._s_bigintRe.lastIndex = this.m_cpos;
        const mbi = Lexer._s_bigintRe.exec(this.m_input);
        if (mbi !== null) {
            this.recordLexTokenWData(this.m_cpos + mbi[0].length, TokenStrings.BigInt, mbi[0]);
            return true;
        }

        Lexer._s_decimalRe.lastIndex = this.m_cpos;
        const md = Lexer._s_decimalRe.exec(this.m_input);
        if (md !== null) {
            this.recordLexTokenWData(this.m_cpos + md[0].length, TokenStrings.Decimal, md[0]);
            return true;
        }

        Lexer._s_floatRe.lastIndex = this.m_cpos;
        const mf = Lexer._s_floatRe.exec(this.m_input);
        if (mf !== null) {
            this.recordLexTokenWData(this.m_cpos + mf[0].length, TokenStrings.Float, mf[0]);
            return true;
        }

        Lexer._s_natRe.lastIndex = this.m_cpos;
        const mn = Lexer._s_natRe.exec(this.m_input);
        if (mn !== null) {
            this.recordLexTokenWData(this.m_cpos + mn[0].length, TokenStrings.Nat, mn[0]);
            return true;
        }

        Lexer._s_intRe.lastIndex = this.m_cpos;
        const mi = Lexer._s_intRe.exec(this.m_input);
        if (mi !== null) {
            this.recordLexTokenWData(this.m_cpos + mi[0].length, TokenStrings.Int, mi[0]);
            return true;
        }

        Lexer._s_intNumberinoRe.lastIndex = this.m_cpos;
        const inio = Lexer._s_intNumberinoRe.exec(this.m_input);
        if (inio !== null) {
            this.recordLexTokenWData(this.m_cpos + inio[0].length, TokenStrings.Numberino, inio[0]);
            return true;
        }

        return false;
    }

    private static readonly _s_stringRe = /"[^"]*"/uy;
    private static readonly _s_ascii_stringRe = /ascii\{"[^"]*"\}/uy;
    private static readonly _s_template_stringRe = /`[^`]*`/uy;
    private static readonly _s_ascii_template_stringRe = /ascii\{`[^`]*`\}/uy;

    private tryLexString() {
        Lexer._s_template_stringRe.lastIndex = this.m_cpos;
        const template_string_m = Lexer._s_template_stringRe.exec(this.m_input);
        if (template_string_m !== null) {
            this.recordLexTokenWData(this.m_cpos + template_string_m[0].length, TokenStrings.TemplateString, template_string_m[0]);
            return true;
        }

        Lexer._s_ascii_template_stringRe.lastIndex = this.m_cpos;
        const ascii_template_string_m = Lexer._s_ascii_template_stringRe.exec(this.m_input);
        if (ascii_template_string_m !== null) {
            this.recordLexTokenWData(this.m_cpos + ascii_template_string_m[0].length, TokenStrings.TemplateASCIIString, ascii_template_string_m[0]);
            return true;
        }

        Lexer._s_stringRe.lastIndex = this.m_cpos;
        const ms = Lexer._s_stringRe.exec(this.m_input);
        if (ms !== null) {
            this.recordLexTokenWData(this.m_cpos + ms[0].length, TokenStrings.String, ms[0]);
            return true;
        }

        Lexer._s_ascii_stringRe.lastIndex = this.m_cpos;
        const mas = Lexer._s_ascii_stringRe.exec(this.m_input);
        if (mas !== null) {
            this.recordLexTokenWData(this.m_cpos + mas[0].length, TokenStrings.ASCIIString, mas[0]);
            return true;
        }

        return false;
    }

    private static readonly _s_regexRe = /\/[^\r\n]*(\\(.)[^\r\n]*)*\//y;
    private tryLexRegex() {
        Lexer._s_regexRe.lastIndex = this.m_cpos;
        const ms = Lexer._s_regexRe.exec(this.m_input);
        if (ms !== null && RegexFollows.has(this.m_tokens[this.m_tokens.length - 1].kind)) {
            this.recordLexTokenWData(this.m_cpos + ms[0].length, TokenStrings.Regex, ms[0]);
            return true;
        }

        return false;
    }

    private static readonly _s_bsqvvRe = /[{}"]/;
    private tryLexBSQON() {
        let bbpos = this.m_cpos;
        if (!this.m_input.startsWith("bsqon{", bbpos)) {
            return false;
        }

        //
        //TODO: when we support native inline BSQON parsing we want to support the form bsqon<T>{...} as well
        //

        bbpos += 6;

        let pdepth = 1;
        while(pdepth !== 0 && bbpos < this.m_input.length) {
            const mm = Lexer._s_bsqvvRe.exec(this.m_input.slice(bbpos));
            if(mm === null) {
                return false;
            }

            if(mm[0] === "{") {
                pdepth++;
                bbpos = bbpos + mm.index + 1;
            }
            else if(mm[0] === "}") {
                pdepth--;
                bbpos = bbpos + mm.index + 1;
            }
            else {
                bbpos = bbpos + mm.index;
                       
                Lexer._s_stringRe.lastIndex = bbpos;
                const ms = Lexer._s_stringRe.exec(this.m_input);
                if (ms === null) {
                    return false;
                }

                bbpos = bbpos + ms[0].length;
            }
        }

        if (pdepth === 0) {
            this.recordLexTokenWData(bbpos, TokenStrings.BSQON, this.m_input.substring(this.m_cpos, bbpos));
            return true;
        }
        else {
            return false;
        }
    }

    private static readonly _s_bsqexamplefilebeginRe = /(\s+([.]{1,2}\/)|([$]{))/y;
    private static readonly _s_bsqexamplefileendRe = /;/;
    private static readonly _s_bsqexamplesplitRe = /->|"|;/;
    private static readonly _s_bsqexampleendRe = /[;"]/;
    private tryLexBSQONExample() {
        if (!this.m_input.startsWith("example ", this.m_cpos)) {
            return false;
        }

        this.recordLexToken(this.m_cpos + KW_example.length, KW_example);

        Lexer._s_bsqexamplefilebeginRe.lastIndex = this.m_cpos;
        const fb = Lexer._s_bsqexamplefilebeginRe.exec(this.m_input);
        if (fb !== null && fb.index === this.m_cpos) {
            const fe = Lexer._s_bsqexamplefileendRe.exec(this.m_input.slice(this.m_cpos));
            if (fe === null) {
                return false;
            }

            this.recordLexTokenWData(this.m_cpos + fe.index, TokenStrings.BSQON_EXAMPLE_FILE, this.m_input.substring(this.m_cpos, this.m_cpos + fe.index));
            return true;
        }
        else {
            let bbpos = this.m_cpos;
            while (bbpos < this.m_input.length) {
                const mm = Lexer._s_bsqexamplesplitRe.exec(this.m_input.slice(bbpos));
                if (mm === null) {
                    return false;
                }

                if (mm[0] === ";") {
                    return false;
                }

                if (mm[0] === "->") {
                    bbpos = bbpos + mm.index;
                    break;
                }
                else {
                    bbpos = bbpos + mm.index;

                    Lexer._s_stringRe.lastIndex = bbpos;
                    const ms = Lexer._s_stringRe.exec(this.m_input);
                    if (ms === null) {
                        return false;
                    }

                    bbpos = bbpos + ms[0].length;
                }
            }
            this.recordLexTokenWData(bbpos, TokenStrings.BSQON_EXAMPLE_ARGS, this.m_input.substring(this.m_cpos, bbpos).trim());
            this.m_cpos += 2; //skip ->

            bbpos = this.m_cpos;
            while (bbpos < this.m_input.length) {
                const mm = Lexer._s_bsqexampleendRe.exec(this.m_input.slice(bbpos));
                if (mm === null) {
                    return false;
                }

                if (mm[0] === "->") {
                    return false;
                }

                if (mm[0] === ";") {
                    bbpos = bbpos + mm.index;
                    break;
                }
                else {
                    bbpos = bbpos + mm.index;

                    Lexer._s_stringRe.lastIndex = bbpos;
                    const ms = Lexer._s_stringRe.exec(this.m_input);
                    if (ms === null) {
                        return false;
                    }

                    bbpos = bbpos + ms[0].length;
                }
            }
            this.recordLexTokenWData(bbpos, TokenStrings.BSQON_EXAMPLE_RESULT, this.m_input.substring(this.m_cpos, bbpos).trim());

            return true;
        }
    }

    private static readonly _s_symbolRe = /[\W]+/y;
    private tryLexSymbol() {
        Lexer._s_symbolRe.lastIndex = this.m_cpos;
        const ms = Lexer._s_symbolRe.exec(this.m_input);
        if (ms !== null) {
            const sym = SymbolStrings.find((value) => ms[0].startsWith(value));
            if (sym !== undefined) {
                this.recordLexToken(this.m_cpos + sym.length, sym);
                return true;
            }
        }

        return false;
    }

    private static readonly _s_nameRe = /(recursive\?)|([$]?\w*)/y;
    private tryLexName(): boolean {
        Lexer._s_nameRe.lastIndex = this.m_cpos;
        const m = Lexer._s_nameRe.exec(this.m_input);

        const kwmatch = (m !== null) ? Lexer.findKeywordString(m[0]) : undefined;
        if (kwmatch !== undefined && m !== null) {
            this.recordLexToken(this.m_cpos + m[0].length, kwmatch);
            return true;
        }
        else if(m !== null && this.isFormatName(m[0])) {
            const spec = m[0];
            this.recordLexTokenWData(this.m_cpos + spec.length, TokenStrings.FormatSpecifier, spec);
            return true;
        }
        else if (m !== null && this.isIdentifierName(m[0])) {
            const name = m[0];
            const isTypeThing = /^_[A-Z]/.test(name);
            if (isTypeThing) {
                this.recordLexToken(this.m_cpos + 1, TokenStrings.FollowTypeSep);
            }
            else {
                this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Identifier, name);
            }
            return true;
        }
        else if (m !== null && this.isTemplateName(m[0])) {
            const name = m[0];
            this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Template, name);
            return true;
        }
        else {
            if(this.isInScopeNameMode()) {
                const scopeopt = this.tryExtractScopeName();
                if(scopeopt !== undefined) {
                    this.recordLexTokenWData(this.m_cpos + scopeopt.length, TokenStrings.ScopeName, scopeopt);
                    return true;
                }
                else {
                    this.recordLexToken(this.m_cpos + 1, TokenStrings.Error);
                    return false;
                }
            }
            else {
                const nsopt = this.tryExtractNamespaceName();
                if(nsopt !== undefined) {
                    this.recordLexTokenWData(this.m_cpos + nsopt.length, TokenStrings.Namespace, nsopt);
                    return true;
                }
                else {
                    const topt = this.tryExtractTypenameName();
                    if(topt !== undefined) {
                        this.recordLexTokenWData(this.m_cpos + topt.length, TokenStrings.Type, topt);
                        return true;
                    }
                    else {
                        this.recordLexToken(this.m_cpos + 1, TokenStrings.Error);
                        return false;
                    }
                }
            }
        }
    }

    static isAttributeKW(str: string) {
        return AttributeStrings.indexOf(str) !== -1;
    }

    private static readonly _s_macroRe = /(#if[ ]+([A-Z][_A-Z0-9]*)|#else|#endif)/y;
    tryLexMacroOp(): [string, string | undefined] | undefined {
        Lexer._s_macroRe.lastIndex = this.m_cpos;
        const m = Lexer._s_macroRe.exec(this.m_input);
        if (m === null) {
            return undefined;
        }

        const name = m[0].trim();
        this.m_cpos += m[0].length;

        if(name.slice(0, "#if".length) === "#if") {
            return ["#if", name.slice("#if".length).trim()];
        }
        else {
            return [name, undefined]
        }
    }

    lex(): Token[] {
        if (this.m_tokens.length !== 0) {
            return this.m_tokens;
        }

        let mode: "scan" | "normal" = "normal";
        let macrostack: ("scan" | "normal")[] = []

        this.m_tokens = [];
        while (this.m_cpos < this.m_input.length) {
            if(mode === "scan") {
                const macro = this.tryLexMacroOp();
                if (macro !== undefined) {
                    if (macro[0] === "#if") {
                        macrostack.push("scan")
                    }
                    else if (macro[0] === "#else") {
                        mode = macrostack[macrostack.length - 1];
                    }
                    else {
                        mode = macrostack.pop() as "scan" | "normal";
                    }
                }
                else {
                    const nexthash = this.m_input.indexOf("#", this.m_cpos + 1);
                    if(nexthash === -1) {
                        //ended in dangling macro
                        this.recordLexToken(this.m_input.length, TokenStrings.Error);
                        this.m_cpos = this.m_input.length;
                    }
                    else {
                        const skips = this.m_input.slice(this.m_cpos, nexthash);

                        for (let i = 0; i < skips.length; ++i) {
                            if (skips[i] === "\n") {
                                this.m_cline++;
                                this.m_linestart = this.m_cpos + i + 1;
                            }
                        }

                        this.m_cpos = nexthash;
                    }
                }
            }
            else {
                const macro = this.tryLexMacroOp();
                if(macro !== undefined) {
                    if(macro[0] === "#if") {
                        macrostack.push("normal")
                        if(this.m_macrodefs.includes(macro[1] as string)) {
                            mode = "normal";
                        }
                        else {
                            mode = "scan";
                        }
                    }
                    else if(macro[0] === "#else") {
                        mode = "scan";
                    }
                    else {
                        mode = macrostack.pop() as "scan" | "normal";
                    }
                }
                else {
                    if (this.tryLexWS() || this.tryLexComment()) {
                        //continue
                    }
                    else if (this.tryLexBSQONExample()) {
                        //continue
                    }
                    else if (this.tryLexNumber() || this.tryLexString() || this.tryLexRegex() || this.tryLexBSQON()) {
                        //continue
                    }
                    else if (this.tryLexSymbol() || this.tryLexName()) {
                        //continue
                    }
                    else {
                        this.recordLexToken(this.m_cpos + 1, TokenStrings.Error);
                    }
                }
            }
        }

        this.recordLexToken(this.m_input.length, TokenStrings.EndOfStream);
        return this.m_tokens;
    }
}

class ParseError extends Error {
    constructor(line: number, message?: string) {
        super(`Parse failure on line ${line} -- ${message}`);
        Object.setPrototypeOf(this, new.target.prototype);
    }
}

enum InvokableKind {
    Basic,
    Member,
    SelfMember,
    PCodeFn,
    PCodePred,
    DynamicOperator
}

class Parser {
    private m_tokens: Token[];
    private m_cpos: number;
    private m_epos: number;

    private m_penv: ParserEnvironment;

    private m_errors: [string, number, string][];
    private m_recoverStack: number[];

    constructor(assembly: Assembly) {
        this.m_tokens = [];
        this.m_cpos = 0;
        this.m_epos = 0;

        this.m_penv = new ParserEnvironment(assembly);

        this.m_errors = [];
        this.m_recoverStack = [];
    }

    private initialize(toks: Token[]) {
        this.m_tokens = toks;
        this.m_cpos = 0;
        this.m_epos = toks.length;
    }

    ////
    //Helpers

    private static attributeSetContains(attr: string, attribs: string[]): boolean {
        return attribs.indexOf(attr) !== -1;
    }

    private getCurrentLine(): number {
        return this.m_tokens[this.m_cpos].line;
    }

    private getCurrentSrcInfo(): SourceInfo {
        const tk = this.m_tokens[this.m_cpos];
        return new SourceInfo(tk.line, 0, tk.pos, tk.span);
    }

    private setRecover(pos: number) {
        this.m_recoverStack.push(pos);
    }

    private clearRecover(pos?: number) {
        this.m_recoverStack.pop();
    }

    private processRecover() {
        this.m_cpos = this.m_recoverStack.pop() as number;
    }

    private raiseError(line: number, msg: string) {
        this.m_errors.push([this.m_penv.getCurrentFile(), line, msg]);
        throw new ParseError(line, msg);
    }

    private ensureTaskOpOk() {
        if(!this.m_penv.taskOpsOk()) {
            this.raiseError(this.getCurrentLine(), "Task operations are only permitted in \".bsqtask\" files");
        }
    }

    private scanMatchingParens(lp: string, rp: string, sindex?: number): number {
        let pscount = 1;
        for (let pos = this.m_cpos + (sindex || 0) + 1; pos < this.m_epos; ++pos) {
            const tok = this.m_tokens[pos];
            if (tok.kind === lp) {
                pscount++;
            }
            else if (tok.kind === rp) {
                pscount--;
            }
            else {
                //nop
            }

            if (pscount === 0) {
                return pos + 1;
            }
        }

        return this.m_epos;
    }

    private scanCodeParens(): number {
        let pscount = 1;
        for (let pos = this.m_cpos + 1; pos < this.m_epos; ++pos) {
            const tok = this.m_tokens[pos];
            if (LeftScanParens.indexOf(tok.kind) !== -1) {
                pscount++;
            }
            else if (RightScanParens.indexOf(tok.kind) !== -1) {
                pscount--;
            }
            else {
                //nop
            }

            if (pscount === 0) {
                return pos + 1;
            }
        }

        return this.m_epos;
    }

    private scanLParens(cpos: number): number {
        let pscount = 1;
        for (let pos = cpos + 1; pos < this.m_epos; ++pos) {
            const tok = this.m_tokens[pos];
            if (tok.kind === SYM_lparen) {
                pscount++;
            }
            else if (tok.kind === SYM_rparen) {
                pscount--;
            }
            else {
                //nop
            }

            if (pscount === 0) {
                return pos + 1;
            }
        }

        return this.m_epos;
    }

    private setNamespaceAndFile(ns: string, file: string) {
        this.m_penv.setNamespaceAndFile(ns, file);
    }

    private peekToken(pos?: number): string {
        return this.m_tokens[this.m_cpos + (pos || 0)].kind;
    }

    private peekTokenData(pos?: number): string {
        return this.m_tokens[this.m_cpos + (pos || 0)].data as string;
    }

    private testToken(kind: string): boolean {
        return (this.m_cpos !== this.m_epos) && this.m_tokens[this.m_cpos].kind === kind;
    }

    private testFollows(...kinds: string[]): boolean {
        for (let i = 0; i < kinds.length; ++i) {
            if (this.m_cpos + i === this.m_epos || this.m_tokens[this.m_cpos + i].kind !== kinds[i]) {
                return false;
            }
        }

        return true;
    }

    private consumeToken() {
        this.m_cpos++;
    }

    private consumeTokenIf(kind: string) {
        if (this.testToken(kind)) {
            this.consumeToken();
        }
    }

    private testAndConsumeTokenIf(kind: string): boolean {
        const test = this.testToken(kind);
        if (test) {
            this.consumeToken();
        }
        return test;
    }

    private consumeTokenAndGetValue(): string {
        const td = this.m_tokens[this.m_cpos].data;
        this.consumeToken();
        return td as string;
    }

    private ensureToken(kind: string, contextinfo: string) {
        if (!this.testToken(kind)) {
            const found = this.m_tokens[this.m_cpos].data || this.m_tokens[this.m_cpos].kind;
            this.raiseError(this.m_tokens[this.m_cpos].line, `Expected "${kind}" but found "${found}" when trying to parse: ${contextinfo}`);
        }
    }

    private ensureAndConsumeToken(kind: string, contextinfo: string) {
        this.ensureToken(kind, contextinfo);
        this.consumeToken();
    }

    private ensureNotToken(kind: string, contextinfo: string) {
        if (this.testToken(kind)) {
            this.raiseError(this.m_tokens[this.m_cpos].line, `Token "${kind}" was not expected when trying to parse: ${contextinfo}`);
        }
    }

    private scanToken(tok: string): number {
        let pos = this.m_cpos;

        while (pos !== this.m_epos) {
            if (this.m_tokens[pos].kind === tok) {
                return pos;
            }
            pos++;
        }
        return this.m_epos;
    }

    private scanTokenOptions(...toks: string[]): number {
        let pos = this.m_cpos;

        while (pos !== this.m_epos) {
            if (toks.indexOf(this.m_tokens[pos].kind) !== -1) {
                return pos;
            }
            pos++;
        }
        return this.m_epos;
    }

    private parseListOf<T>(contextinfobase: string, start: string, end: string, sep: string, fn: () => T): T[] {
        let result: T[] = [];

        this.ensureAndConsumeToken(start, contextinfobase);
        while (!this.testAndConsumeTokenIf(end)) {
            result.push(fn());
            
            if (this.testAndConsumeTokenIf(sep)) {
                this.ensureNotToken(end, `element in ${contextinfobase} list`);
            }
            else {
                this.ensureToken(end, `element in ${contextinfobase} list`);
            }
        }

        return result;
    }

    private parseBuildInfo(cb: BuildLevel): BuildLevel {
        if( this.testToken(KW_debug) || this.testToken(KW_test) || this.testToken(KW_release)) {
            return this.consumeTokenAndGetValue() as "spec" | "debug" | "test" | "release" | "safety";
        }
        else {
            return cb;
        }
    }

    ////
    //Misc parsing

    private parseInvokableCommon(ikind: InvokableKind, noBody: boolean, attributes: string[], isrecursive: "yes" | "no" | "cond", terms: TemplateTermDecl[], implicitTemplates: string[], termRestrictions: TypeConditionRestriction | undefined, optSelfRef: boolean): InvokeDecl {
        const sinfo = this.getCurrentSrcInfo();
        const srcFile = this.m_penv.getCurrentFile();
        const line = this.getCurrentLine();

        let resultInfo = this.m_penv.SpecialAutoSignature;

        const params = this.parseListOf<FunctionParameter>("function declaration", SYM_lparen, SYM_rparen, SYM_coma, () => {
            this.ensureToken(TokenStrings.Identifier, "function parameter");
            const pname = this.consumeTokenAndGetValue();

            let argtype = this.m_penv.SpecialAutoSignature;
            if (this.testAndConsumeTokenIf(SYM_colon)) {
                argtype = this.parseTypeSignature();
            }
            else {
                if (ikind !== InvokableKind.PCodeFn && ikind !== InvokableKind.PCodePred) {
                    this.raiseError(line, "Missing type specifier -- auto typing is only supported for lambda parameter declarations");
                }
            }

            let litexp: LiteralExpressionValue | undefined = undefined;
            if(this.testAndConsumeTokenIf("===")) {
                if(ikind !== InvokableKind.DynamicOperator) {
                    this.raiseError(line, "Literal match parameters are only allowed on dynamic operator definitions");
                }

                litexp = this.parseLiteralExpression("dynamic dispatch literal value");
            }

            return new FunctionParameter(pname, argtype, litexp);
        });

        const allTypedParams = params.every((param) => !(param.type instanceof AutoTypeSignature));
        if (this.testAndConsumeTokenIf(SYM_colon)) {
            resultInfo = this.parseTypeSignature();
        }
        else {
            if (ikind === InvokableKind.PCodePred && allTypedParams) {
                resultInfo = new NominalTypeSignature(sinfo, "Core", ["Bool"]);
            }

            if (ikind !== InvokableKind.PCodeFn && ikind !== InvokableKind.PCodePred) {
                if(!optSelfRef !== true) {
                    this.raiseError(line, "Cannot have void return unless one of the reciver is by ref");
                }
                resultInfo = this.m_penv.SpecialNoneSignature; //void conversion
            }
        }

        const argNames = new Set<string>(params.map((param) => param.name));
        if(ikind === InvokableKind.Member) {
            argNames.add("this");
        }
        if(ikind === InvokableKind.SelfMember) {
            argNames.add("self");
        }

        let preconds: PreConditionDecl[] = [];
        let postconds: PostConditionDecl[] = [];
        let samples: (InvokeSampleDeclInline | InvokeSampleDeclFile)[] = [];
        
        const boundtemplates = new Set<string>(!(ikind === InvokableKind.PCodeFn || ikind === InvokableKind.PCodePred) ? [...terms.map((tt) => tt.name), ...implicitTemplates] : []);
        if (ikind === InvokableKind.PCodeFn || ikind === InvokableKind.PCodePred) {
            this.ensureAndConsumeToken(SYM_bigarrow, "a lambda declaration");
        }
        else {
            //
            //TODO: in type checker and emitter need to (1) pull these into concrete impls frim abstract impls (2) make sure concrete impls don't extend abstract requirements 
            //      -- includes operators and virtual methods
            //
            [preconds, postconds] = this.parsePreAndPostConditions(sinfo, argNames, boundtemplates, resultInfo);
            samples = this.parseSamples(sinfo);
        }

        let body: BodyImplementation | undefined = undefined;
        let capturedvars = new Set<string>();
        let capturedtemplates = new Set<string>();
        if (noBody) {
            this.ensureAndConsumeToken(SYM_semicolon, "an abstract function declaration");
        }
        else {
            try {
                this.m_penv.pushFunctionScope(new FunctionScope(argNames, boundtemplates, resultInfo, ikind === InvokableKind.PCodeFn || ikind === InvokableKind.PCodePred));
                body = this.parseBody(srcFile);
                capturedvars = this.m_penv.getCurrentFunctionScope().getCaptureVars();
                capturedtemplates = this.m_penv.getCurrentFunctionScope().getCaptureTemplates();
                this.m_penv.popFunctionScope();
            }
            catch (ex) {
                this.m_penv.popFunctionScope();
                throw ex;
            }
        }

        if (ikind === InvokableKind.PCodeFn || ikind === InvokableKind.PCodePred) {
            const bbody = body as BodyImplementation;
            return InvokeDecl.createPCodeInvokeDecl(this.m_penv.getCurrentNamespace(), sinfo, this.getCurrentSrcInfo(), srcFile, attributes, isrecursive, params, resultInfo, capturedvars, capturedtemplates, bbody, ikind === InvokableKind.PCodeFn, ikind === InvokableKind.PCodePred);
        }
        else {
            if(body === undefined) {
                return InvokeDecl.createStandardInvokeDecl(this.m_penv.getCurrentNamespace(), sinfo, this.getCurrentSrcInfo(), srcFile, attributes, isrecursive, terms, termRestrictions, params, optSelfRef, resultInfo, preconds, postconds, samples, undefined);
            }
            else {
                if(body.body instanceof SynthesisBody) {
                    return InvokeDecl.createSynthesisInvokeDecl(this.m_penv.getCurrentNamespace(), sinfo, this.getCurrentSrcInfo(), srcFile, attributes, isrecursive, terms, termRestrictions, params, optSelfRef, resultInfo, preconds, postconds, samples, body);
                }
                else {
                    return InvokeDecl.createStandardInvokeDecl(this.m_penv.getCurrentNamespace(), sinfo, this.getCurrentSrcInfo(), srcFile, attributes, isrecursive, terms, termRestrictions, params, optSelfRef, resultInfo, preconds, postconds, samples, body);
                }
            }
        }
    }

    ////
    //Type parsing

    private parseTypeSignature(): TypeSignature {
        return this.parseOrCombinatorType();
    }

    private parseOrCombinatorType(): TypeSignature {
        const ltype = this.parsePostfixTypeReference();
        if (!this.testToken(SYM_bar)) {
            return ltype;
        }
        else {
            this.consumeToken();
            return Parser.orOfTypeSignatures(ltype.sinfo, ltype, this.parseOrCombinatorType());
        }
    }

    private parsePostfixTypeReference(): TypeSignature {
        let roottype = this.parseCombineCombinatorType();
        while (this.testAndConsumeTokenIf(SYM_question)) {
            roottype = this.parseNoneableType(roottype);
        }
        return roottype;
    }

    private parseNoneableType(basetype: TypeSignature): TypeSignature {
        return Parser.orOfTypeSignatures(basetype.sinfo, basetype, this.m_penv.SpecialNoneSignature);
    }

    private parseCombineCombinatorType(): TypeSignature {
        const ltype = this.parseProjectType();
        if (!this.testToken(SYM_amp)) {
            return ltype;
        }
        else {
            this.consumeToken();
            return this.andOfTypeSignatures(ltype.sinfo, ltype, this.parseCombineCombinatorType());
        }
    }

    private parseProjectType(): TypeSignature {
        const sinfo = this.getCurrentSrcInfo();

        const ltype = this.parseBaseTypeReference();
        if (!this.testToken(SYM_bang)) {
            return ltype;
        }
        else {
            this.consumeToken();
            const ptype = this.parseNominalType();
            
            return new ProjectTypeSignature(sinfo, ltype, ptype);
        }
    }

    private parseBaseTypeReference(): TypeSignature {
        switch (this.peekToken()) {
            case TokenStrings.Template: {
                return this.parseTemplateTypeReference();
            }
            case TokenStrings.Namespace:
            case TokenStrings.Type:
                return this.parseNominalType();
            case SYM_lbrack:
                return this.parseTupleType();
            case SYM_lbrace:
                return this.parseRecordType();
            case KW_function:
            case KW_pred:
            case KW_recursive_q:
            case KW_recursive:
                return this.parsePCodeType();
            case SYM_lparen: {
                this.consumeToken();
                const ptype = this.parseTypeSignature();
                this.ensureAndConsumeToken(SYM_rparen, "(TYPE _<- missing paren?");

                return ptype;
            }
            case TokenStrings.ScopeName: {
                //TODO: This is a dummy case for the parse provides call in pass1 where we just need to scan and discard the type info -- we should actually write a better pass for this
                this.consumeToken();
                this.parseTermList();
                return new NominalTypeSignature(SourceInfo.implicitSourceInfo(), "Core", ["DummySig"]);
            }
            default: {
                this.raiseError(this.getCurrentLine(), "Could not parse type");
                return new ParseErrorTypeSignature(SourceInfo.implicitSourceInfo());
            }
        }
    }

    private parseTemplateTypeReference(): TypeSignature {
        const sinfo = this.getCurrentSrcInfo();

        const tname = this.consumeTokenAndGetValue();
        this.m_penv.useTemplateType(tname);

        return new TemplateTypeSignature(sinfo, tname);
    }

    private parseTermList(): TypeSignature[] {
        let terms: TypeSignature[] = [];
        if (this.testToken(SYM_le)) {
            try {
                this.setRecover(this.scanMatchingParens(SYM_le, SYM_ge));
                terms = this.parseListOf<TypeSignature>("template term list", SYM_le, SYM_ge, SYM_coma, () => {
                    return this.parseTypeSignature();
                });

                this.clearRecover();
            }
            catch (ex) {
                this.processRecover();
            }
        }
        return terms;
    }

    private parseNominalType(): TypeSignature {
        const sinfo = this.getCurrentSrcInfo();

        let ns: string | undefined = undefined;
        if (this.testToken(TokenStrings.Namespace)) {
            ns = this.consumeTokenAndGetValue();
            this.ensureAndConsumeToken(SYM_coloncolon, "nominal type after namespace");
        }

        const tname = this.consumeTokenAndGetValue();
        ns = this.m_penv.tryResolveNamespace(ns, tname);
        if (ns === undefined) {
            ns = "[Unresolved Namespace]";
        }

        let tnames: string[] = [tname];
        let terms: TypeSignature[] = this.parseTermList();

        while (this.testFollows(SYM_coloncolon, TokenStrings.Type)) {
            this.ensureAndConsumeToken(SYM_coloncolon, "nominal type after nested type");

            this.ensureToken(TokenStrings.Type, "nominal type after scope operator");
            const stname = this.consumeTokenAndGetValue();
            tnames.push(stname);

            const sterms = this.parseTermList();
            terms = [...terms, ...sterms];
        }

        return new NominalTypeSignature(sinfo, ns as string, tnames, terms);
    }

    private parseTupleType(): TypeSignature {
        const sinfo = this.getCurrentSrcInfo();

        let entries: TypeSignature[] = [];

        try {
            this.setRecover(this.scanMatchingParens(SYM_lbrack, SYM_rbrack));
            entries = this.parseListOf<TypeSignature>("tuple type", SYM_lbrack, SYM_rbrack, SYM_coma, () => {
                const rtype = this.parseTypeSignature();

                return rtype;
            });

            this.clearRecover();
            return new TupleTypeSignature(sinfo, entries);
        }
        catch (ex) {
            this.processRecover();
            return new ParseErrorTypeSignature(sinfo);
        }
    }

    private parseRecordType(): TypeSignature {
        const sinfo = this.getCurrentSrcInfo();

        let entries: [string, TypeSignature][] = [];

        try {
            this.setRecover(this.scanMatchingParens(SYM_lbrace, SYM_rbrace));

            let pnames = new Set<string>();
            entries = this.parseListOf<[string, TypeSignature]>("record type", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                this.ensureToken(TokenStrings.Identifier, "record type entry property name");

                const name = this.consumeTokenAndGetValue();
                if(pnames.has(name)) {
                    this.raiseError(this.getCurrentLine(), `Duplicate property name "${name}" in record declaration`);
                }
                pnames.add(name);

                this.ensureAndConsumeToken(SYM_colon, "record type property type");
                const rtype = this.parseTypeSignature();

                return [name, rtype];
            });

            this.clearRecover();
            return new RecordTypeSignature(sinfo, entries);
        }
        catch (ex) {
            this.processRecover();
            return new ParseErrorTypeSignature(sinfo);
        }
    }

    private parsePCodeType(): TypeSignature {
        const sinfo = this.getCurrentSrcInfo();

        let recursive: "yes" | "no" | "cond" = "no";
        if (this.testAndConsumeTokenIf(KW_recursive_q)) {
            recursive = "cond";
        }
        if (this.testAndConsumeTokenIf(KW_recursive)) {
            recursive = "yes";
        }

        const ispred = this.testToken(KW_pred);
        this.consumeToken();

        try {
            this.setRecover(this.scanMatchingParens(SYM_lparen, SYM_rparen));

            const params = this.parseListOf<FunctionParameter>("lambda function parameters", SYM_lparen, SYM_rparen, SYM_coma, () => {
                return new FunctionParameter("_", this.parseTypeSignature(), undefined);
            });

            this.ensureAndConsumeToken(SYM_arrow, "lambda type reference");
            const resultInfo = this.parseTypeSignature();

            this.clearRecover();
            return new FunctionTypeSignature(sinfo, false, recursive, params, resultInfo, ispred);
        }
        catch (ex) {
            this.processRecover();
            return new ParseErrorTypeSignature(sinfo);
        }
    }

    private static orOfTypeSignatures(sinfo: SourceInfo, t1: TypeSignature, t2: TypeSignature): TypeSignature {
        const types = [
            ...((t1 instanceof UnionTypeSignature) ? t1.types : [t1]),
            ...((t2 instanceof UnionTypeSignature) ? t2.types : [t2]),
        ];

        return new UnionTypeSignature(sinfo, types);
    }

    private andOfTypeSignatures(sinfo: SourceInfo, t1: TypeSignature, t2: TypeSignature): TypeSignature {
        const types = [
            ...((t1 instanceof AndTypeSignature) ? t1.types : [t1]),
            ...((t2 instanceof AndTypeSignature) ? t2.types : [t2]),
        ];

        return new AndTypeSignature(sinfo, types);
    }

    ////
    //Expression parsing
    private parseITest(): ITest {
        const isnot = this.testAndConsumeTokenIf(SYM_bang);

        if(this.testToken(SYM_le)) {
            return this.parseITypeTest(isnot);
        }
        else if(this.testToken(SYM_lbrack)) {
            return this.parseILiteralTest(isnot);
        }
        else {
            if(this.testToken(KW_none)) {
                this.consumeToken();
                return new ITestNone(isnot);
            }
            else if(this.testToken(KW_some)) {
                this.consumeToken();
                return new ITestSome(isnot);
            }
            else if(this.testToken(KW_nothing)) {
                this.consumeToken();
                return new ITestNothing(isnot);
            }
            else if(this.testToken(KW_something)) {
                this.consumeToken();
                return new ITestSomething(isnot);
            }
            else if(this.testToken(KW_ok)) {
                this.consumeToken();
                return new ITestOk(isnot);
            }
            else if(this.testToken(KW_err)) {
                this.consumeToken();
                return new ITestErr(isnot);
            }
            else {
                this.raiseError(this.getCurrentLine(), `Unknown option for ITest -- ${this.peekTokenData()}`);
                return (undefined as any) as ITest;
            }
        }
    }

    private parseITypeTest(isnot: boolean): ITest {
        this.consumeToken();
        const ttype = this.parseTypeSignature();
        this.ensureAndConsumeToken(SYM_ge, "itype test");

        return new ITestType(isnot, ttype);
    }

    private parseILiteralTest(isnot: boolean): ITest {
        this.consumeToken();
        const literal = this.parseLiteralExpression("itype test");
        this.ensureAndConsumeToken(SYM_rbrack, "itype test");

        return new ITestLiteral(isnot, literal);
    }

    private parseArguments(lparen: string, rparen: string): Expression[] {
        let args: Expression[] = [];

        try {
            this.setRecover(this.scanMatchingParens(lparen, rparen));

            this.ensureAndConsumeToken(lparen, "argument list");
            while (!this.testAndConsumeTokenIf(rparen)) {
                const exp = this.parseExpression();
                args.push(exp);

                if (this.testAndConsumeTokenIf(SYM_coma)) {
                    this.ensureNotToken(rparen, "argument list after \",\"");
                }
                else {
                    this.ensureToken(rparen, "argument list -- maybe missing a \",\"");
                }
            }

            this.clearRecover();
            return args;
        }
        catch (ex) {
            this.processRecover();
            return [];
        }
    }

    private parseArgumentsNamed(lparen: string, rparen: string): {name: string, value: Expression}[] {
        let args: {name: string, value: Expression}[] = [];

        try {
            this.setRecover(this.scanMatchingParens(lparen, rparen));

            this.consumeToken();
            while (!this.testAndConsumeTokenIf(rparen)) {
                this.ensureToken(TokenStrings.Identifier, "name in argument list");

                const name = this.consumeTokenAndGetValue();
                this.ensureAndConsumeToken(SYM_eq, "named argument list");

                const exp = this.parseExpression();
                args.push({name: name, value: exp});

                if (this.testAndConsumeTokenIf(SYM_coma)) {
                    this.ensureNotToken(rparen, "argument list after \",\"");
                }
                else {
                    this.ensureToken(rparen, "argument list -- maybe missing a \",\"");
                }
            }

            this.clearRecover();
            return args;
        }
        catch (ex) {
            this.processRecover();
            return [];
        }
    }

    private parseEnvUpdateArguments(lparen: string, rparen: string): {name: string, value: [TypeSignature, Expression] | undefined}[] {
        let args: {name: string, value: [TypeSignature, Expression] | undefined}[] = [];

        try {
            this.setRecover(this.scanMatchingParens(lparen, rparen));

            this.consumeToken();
            while (!this.testAndConsumeTokenIf(rparen)) {
                this.ensureToken(TokenStrings.Identifier, "name in environment argument list");
                const name = this.consumeTokenAndGetValue();

                if(this.testToken(SYM_eq)) {
                    this.consumeToken();

                    this.ensureToken(TokenStrings.Identifier, "null value in environment argument list");
                    const vv = this.consumeTokenAndGetValue();
                    if(vv !== "_") {
                        this.raiseError(this.getCurrentLine(), "expected _");
                    }

                    args.push({ name: name, value: undefined });
                }
                else {
                    this.ensureAndConsumeToken(SYM_colon, "type in environment argument list");
                    const ttype = this.parseTypeSignature();

                    this.ensureAndConsumeToken(SYM_eq, "value in environment argument list")
                    const exp = this.parseExpression();

                    args.push({ name: name, value: [ttype, exp] });
                }

                if (this.testAndConsumeTokenIf(SYM_coma)) {
                    this.ensureNotToken(rparen, "argument list after \",\"");
                }
                else {
                    this.ensureToken(rparen, "argument list -- maybe missing a \",\"");
                }
            }

            this.clearRecover();
            return args;
        }
        catch (ex) {
            this.processRecover();
            return [];
        }
    }

    private parseTemplateArguments(): TypeSignature[] {
        try {
            this.setRecover(this.scanMatchingParens(SYM_le, SYM_ge));
            let targs: TypeSignature[] = [];

            this.consumeToken();
            while (!this.testAndConsumeTokenIf(SYM_ge)) {
                targs.push(this.parseTypeSignature());

                if (this.testAndConsumeTokenIf(SYM_coma)) {
                    this.ensureNotToken(SYM_ge, "template argument list after \",\"");
                }
                else {
                    this.ensureToken(SYM_ge, "template argument list -- maybe missing a \",\"");
                }
            }

            this.clearRecover();
            return targs;
        }
        catch (ex) {
            this.processRecover();
            return [];
        }
    }

    private parseRecursiveAnnotation(): RecursiveAnnotation {
        let recursive: "yes" | "no" | "cond" = "no";
        
        this.consumeToken();
        if (!this.testToken(KW_recursive) && !this.testToken(KW_recursive_q)) {
            this.raiseError(this.getCurrentLine(), "Expected recursive annotation");
        }

        recursive = this.testToken("recursive") ? "yes" : "cond";
        this.consumeToken();

        this.ensureAndConsumeToken(SYM_rbrack, "recursive annotation");
         
        return recursive;
    }

    private parseConstructorPrimary(otype: TypeSignature): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const args = this.parseArguments(SYM_lbrace, SYM_rbrace);

        return new ConstructorPrimaryExpression(sinfo, otype, args);
    }
    
    private parsePCodeTerm(): Expression {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        let isrecursive: "yes" | "no" | "cond" = "no";
        if(this.testAndConsumeTokenIf(KW_recursive)) {
            isrecursive = "yes";
        }
        else if(this.testAndConsumeTokenIf(KW_recursive_q)) {
            isrecursive = "cond";
        }
        else {
            isrecursive = "no";
        }

        const ispred = this.testToken(KW_pred);
        this.consumeToken();

        const sig = this.parseInvokableCommon(ispred ? InvokableKind.PCodePred : InvokableKind.PCodeFn, false, [], isrecursive, [], [...this.m_penv.getCurrentFunctionScope().getBoundTemplates()], undefined, false);
        const someAuto = sig.params.some((param) => param.type instanceof AutoTypeSignature) || (sig.resultType instanceof AutoTypeSignature);
        const allAuto = sig.params.every((param) => param.type instanceof AutoTypeSignature) && (sig.resultType instanceof AutoTypeSignature);
        if (someAuto && !allAuto) {
            this.raiseError(line, "Cannot have mixed of auto propagated and explicit types on lambda arguments/return");
        }

        sig.captureVarSet.forEach((v) => {
            this.m_penv.useLocalVar(v);
        });

        sig.captureTemplateSet.forEach((t) => {
            this.m_penv.useTemplateType(t);
        });

        return new ConstructorPCodeExpression(sinfo, allAuto, sig);
    }

    private parseFollowTypeTag(incontext: string, hassep: boolean): TypeSignature {
        const sinfo = this.getCurrentSrcInfo();

        if(hassep) {
            this.ensureAndConsumeToken(TokenStrings.FollowTypeSep, incontext);
        }

        if (this.testToken(TokenStrings.Template)) {
            return this.parseTemplateTypeReference();
        }
        else {
            const line = this.getCurrentLine();

            let ns: string | undefined = undefined;
            if (this.testToken(TokenStrings.Namespace)) {
                ns = this.consumeTokenAndGetValue();
                this.ensureAndConsumeToken(SYM_coloncolon, "namespace scope resolve");
            }

            const tname = this.consumeTokenAndGetValue();
            const ons = ns;
            ns = this.m_penv.tryResolveNamespace(ns, tname);
            if (ns === undefined) {
                this.raiseError(line, `Could not resolve namespace/type${ns !== undefined ? (" " + ons + SYM_coloncolon + tname) : tname}`);
            }

            return new NominalTypeSignature(sinfo, ns as string, [tname], []);
        }
    }

    private parseLiteralExpression(incontext: string | undefined): LiteralExpressionValue {
        const sinfo = this.getCurrentSrcInfo();

        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(), this.m_penv.getCurrentFunctionScope().getBoundTemplates(), this.m_penv.SpecialAutoSignature, true));
            const exp = this.parsePrefixExpression();
            const captured = this.m_penv.getCurrentFunctionScope().getCaptureVars();

            if(captured.size !== 0) {
                this.raiseError(sinfo.line, "Cannot reference local variables in literal expression");
            }

            this.m_penv.popFunctionScope();

            return new LiteralExpressionValue(exp);
        }
        catch (ex) {
            this.m_penv.popFunctionScope();
            throw ex;
        }
    }

    private parseConstExpression(capturesok: boolean): ConstantExpressionValue {
        const sinfo = this.getCurrentSrcInfo();

        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(), new Set<string>(), this.m_penv.SpecialAutoSignature, true));
            const exp = this.parseMapEntryConstructorExpression();
            const captured = this.m_penv.getCurrentFunctionScope().getCaptureVars();

            if(!capturesok && captured.size !== 0) {
                this.raiseError(sinfo.line, "Cannot reference local variables in constant expression");
            }

            this.m_penv.popFunctionScope();

            return new ConstantExpressionValue(exp, captured);
        }
        catch (ex) {
            this.m_penv.popFunctionScope();
            throw ex;
        }
    }

    private checkTypeScopeBasedExpressionFollowsParens(): boolean {
        const lpos = this.scanMatchingParens(SYM_lparen, SYM_rparen);
        const ptok = this.peekToken(lpos - this.m_cpos);

        return ptok === "::";
    }

    private parsePrimaryExpression(): [Expression, boolean] {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        const tk = this.peekToken();
        if (tk === KW_none) {
            this.consumeToken();
            return [new LiteralNoneExpression(sinfo), false];
        }
        else if (tk === KW_nothing) {
            this.consumeToken();
            return [new LiteralNothingExpression(sinfo), false];
        }
        else if (tk === KW_true || tk === KW_false) {
            this.consumeToken();
            return [new LiteralBoolExpression(sinfo, tk === KW_true), false];
        }
        else if (tk === TokenStrings.Int) {
            const istr = this.consumeTokenAndGetValue();
            return [new LiteralIntegralExpression(sinfo, istr, this.m_penv.SpecialIntSignature), false];
        }
        else if (tk === TokenStrings.Nat) {
            const istr = this.consumeTokenAndGetValue();
            return [new LiteralIntegralExpression(sinfo, istr, this.m_penv.SpecialNatSignature), false];
        }
        else if (tk === TokenStrings.Float) {
            const fstr = this.consumeTokenAndGetValue();
            return [new LiteralFloatPointExpression(sinfo, fstr, this.m_penv.SpecialFloatSignature), false];
        }
        else if (tk === TokenStrings.Decimal) {
            const fstr = this.consumeTokenAndGetValue();
            return [new LiteralFloatPointExpression(sinfo, fstr, this.m_penv.SpecialDecimalSignature), false];
        }
        else if (tk === TokenStrings.BigInt) {
            const istr = this.consumeTokenAndGetValue();
            return [new LiteralIntegralExpression(sinfo, istr, this.m_penv.SpecialBigIntSignature), false];
        }
        else if (tk === TokenStrings.BigNat) {
            const istr = this.consumeTokenAndGetValue();
            return [new LiteralIntegralExpression(sinfo, istr, this.m_penv.SpecialBigNatSignature), false];
        }
        else if (tk === TokenStrings.Rational) {
            const istr = this.consumeTokenAndGetValue();
            return [new LiteralRationalExpression(sinfo, istr, this.m_penv.SpecialRationalSignature), false];
        }
        else if (tk === TokenStrings.String) {
            const sstr = this.consumeTokenAndGetValue(); //keep in original format

            if (this.testToken(TokenStrings.FollowTypeSep)) {
                const ttype = this.parseFollowTypeTag("typed primitive", true);

                const asstr = "\"" + sstr.slice(1, sstr.length - 1) + "\"";
                return [new LiteralTypedPrimitiveConstructorExpression(sinfo, new LiteralStringExpression(sinfo, asstr), ttype), false];
            }
            else if(this.testToken(TokenStrings.Namespace) || this.testToken(TokenStrings.Type)) {
                const ttype = this.parseNominalType();
                return [new LiteralTypedStringExpression(sinfo, sstr, ttype), false];
            }
            else {
                return [new LiteralStringExpression(sinfo, sstr), false];
            }
        }
        else if (tk === TokenStrings.ASCIIString) {
            const sstr = this.consumeTokenAndGetValue(); //keep in original format
            if (this.testToken(TokenStrings.FollowTypeSep)) {
                const ttype = this.parseFollowTypeTag("typed primitive", true);

                const asstr = "\"" + sstr.slice("ascii{".length + 1, sstr.length - (1 + "}".length)) + "\"";
                return [new LiteralTypedPrimitiveConstructorExpression(sinfo, new LiteralASCIIStringExpression(sinfo, asstr), ttype), false];
            }
            else if(this.testToken(TokenStrings.Namespace) || this.testToken(TokenStrings.Type)) {
                const ttype = this.parseNominalType();
                return [new LiteralASCIITypedStringExpression(sinfo, sstr, ttype), false];
            }
            else {
                return [new LiteralASCIIStringExpression(sinfo, sstr), false];
            }
        }
        else if (tk === TokenStrings.TemplateString) {
            const sstr = this.consumeTokenAndGetValue(); //keep in original format
            return [new LiteralTemplateStringExpression(sinfo, sstr), false];
        }
        else if (tk === TokenStrings.TemplateASCIIString) {
            const sstr = this.consumeTokenAndGetValue(); //keep in original format
            return [new LiteralASCIITemplateStringExpression(sinfo, sstr), false];
        }
        else if (tk === TokenStrings.Regex) {
            const restr = this.consumeTokenAndGetValue(); //keep in escaped format
            const re = BSQRegex.parse(this.m_penv.getCurrentNamespace(), undefined, restr);
            if(typeof(re) === "string") {
                this.raiseError(line, re);
            }

            this.m_penv.assembly.addLiteralRegex(re as BSQRegex);
            return [new LiteralRegexExpression(sinfo, re as BSQRegex), false];
        }
        else if (tk === KW_ok || tk === KW_err || tk === KW_something || tk === KW_result) {
            this.consumeToken();
            this.ensureAndConsumeToken("(", tk + " constructor");
            let arg = new LiteralNoneExpression(this.getCurrentSrcInfo());
            if(tk === KW_ok || tk === KW_something) {
                arg = this.parseExpression();
            }
            else {
                if(!this.testToken(")")) {
                    arg = this.parseExpression();
                }
            }
            this.ensureAndConsumeToken(")", tk + "constructor -- missing closing \")\"?");

            return [new SpecialConstructorExpression(sinfo, tk, arg), false];
        }
        else if (tk === TokenStrings.BSQON) {
            const bbvalue = this.consumeTokenAndGetValue();
            let oftype: TypeSignature | undefined = undefined;
            if(this.testAndConsumeTokenIf(SYM_at)) {
                this.ensureAndConsumeToken(SYM_le, "BSQON literal type annotation");
                oftype = this.parseTypeSignature();
                this.ensureAndConsumeToken(SYM_ge, "BSQON literal type annotation");
            }

            return [new BSQONLiteralExpression(sinfo, bbvalue, oftype), false];
        }
        else if (tk === KW_env) {
            this.ensureTaskOpOk();
            this.consumeToken();

            let opttype = this.m_penv.SpecialStringSignature;
            if(this.testAndConsumeTokenIf(SYM_le)) {
                opttype = this.parseTypeSignature();
                this.ensureAndConsumeToken(SYM_ge, "");
            }

            const isNoneMode = this.testAndConsumeTokenIf(SYM_question);

            this.ensureAndConsumeToken(SYM_lbrack, "environment access");
            this.ensureToken(TokenStrings.String, "environment access");
            const keyname = this.consumeTokenAndGetValue();
            this.ensureToken(SYM_rbrack, "environment access");

            return [new AccessEnvValueExpression(sinfo, keyname, opttype, isNoneMode), false];
        }
        else if (tk === TokenStrings.Identifier && this.peekTokenData() === "self") {
            this.ensureTaskOpOk();
            this.consumeToken();

            this.ensureAndConsumeToken(SYM_dot, "self field access");
            this.ensureNotToken(TokenStrings.Identifier, "self field access");
            const sfname = this.consumeTokenAndGetValue();

            if (!this.testToken(SYM_le) && !this.testToken(SYM_lparen)) {
                if(sfname !== "cntl") {
                    return [new TaskSelfFieldExpression(sinfo, sfname), false];
                }
                else {
                    return [new PostfixOp(sinfo, new TaskSelfControlExpression(sinfo), [new PostfixAccessFromName(sinfo, sfname)]), false];
                }
            }
            else {
                const targs = this.testToken(SYM_le) ? this.parseTemplateArguments() : [];
                const args = this.parseArguments(SYM_lparen, SYM_rparen);

                return [new TaskSelfActionExpression(sinfo, sfname, targs, args, false), false];
            }
        }
        else if (tk === KW_ref && this.peekToken(1) === TokenStrings.Identifier && this.peekTokenData(1) === "self") {
            this.ensureTaskOpOk();
            this.consumeToken();
            this.consumeToken();

            this.ensureAndConsumeToken(SYM_dot, "self field access");
            this.ensureNotToken(TokenStrings.Identifier, "self field access");
            const sfname = this.consumeTokenAndGetValue();

            const targs = this.testToken(SYM_le) ? this.parseTemplateArguments() : [];
            const args = this.parseArguments(SYM_lparen, SYM_rparen);

            return [new TaskSelfActionExpression(sinfo, sfname, targs, args, true), false];
        }
        else if (tk === TokenStrings.Identifier || this.testFollows(KW_ref, TokenStrings.Identifier)) {
            const refstr = this.testAndConsumeTokenIf(KW_ref);
            let namestr = this.consumeTokenAndGetValue();

            const isvar = this.m_penv.isVarDefinedInAnyScope(namestr) || namestr === "this" || namestr.startsWith("$");
            if (isvar) {
                const istr = this.m_penv.useLocalVar(namestr);

                if(refstr && (this.testToken(SYM_lbrack) || this.testToken(SYM_lparen))) {
                    this.raiseError(line, "cannot use ref on lambda invoke");
                }

                if (this.testToken(SYM_lbrack)) {
                    const rec = this.parseRecursiveAnnotation();
                    const args = this.parseArguments(SYM_lparen, SYM_rparen);

                    return [new PCodeInvokeExpression(sinfo, istr, rec, args), false];
                }
                else if (this.testToken(SYM_lparen)) {
                    const args = this.parseArguments(SYM_lparen, SYM_rparen);

                    return [new PCodeInvokeExpression(sinfo, istr, "no", args), false];
                }
                else {
                    return [new AccessVariableExpression(sinfo, istr), refstr];
                }
            }
            else {
                const tryfunctionns = this.m_penv.tryResolveNamespace(undefined, namestr);
                if (tryfunctionns === undefined) {
                    this.raiseError(line, `Cannot resolve name "${namestr}"`);
                }

                if(refstr) {
                    this.raiseError(line, "cannot use ref on namespace invoke");
                }

                const targs = this.testToken(SYM_le) ? this.parseTemplateArguments() : [];
                const rec = this.testToken(SYM_lbrack) ? this.parseRecursiveAnnotation() : "no";
                const args = this.parseArguments(SYM_lparen, SYM_rparen);

                return [new CallNamespaceFunctionOrOperatorExpression(sinfo, tryfunctionns as string, namestr, targs, rec, args), false];
            }
        }
        else if (tk === KW_fn || this.testFollows(KW_recursive, KW_fn) || this.testFollows(KW_recursive_q, KW_fn) || tk === KW_pred || this.testFollows(KW_recursive, KW_pred) || this.testFollows(KW_recursive_q, KW_pred)) {
            return [this.parsePCodeTerm(), false];
        }
        else if (tk === SYM_lparen && !this.checkTypeScopeBasedExpressionFollowsParens()) {
            try {
                this.setRecover(this.scanMatchingParens(SYM_lparen, SYM_rparen));

                this.consumeToken();
                const exp = this.parseExpression();
                this.ensureAndConsumeToken(SYM_rparen, "(Exp _<- Missing \")\"?");

                this.clearRecover();
                return [exp, false];
            }
            catch (ex) {
                this.processRecover();
                return [new InvalidExpression(sinfo), false];
            }
        }
        else if (this.testToken(SYM_lbrack)) {
            const args = this.parseArguments(SYM_lbrack, SYM_rbrack);
            return [new ConstructorTupleExpression(sinfo, args), false];
        }
        else if  (this.testToken(SYM_lbrace)) {
            const args = this.parseArgumentsNamed(SYM_lbrace, SYM_rbrace).sort((a, b) => ((a.name !== b.name) ? (a.name < b.name ? -1 : 1) : 0));
            return [new ConstructorRecordExpression(sinfo, args.map((nn) => {
                return {property: nn.name, value: nn.value};
            })), false];
        }
        else if (this.testToken(SYM_land) || this.testToken(SYM_lor)) {
            const op = this.consumeTokenAndGetValue() as "/\\" | "\\/";
            const args = this.parseArguments(SYM_lparen, SYM_rparen);
            if(op === SYM_land) {
                return [new LogicActionAndExpression(sinfo, args), false];
            }
            else {
                return [new LogicActionOrExpression(sinfo, args), false];
            }
        }
        else if (this.testFollows(TokenStrings.Namespace, SYM_coloncolon, TokenStrings.Identifier)) {
            //it is a namespace access of some type
            let ns: string | undefined = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            if(ns === "Task" && (name === "getTaskID" || name === "isCanceled")) {
                this.ensureTaskOpOk();

                if(name === "getTaskID") {
                    return [new TaskGetIDExpression(sinfo), false];
                }
                else {
                    return [new TaskCancelRequestedExpression(sinfo), false];
                }
            }
            else {
                ns = this.m_penv.tryResolveNamespace(ns, name);
                if (ns === undefined) {
                    ns = "[Unresolved Namespace]";
                }

                if (!this.testToken(SYM_le) && !this.testToken(SYM_lbrack) && !this.testToken(SYM_lparen)) {
                    //just a constant access
                    return [new AccessNamespaceConstantExpression(sinfo, ns, name), false];
                }
                else {
                    const targs = this.testToken(SYM_le) ? this.parseTemplateArguments() : [];
                    const rec = this.testToken(SYM_lbrack) ? this.parseRecursiveAnnotation() : "no";
                    const args = this.parseArguments(SYM_lparen, SYM_rparen);

                    return [new CallNamespaceFunctionOrOperatorExpression(sinfo, ns, name, targs, rec, args), false];
                }
            }
        }
        else if (this.testFollows(TokenStrings.Namespace, SYM_hash, TokenStrings.Identifier)) {
            //it is a namespace access of some formatter info
            let ns: string | undefined = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            return [new AccessFormatInfoExpression(sinfo, ns, name), false];
        }
        else {
            if(this.testToken(TokenStrings.Numberino)) {
                this.raiseError(this.getCurrentLine(), `expected numeric specifier, [i, n, I, N, f, d, R], on literal but got naked ${this.peekTokenData()}`)
            }
            const ttype = this.parseTypeSignature();

            if (this.testFollows(SYM_coloncolon, TokenStrings.Identifier)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                if (!this.testToken(SYM_le) && !this.testToken(SYM_lbrack) && !this.testToken(SYM_lparen) && !this.testToken(SYM_lbrace)) {
                    //just a static access
                    return [new AccessStaticFieldExpression(sinfo, ttype, name), false];
                }
                else {
                    const targs = this.testToken(SYM_le) ? this.parseTemplateArguments() : [];
                    const rec = this.testToken(SYM_lbrack) ? this.parseRecursiveAnnotation() : "no";
                    const args = this.parseArguments(SYM_lparen, SYM_rparen);
                    return [new CallStaticFunctionExpression(sinfo, ttype, name, targs, rec, args), false];
                }
            }
            else if (this.testFollows(SYM_lbrace)) {
                return [this.parseConstructorPrimary(ttype), false];
            }
            else {
                //
                //TODO: maybe a better error here -- slice the string at the position...
                //
                this.raiseError(line, `Unknown token sequence in parsing expression -- ${tk}`);
                return [new InvalidExpression(sinfo), false];
            }
        }
    }
    
    private literalPrefixStackAndTypedConstructorHandler(ops: ("!" | "+" | "-")[]): [Expression, ("!" | "+" | "-")[], boolean] {
        const sinfo = this.getCurrentSrcInfo();

        let [exp, refpfx] = this.parsePrimaryExpression();
        if (this.testToken(TokenStrings.FollowTypeSep)) {
            const ttype = this.parseFollowTypeTag("typed primitive", true);

            const okexp = (exp instanceof LiteralBoolExpression) || (exp instanceof LiteralIntegralExpression) || (exp instanceof LiteralFloatPointExpression) ||
                (exp instanceof LiteralRationalExpression) || (exp instanceof LiteralStringExpression) || (exp instanceof LiteralASCIIStringExpression);
                //Typed strings handled in parse primary

            if(okexp) {
                return [new LiteralTypedPrimitiveConstructorExpression(sinfo, exp, ttype), ops, false];
            }
            else {
                this.raiseError(sinfo.line, `Only literal values can be used in typed initializers`);
                return [new InvalidExpression(sinfo), [], false];
            }
        }
        else {
            return [exp, ops, refpfx];
        }
    }

    private parseTupleIndex(): number {
        if(this.testToken(TokenStrings.Numberino)) {
            const niov = this.consumeTokenAndGetValue();
            return Number.parseInt(niov);
        }
        else if(this.testToken(TokenStrings.Int)) {
            const iv = this.consumeTokenAndGetValue();
            return Number.parseInt(iv.substr(0, iv.length - 1));
        }
        else if(this.testToken(TokenStrings.Nat)) {
            const nv = this.consumeTokenAndGetValue();
            return Number.parseInt(nv.substr(0, nv.length - 1));
        }
        else {
            this.raiseError(this.getCurrentSrcInfo().line, "Expected an Int or a Nat literal");
            return -1;
        }
    }

    private parsePostfixExpression(pfxops: ("!" | "+" | "-")[]): [Expression, ("!" | "+" | "-")[]] {
        const rootinfo = this.getCurrentSrcInfo();

        let [rootexp, remainingops, refpfx] = this.literalPrefixStackAndTypedConstructorHandler(pfxops);

        let ops: PostfixOperation[] = [];
        while (true) {
            const sinfo = this.getCurrentSrcInfo();

            if(this.testToken(SYM_question)) {
                this.consumeToken();

                const ttest = this.parseITest();
                ops.push(new PostfixIsTest(sinfo, ttest));
            }
            else if(this.testToken(SYM_at)) {
                this.consumeToken();
                
                const ttest = this.parseITest();
                ops.push(new PostfixAsConvert(sinfo, ttest));
            }
            else if (this.testToken(SYM_dot)) {
                this.consumeToken();

                if (this.testToken(TokenStrings.Numberino)) {
                    if(refpfx) {
                        this.raiseError(sinfo.line, "Cannot use \"ref on numeric index op\"");
                    }

                    const index = this.parseTupleIndex();
                    ops.push(new PostfixAccessFromIndex(sinfo, index));
                }
                else {
                    let specificResolve: TypeSignature | undefined = undefined;
                    if (this.testToken(TokenStrings.Namespace) || this.testToken(TokenStrings.Type) || this.testToken(TokenStrings.Template)) {
                        specificResolve = this.parseTypeSignature();
                        this.ensureAndConsumeToken(SYM_coloncolon, "type resolution specfier for postfix \".\" access");
                    }

                    this.ensureToken(TokenStrings.Identifier, "postfix \".\" access");
                    const name = this.consumeTokenAndGetValue();

                    if (!(this.testToken(SYM_le) || this.testToken(SYM_lbrack) || this.testToken(SYM_lparen))) {
                        if(refpfx) {
                            this.raiseError(sinfo.line, "Cannot use \"ref on field/property index op\"");
                        }

                        if (specificResolve !== undefined) {
                            this.raiseError(this.getCurrentLine(), "Encountered named access but given type resolver (only valid on method calls)");
                        }

                        ops.push(new PostfixAccessFromName(sinfo, name));
                    }
                    else {
                        if (this.testToken(SYM_le)) {
                            const nextnonlptokenidx = this.peekToken(1) === SYM_lparen ? this.scanLParens(this.m_cpos + 1) : this.m_cpos + 1;
                            if(nextnonlptokenidx === this.m_epos) {
                                this.raiseError(this.getCurrentLine(), "Truncated statement?");
                            }

                            const followtoken = this.m_tokens[nextnonlptokenidx].kind;
                            if (followtoken === TokenStrings.Namespace || followtoken === TokenStrings.Type || followtoken === TokenStrings.Template || followtoken ===  SYM_lbrack || followtoken === SYM_lbrace) {
                                const terms = this.parseTemplateArguments();
                                const rec = this.testToken(SYM_lbrack) ? this.parseRecursiveAnnotation() : "no";

                                const args = this.parseArguments(SYM_lparen, SYM_rparen);
                                ops.push(new PostfixInvoke(sinfo, specificResolve, refpfx, name, terms, rec, args));
                            }
                            else {
                                if(refpfx) {
                                    this.raiseError(sinfo.line, "Cannot use \"ref on field/property index op\"");
                                }

                                if (specificResolve !== undefined) {
                                    this.raiseError(this.getCurrentLine(), "Encountered named access but given type resolver (only valid on method calls)");
                                }

                                ops.push(new PostfixAccessFromName(sinfo, name));
                            }
                        }
                        else {
                            const rec = this.testToken(SYM_lbrack) ? this.parseRecursiveAnnotation() : "no";

                            const args = this.parseArguments(SYM_lparen, SYM_rparen);
                            ops.push(new PostfixInvoke(sinfo, specificResolve, refpfx, name, [], rec, args));
                        }
                    }
                }

                refpfx = false;
            }
            else {
                if (ops.length === 0) {
                    return [rootexp, remainingops];
                }
                else {
                    return [new PostfixOp(rootinfo, rootexp, ops), remainingops];
                }
            }
        }
    }

    private parseStatementExpression(ops: ("!" | "+" | "-")[]): [Expression, ("!" | "+" | "-")[]] {
        if (this.testToken(KW_if)) {
            return [this.parseIfExpression(), ops];
        }
        else if (this.testToken(KW_switch)) {
            return [this.parseSwitchExpression(), ops];
        }
        else if (this.testToken(KW_match)) {
            return [this.parseMatchExpression(), ops];
        }
        else {
            return this.parsePostfixExpression(ops);
        }
    }

    private prefixStackApplicationHandler(sinfo: SourceInfo, ops: ("!" | "+" | "-")[]): Expression {
        let [exp, remainingops] = this.parseStatementExpression(ops);
        
        for (let i = 0; i < remainingops.length; ++i) {
            const op = remainingops[i];

            if (op === SYM_bang) {
                exp = new PrefixNotOp(sinfo, exp);
            }
            else if (op === SYM_minus) {
                exp = new PrefixNegateOp(sinfo, exp);
            }
            else {
                return exp;
            }
        }

        return exp;
    }

    private parsePrefixExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        let ops:  ("!" | "+" | "-")[] = [];
        while(this.testToken(SYM_bang) || this.testToken(SYM_plus) || this.testToken(SYM_minus)) {
            ops.push(this.consumeTokenAndGetValue() as "!" | "+" | "-");
        }

        return this.prefixStackApplicationHandler(sinfo, ops.reverse());
    }

    private isMultiplicativeFollow(): boolean {
        if(this.testToken(SYM_times) || this.testToken(SYM_div)) {
            return true;
        }
        else {
            return false;
        }
    }

    private parseMultiplicativeExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parsePrefixExpression();

        if(!this.isMultiplicativeFollow()) {
            return exp;
        }
        else {
            let aexp: Expression = exp;
            while (this.isMultiplicativeFollow()) {
                const op = this.consumeTokenAndGetValue();

                const lhs = aexp;
                const rhs = this.parsePrefixExpression();
                if(op === SYM_times) {
                    aexp = new BinMultExpression(sinfo, lhs, rhs);
                }
                else {
                    aexp = new BinDivExpression(sinfo, lhs, rhs);
                }
            }

            return aexp;
        }
    }

    private isAdditiveFollow(): boolean {
        if(this.testToken(SYM_plus) || this.testToken(SYM_minus)) {
            return true;
        }
        else {
            return false;
        }
    }

    private parseAdditiveExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseMultiplicativeExpression();

        if(!this.isAdditiveFollow()) {
            return exp;
        }
        else {
            let aexp: Expression = exp;
            while (this.isAdditiveFollow()) {
                const op = this.consumeTokenAndGetValue();
                    
                const lhs = aexp;
                const rhs = this.parseMultiplicativeExpression();
                if(op === SYM_plus) {
                    aexp = new BinAddExpression(sinfo, lhs, rhs);
                }
                else {
                    aexp = new BinSubExpression(sinfo, lhs, rhs);
                }
            }

            return aexp;
        }
    }

    private parseRelationalExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseAdditiveExpression();

        if (this.testAndConsumeTokenIf(SYM_eqeqeq)) {
            return new BinKeyEqExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_bangeqeq)) {
            return new BinKeyNeqExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_eqeq)) {
            return new NumericEqExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_bangeq)) {
            return new NumericNeqExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_le)) {
            return new NumericLessExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_leq)) {
            return new NumericLessEqExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_ge)) {
            return new NumericGreaterExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_geq)) {
            return new NumericGreaterEqExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else {
            return exp;
        }
    }

    private parseAndExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseRelationalExpression();

        if (this.testAndConsumeTokenIf(SYM_ampamp)) {
            return new BinLogicAndxpression(sinfo, exp, this.parseAndExpression());
        }
        else {
            return exp;
        }
    }

    private parseOrExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseAndExpression();

        if (this.testAndConsumeTokenIf(SYM_barbar)) {
            return new BinLogicOrExpression(sinfo, exp, this.parseOrExpression());
        }
        else {
            return exp;
        }
    }

    private parseImpliesExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseOrExpression();

        if (this.testAndConsumeTokenIf(SYM_implies)) {
            return new BinLogicImpliesExpression(sinfo, exp, this.parseImpliesExpression());
        }
        else {
            return exp;
        }
    }

    private parseMapEntryConstructorExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        const lexp = this.parseImpliesExpression();   
        if(this.testAndConsumeTokenIf("=>")) {
            const rexp = this.parseImpliesExpression();
        
            return new MapEntryConstructorExpression(sinfo, lexp, rexp);
        }
        else {
            return lexp;
        }
    }

    private parseIfTest(bindername: string): IfTest {
        const tk = this.peekToken();
        
        if(tk !== SYM_lparen) {
            const itest = this.parseITest();
            
            this.ensureAndConsumeToken(SYM_lparen, "if test");
            const exp = this.parseExpression();
            this.ensureAndConsumeToken(SYM_rparen, "if test");

            return new IfTest(exp, itest);
        }
        else {
            this.ensureAndConsumeToken(SYM_lparen, "if test");
            const exp = this.parseExpression();
            this.ensureAndConsumeToken(SYM_rparen, "if test");

            return new IfTest(exp,  undefined);
        }
    }

    private parseExpressionWithBinder(): [boolean, Expression] {
        try {
            this.m_penv.getCurrentFunctionScope().pushLocalScope();
            this.m_penv.getCurrentFunctionScope().defineLocalVar("$", `$_$_${this.m_penv.getBinderExtension("$")}`, true);

            const ee = this.parseExpression();
            const isbind = this.m_penv.getCurrentFunctionScope().getUsedImplicitBinder();

            return [isbind, ee];
        }
        finally {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
        }
    }

    private parseIfExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const bindername = `$_$_${this.m_penv.getBinderExtension("$")}`;

        let conds: {cond: IfTest, value: Expression, binderinfo: string | undefined}[] = [];

        this.consumeToken();
        const iftest = this.parseIfTest(bindername);

        this.ensureAndConsumeToken(KW_then, "if expression value")
        const [ifbind, ifbody] = this.parseExpressionWithBinder();
        conds.push({ cond: iftest, value: ifbody, binderinfo: ifbind ? bindername : undefined });

        while (this.testAndConsumeTokenIf(KW_elif)) {
            const eliftest = this.parseIfTest(bindername);

            this.ensureAndConsumeToken(KW_then, "elif expression value")
            const [elifbind, elifbody] = this.parseExpressionWithBinder();

            conds.push({ cond: eliftest, value: elifbody, binderinfo: elifbind ? bindername : undefined});
        }

        this.ensureAndConsumeToken(KW_else, "if expression else value");
        const [elsebind, elsebody] = this.parseExpressionWithBinder();

        return new IfExpression(sinfo, conds, {value: elsebody, binderinfo: elsebind ? bindername : undefined});
    }

    private parseSwitchLiteralGuard(): LiteralExpressionValue | undefined {
        if (this.testToken(TokenStrings.Identifier)) {
            const tv = this.consumeTokenAndGetValue();
            if (tv !== "_") {
                this.raiseError(this.getCurrentSrcInfo().line, "Expected wildcard match");
            }

            return undefined;
        }
        else {
            return this.parseLiteralExpression("switch literal guard");
        }
    }

    private parseSwitchExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const bindername = `$_$_${this.m_penv.getBinderExtension("$")}`;

        this.ensureAndConsumeToken(KW_switch, "switch expression dispatch value");

        this.ensureAndConsumeToken(SYM_lparen, "switch expression dispatch value");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(SYM_rparen, "switch expression dispatch value");

        let entries: { condlit: LiteralExpressionValue | undefined, value: Expression, bindername: string | undefined }[] = [];
        this.ensureAndConsumeToken(SYM_lbrace, "switch expression options");

        const swlit = this.parseSwitchLiteralGuard();
        this.ensureAndConsumeToken(SYM_bigarrow, "switch expression entry");
        const [swbind, swvalue] = this.parseExpressionWithBinder();

        entries.push({ condlit: swlit, value: swvalue, bindername: swbind ? bindername : undefined });
        
        while (this.testToken(SYM_bar)) {
            this.consumeToken();

            const swlitx = this.parseSwitchLiteralGuard();
            this.ensureAndConsumeToken(SYM_bigarrow, "switch expression entry");
            const [swbindx, swvaluex] = this.parseExpressionWithBinder();

            entries.push({ condlit: swlitx, value: swvaluex, bindername: swbindx ? bindername : undefined });
        }
        this.ensureAndConsumeToken(SYM_rbrace, "switch expression options");

        return new SwitchExpression(sinfo, mexp, entries);
    }

    private parseMatchTypeGuard(): TypeSignature | undefined {
        if (this.testToken(TokenStrings.Identifier)) {
            const tv = this.consumeTokenAndGetValue();
            if (tv !== "_") {
                this.raiseError(this.getCurrentSrcInfo().line, "Expected wildcard match");
            }

            return undefined;
        }
        else {
            return this.parseTypeSignature();
        }
    }

    private parseMatchExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const bindername = `$_$_${this.m_penv.getBinderExtension("$")}`;

        this.ensureAndConsumeToken(KW_match, "match expression dispatch value");

        this.ensureAndConsumeToken(SYM_lparen, "match expression dispatch value");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(SYM_rparen, "match expression dispatch value");
 
        let entries: { mtype: TypeSignature | undefined, value: Expression, bindername: string | undefined }[] = [];
        this.ensureAndConsumeToken(SYM_lbrace, "match expression options");

        const mtype = this.parseMatchTypeGuard();
        this.ensureAndConsumeToken(SYM_bigarrow, "match expression entry");
        const [mbind, mvalue] = this.parseExpressionWithBinder();

        entries.push({ mtype: mtype, value: mvalue, bindername: mbind ? bindername : undefined });
        while (this.testToken(SYM_bar)) {
            this.consumeToken();
            
            const mtypex = this.parseMatchTypeGuard();
            this.ensureAndConsumeToken(SYM_bigarrow, "match expression entry");
            const [mbindx, mvaluex] = this.parseExpressionWithBinder();


            entries.push({ mtype: mtypex, value: mvaluex, bindername: mbindx ? bindername : undefined });
        }
        this.ensureAndConsumeToken(SYM_rbrace, "match expression options");

        return new MatchExpression(sinfo, mexp, entries);
    }

    private parseExpression(): Expression {
        return this.parseMapEntryConstructorExpression();
    }

    private parseSCReturnTest(): ITest | Expression {
        const isnot = this.testToken(SYM_bang);

        if(this.testToken(SYM_lbrack) || this.testFollows(SYM_bang, SYM_lbrack)) {
            this.consumeTokenIf(SYM_bang);
            return this.parseITypeTest(isnot);
        }
        else if(this.testToken(SYM_le) || this.testFollows(SYM_bang, SYM_le)) {
            this.consumeTokenIf(SYM_bang);
            return this.parseILiteralTest(isnot);
        }
        else {
            if(this.testToken(KW_none) || this.testFollows(SYM_bang, KW_none)) {
                this.consumeTokenIf(SYM_bang);
                this.consumeToken();
                return new ITestNone(isnot);
            }
            else if(this.testToken(KW_some) || this.testFollows(SYM_bang, KW_some)) {
                this.consumeTokenIf(SYM_bang);
                this.consumeToken();
                return new ITestSome(isnot);
            }
            else if(this.testToken(KW_nothing) || this.testFollows(SYM_bang, KW_nothing)) {
                this.consumeTokenIf(SYM_bang);
                this.consumeToken();
                return new ITestNothing(isnot);
            }
            else if(this.testToken(KW_something) || this.testFollows(SYM_bang, KW_something)) {
                this.consumeTokenIf(SYM_bang);
                this.consumeToken();
                return new ITestSomething(isnot);
            }
            else if(this.testToken(KW_ok) || this.testFollows(SYM_bang, KW_ok)) {
                this.consumeTokenIf(SYM_bang);
                this.consumeToken();
                return new ITestOk(isnot);
            }
            else if(this.testAndConsumeTokenIf(KW_err) || this.testFollows(SYM_bang, KW_err)) {
                this.consumeTokenIf(SYM_bang);
                this.consumeToken();
                return new ITestErr(isnot);
            }
            else {
                return this.parseExpression();
            }
        }
    }

    private parseSCRefExpression(): [Expression, {sctest: ITest | Expression, scaction: Expression | undefined} | undefined] {
        const ee = this.parsePostfixExpression([])[0];
        if(this.testToken(SYM_questionquestion)) {
            this.consumeToken();
            const sctest = this.parseSCReturnTest();
            const scaction = this.testAndConsumeTokenIf(SYM_colon) ? this.parseExpression() : undefined;

            return [ee, {sctest: sctest, scaction: scaction}];
        }
        else {
            return [ee, undefined];
        }
    }

    private parseSCAssignExpression(): [Expression, {sctest: ITest | Expression, scaction: Expression | undefined, binderinfo: string | undefined} | undefined] {
        const ee = this.parseExpression();
        if(this.testToken(SYM_questionquestion)) {
            const bindername = `$_$_${this.m_penv.getBinderExtension("$")}`;

            this.consumeToken();
            const sctest = this.parseSCReturnTest();
            const scaction = this.testAndConsumeTokenIf(SYM_colon) ? this.parseExpressionWithBinder() : undefined;

            return [ee, {sctest: sctest, scaction: scaction !== undefined ? scaction[1] : undefined, binderinfo: (scaction !== undefined && scaction[0]) ? bindername : undefined}];
        }
        else {
            return [ee, undefined];
        }
    }

    ////
    //Statement parsing

    parseAssignmentVarInfo(sinfo: SourceInfo, vars: "let" | "var" | undefined): {name: string, vtype: TypeSignature} {
        this.ensureToken(TokenStrings.Identifier, "assignment statement");
        const name = this.consumeTokenAndGetValue();

        let itype = this.m_penv.SpecialAutoSignature;
        if (this.testAndConsumeTokenIf(":")) {
            itype = this.parseTypeSignature();
        }

        if (vars !== undefined) {
            return { name: name, vtype: itype };
        }
        else {
            if (!this.m_penv.getCurrentFunctionScope().isVarNameDefined(name)) {
                this.raiseError(sinfo.line, `Variable "${name}" is not defined in scope`);
            }

            if (!(itype instanceof AutoTypeSignature)) {
                this.raiseError(sinfo.line, `Cannot redeclare type of variable "${name}" on assignment`);
            }

            return { name: name, vtype: itype };
        }
    }

    private parseTaskRunStatement(sinfo: SourceInfo, isdefine: boolean, isconst: boolean, vv: {name: string, vtype: TypeSignature} | undefined): Statement {
        this.ensureTaskOpOk();
        
        //TODO: need to cleanup so that SC return and assign work with this as well 

        let allvvs: {name: string, vtype: TypeSignature}[] = [];
        if (vv !== undefined) {
            allvvs.push(vv);
            while (!this.testToken(SYM_eq)) {
                this.ensureAndConsumeToken(SYM_coma, "Expected , in task result assignment list");

                const assign = this.parseAssignmentVarInfo(this.getCurrentSrcInfo(), isconst ? KW_let : KW_var);
                const vvar = { name: assign.name, vtype: assign.vtype };

                if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(assign.name)) {
                    this.raiseError(this.getCurrentLine(), "Variable name is already defined");
                }
                this.m_penv.getCurrentFunctionScope().defineLocalVar(assign.name, assign.name, false);

                allvvs.push(vvar);
            }
        }

        this.consumeToken();
        this.ensureAndConsumeToken(SYM_coloncolon, "Task statement");
        this.ensureToken(TokenStrings.Identifier, "Task statement");

        const name = this.consumeTokenAndGetValue();

        if(name === "getTaskID" || name === "isCanceled") {
            this.ensureAndConsumeToken(SYM_lparen, `Task expression ${name}`);
            this.ensureAndConsumeToken(SYM_rparen, `Task expression ${name}`);
            this.ensureAndConsumeToken(SYM_semicolon, `Task expression ${name}`);

            if(name === "getTaskID") {
                if(vv === undefined) {
                    return new ReturnStatement(sinfo, new TaskGetIDExpression(sinfo));
                }
                else if(isdefine) {
                    return new VariableDeclarationStatement(sinfo, vv.name, isconst, vv.vtype, new TaskGetIDExpression(sinfo), undefined);
                }
                else {
                    return new VariableAssignmentStatement(sinfo, vv.name, new TaskGetIDExpression(sinfo), undefined);
                }
            }
            else {
                if(vv === undefined) {
                    return new ReturnStatement(sinfo, new TaskCancelRequestedExpression(sinfo))
                }
                else if(isdefine) {
                    return new VariableDeclarationStatement(sinfo, vv.name, isconst, vv.vtype, new TaskCancelRequestedExpression(sinfo), undefined);
                }
                else {
                    return new VariableAssignmentStatement(sinfo, vv.name, new TaskCancelRequestedExpression(sinfo), undefined);
                }
            }
        }
        else {
            let argpack: { argn: string, argv: Expression }[] = [];
            if (this.testToken(SYM_lbrace)) {
                this.parseListOf("Task Run arguments", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                    const argn = this.ensureAndConsumeToken(TokenStrings.Identifier, "Task Run argument name");
                    this.ensureAndConsumeToken("=", "Task run argument");
                    const argv = this.parseExpression();

                    return { argn: argn, argv: argv };
                });
            }

            const terms = this.parseTemplateArguments();
            const args = this.parseArguments(SYM_lparen, SYM_rparen);

            if (terms.length !== 0) {
                this.raiseError(sinfo.line, "Must supply at least 1 task to run");
            }

            this.ensureAndConsumeToken(SYM_semicolon, "assignment statement");

            if (name === "run") {
                if (terms.length !== allvvs.length) {
                    this.raiseError(sinfo.line, "Must have equal numbers of tasks and result assignments");
                }

                if (terms.length === 1) {
                    //x = Task::run<T>(args)
                    return new TaskRunStatement(sinfo, isdefine, isconst, allvvs[0], terms[0], argpack, args);
                }
                else {
                    //y, z = Task::run<T, U>(argv, ...)
                    return new TaskMultiStatement(sinfo, isdefine, isconst, allvvs, terms, argpack, args);
                }
            }
            else if (name === "dash") {
                if (terms.length === 1) {
                    this.raiseError(sinfo.line, "dashing to a result on a single task is redundant -- use \"run\" instead");
                }

                if (terms.length !== allvvs.length) {
                    this.raiseError(sinfo.line, "Must have equal numbers of tasks and result assignments");
                }

                //x, y, z = Task::dash<T, U>(argv, ...)
                return new TaskDashStatement(sinfo, isdefine, isconst, allvvs, terms, argpack, args);
            }
            else if (name === "all") {
                if (terms.length !== 1 || args.length !== 1) {
                    this.raiseError(sinfo.line, "Task::all runs same task on all args tuples in the list");
                }

                if (allvvs.length !== 1) {
                    this.raiseError(sinfo.line, "Task::all produces a single result List");
                }

                //x: List<V> = Task::all<T>(List<U>) <-- result list all done
                return new TaskAllStatement(sinfo, isdefine, isconst, allvvs[0], terms[0], argpack, args[0]);
            }
            else if (name === "race") {
                if (terms.length !== 1 || args.length !== 1) {
                    this.raiseError(sinfo.line, "Task::all runs same task on all args tuples in the list");
                }

                if (allvvs.length !== 1) {
                    this.raiseError(sinfo.line, "Task::all produces a single Result");
                }

                //x: Result<T, E> = Task::race<T>(List<U>) <-- result list all done
                return new TaskRaceStatement(sinfo, isdefine, isconst, allvvs[0], terms[0], argpack, args[0]);
            }
            else {
                this.raiseError(sinfo.line, "Unknown \"Task\" operation");
                return new InvalidStatement(sinfo);
            }
        }
    }

    private parseBlockStatement(inctx: string): ScopedBlockStatement | UnscopedBlockStatement {
        if(this.testToken(SYM_lbrace)) {
            return this.parseScopedBlockStatement();
        }
        else if(this.testToken(SYM_lbracebar)) {
            return this.parseUnscopedBlockStatement();
        }
        else {
            this.raiseError(this.getCurrentLine(), `expected a (un)scoped block for ${inctx} manipulation`);
            return new ScopedBlockStatement(this.getCurrentSrcInfo(), [new InvalidStatement(this.getCurrentSrcInfo())]);
        }
    }

    private parseLineStatement(): Statement {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        const tk = this.peekToken();
        if (tk === SYM_semicolon) {
            this.consumeToken();
            return new EmptyStatement(sinfo);
        }
        else if (tk === KW_let || tk === KW_var) {
            this.consumeToken();
            const isConst = tk === KW_let;

            const assign = this.parseAssignmentVarInfo(this.getCurrentSrcInfo(), isConst ? KW_let : KW_var);
            const vvar = { name: assign.name, vtype: assign.vtype };

            if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(assign.name)) {
                this.raiseError(line, "Variable name is already defined");
            }
            this.m_penv.getCurrentFunctionScope().defineLocalVar(assign.name, assign.name, false);

            const hasassign = this.testAndConsumeTokenIf(SYM_eq);
            const ismulti = this.testToken(SYM_coma);
            if(ismulti || (hasassign && this.testToken(TokenStrings.Namespace) && this.peekTokenData() === "Task")) {
                return this.parseTaskRunStatement(sinfo, true, tk === KW_let, vvar);
            }
            else {
                if(ismulti) {
                    this.raiseError(this.getCurrentLine(), "Multiple variable assignement not generally supported yet!");
                }

                let exp: Expression | undefined = undefined;
                let sccinfo: {sctest: ITest | Expression, scaction: Expression | undefined, binderinfo: string | undefined} | undefined = undefined;
                if (hasassign) {
                    [exp, sccinfo] = this.parseSCAssignExpression();
                }
                this.ensureAndConsumeToken(SYM_semicolon, "assignment statement");

                if ((exp === undefined && isConst)) {
                    this.raiseError(line, "Const variable declaration must include an assignment to the variable");
                }

                return new VariableDeclarationStatement(sinfo, vvar.name, isConst, vvar.vtype, exp, sccinfo);
            }
        }
        else if(tk === TokenStrings.Identifier && this.peekTokenData() === "self") {
            this.ensureTaskOpOk();

            this.consumeToken();
            this.ensureAndConsumeToken(SYM_dot, "self field assign statement");
            this.ensureToken(TokenStrings.Identifier, "to assign to in self field assign statement");
            const fname = this.consumeTokenAndGetValue();

            this.ensureAndConsumeToken(SYM_eq, "self field assign statement");
            const value = this.parseExpression();

            this.ensureAndConsumeToken(SYM_semicolon, "self field assign statement");

            return new TaskSetSelfFieldStatement(sinfo, fname, value);
        }
        else if (tk === TokenStrings.Identifier) {
            if(this.peekToken(1) === SYM_at) {
                const name = this.consumeTokenAndGetValue();
                this.consumeToken();
                
                const ttest = this.parseITest()
                this.ensureAndConsumeToken(SYM_semicolon, "variable retype");

                return new VariableRetypeStatement(sinfo, name, ttest);
            }
            else if(this.peekToken(1) === SYM_atat || this.peekToken(1) === SYM_questionquestion) {
                const name = this.consumeTokenAndGetValue();

                const isconvert = this.testToken(SYM_atat);
                this.consumeToken();

                const bindername = `$_$_${this.m_penv.getBinderExtension("$")}`;
                if(isconvert) {
                    const sctest = this.parseITest();
                    const scaction = this.testAndConsumeTokenIf(SYM_colon) ? this.parseExpressionWithBinder() : undefined;

                    return new VariableSCRetypeStatement(sinfo, name, sctest, scaction !== undefined ? scaction[1] : undefined, (scaction !== undefined && scaction[0]) ? bindername : undefined);
                }
                else {
                    const sctest = this.parseSCReturnTest();
                    const scaction = this.testAndConsumeTokenIf(SYM_colon) ? this.parseExpressionWithBinder() : undefined;

                    return new ExpressionSCReturnStatement(sinfo, new AccessVariableExpression(sinfo, name), sctest, scaction !== undefined ? scaction[1] : undefined, (scaction !== undefined && scaction[0]) ? bindername : undefined);
                }
            }
            else {
                const assign = this.parseAssignmentVarInfo(this.getCurrentSrcInfo(), undefined);
                const vvar = { name: assign.name, vtype: assign.vtype };

                if (!this.m_penv.getCurrentFunctionScope().isVarNameDefined(assign.name)) {
                    this.raiseError(line, "Variable name not defined");
                }
                this.m_penv.getCurrentFunctionScope().defineLocalVar(assign.name, assign.name, false);

                this.ensureAndConsumeToken(SYM_eq, "assignment statement");
                if (this.testToken(TokenStrings.Namespace) && this.peekTokenData() === "Task") {
                    return this.parseTaskRunStatement(sinfo, false, false, vvar);
                }
                else {
                    const [exp, scinfo] = this.parseSCAssignExpression();
                    this.ensureAndConsumeToken(SYM_semicolon, "assignment statement");

                    return new VariableAssignmentStatement(sinfo, vvar.name, exp, scinfo);
                }
            }
        }
        else if (tk === KW_return) {
            this.consumeToken();

            if(this.testAndConsumeTokenIf(SYM_semicolon)) {
                return new ReturnStatement(sinfo, new LiteralNoneExpression(sinfo));
            }
            else {
                if(this.testToken(TokenStrings.Namespace) && this.peekTokenData() === "Task") {
                    return this.parseTaskRunStatement(sinfo, false, false, undefined);
                }
                else {
                    const exp = this.parseExpression();

                    this.ensureAndConsumeToken(SYM_semicolon, "return statement");
                    return new ReturnStatement(sinfo, exp);
                }
            }
        }
        else if (tk === KW_env) {
            this.ensureTaskOpOk();

            this.consumeToken();

            const isfresh = this.testToken(SYM_lbrace);
            let binds: {keyname: string, valexp: [TypeSignature, Expression] | undefined}[] = [];
            if(isfresh) {
                binds = this.parseEnvUpdateArguments(SYM_lbrace, SYM_rbrace).map((nn) => {
                    return {keyname: nn.name, valexp: nn.value};
                });
            }
            else {
                binds = this.parseEnvUpdateArguments(SYM_lbrack, SYM_rbrack).map((nn) => {
                    return {keyname: nn.name, valexp: nn.value};
                });
            }

            if(!isfresh && binds.length === 0) {
                this.raiseError(sinfo.line, "environment update without any assignments is vacuous")
            }

            if(binds.some((bb, ii) => binds.findIndex((obb) => obb.keyname === bb.keyname) !== ii)) {
                this.raiseError(sinfo.line, "duplicate key in environment operation");
            }

            if(this.testAndConsumeTokenIf(SYM_semicolon)) {
                //env set value here
                if(isfresh) {
                    return new EnvironmentFreshStatement(sinfo, binds);
                }
                else {
                    return new EnvironmentSetStatement(sinfo, binds);
                }
            }
            else if(this.testAndConsumeTokenIf(KW_in)) {
                const block = this.parseBlockStatement("environment");

                return new EnvironmentSetStatementBracket(sinfo, binds, block, isfresh);
            }
            else {
                this.raiseError(sinfo.line, "expected a \";\" or \"in\" keyword as part of an environment statement");
                return new InvalidStatement(sinfo);
            }
        }
        else if (tk === KW_abort) {
            this.consumeToken();

            this.ensureAndConsumeToken(SYM_semicolon, "abort statement");
            return new AbortStatement(sinfo);
        }
        else if (tk === KW_assert) {
            this.consumeToken();

            const level = this.parseBuildInfo(KW_release);
            const exp = this.parseExpression();

            this.ensureAndConsumeToken(SYM_semicolon, "assert statement");
            return new AssertStatement(sinfo, exp, level);
        }
        else if (tk === KW__debug) {
            this.consumeToken();

            this.ensureAndConsumeToken(SYM_lparen, "_debug statement");
            const value = this.parseExpression();
            this.ensureAndConsumeToken(SYM_rparen, "_debug statement");
            
            this.ensureAndConsumeToken(SYM_semicolon, "_debug statement");
            return new DebugStatement(sinfo, value);
        }
        else if (tk === KW_ref) {
            const call = this.parseSCRefExpression();
            if(!(call[0] instanceof PostfixOp) && !(call[0] instanceof TaskSelfActionExpression)) {
                this.raiseError(sinfo.line, "ref invoke statement");
            }

            return new RefCallStatement(sinfo, call[0] as (PostfixOp | TaskSelfActionExpression), call[1]);
        }
        else if(tk === KW_callwith) {
            this.ensureTaskOpOk();

            this.consumeToken();
            this.ensureToken(TokenStrings.Identifier, "callwith operation");
            if(this.consumeTokenAndGetValue() !== "self") {
                this.raiseError(sinfo.line, "can only callwith on self actions");
            }

            this.ensureAndConsumeToken(SYM_dot, "callwith operation");

            this.ensureToken(TokenStrings.Identifier, "callwith operation name");
            const cname = this.consumeTokenAndGetValue();

            const terms = this.testToken(SYM_le) ? this.parseTemplateArguments() : [];
            const args = this.parseArguments(SYM_lparen, SYM_rparen);

            this.ensureAndConsumeToken(SYM_semicolon, "callwith operation");

            return new TaskCallWithStatement(sinfo, cname, terms, args);
        }
        else if(tk === KW_resultwith) {
            this.ensureTaskOpOk();

            this.consumeToken();
            this.ensureToken(TokenStrings.Identifier, "resultwith operation");
            if(this.consumeTokenAndGetValue() !== "self") {
                this.raiseError(sinfo.line, "can only resultwith on self actions");
            }

            this.ensureAndConsumeToken(SYM_dot, "resultwith operation");

            this.ensureToken(TokenStrings.Identifier, "resultwith operation name");
            const cname = this.consumeTokenAndGetValue();

            const terms = this.testToken(SYM_le) ? this.parseTemplateArguments() : [];
            const args = this.parseArguments(SYM_lparen, SYM_rparen);

            this.ensureAndConsumeToken(SYM_semicolon, "resultwith operation");

            return new TaskCallWithStatement(sinfo, cname, terms, args);
        }
        else if(tk === TokenStrings.Namespace && this.peekTokenData() === "Task") {
            this.ensureTaskOpOk();

            this.consumeToken();
            this.ensureAndConsumeToken(SYM_coloncolon, "Task operation");
            this.ensureToken(TokenStrings.Identifier, "Task operation");
            const op = this.consumeTokenAndGetValue();
            if(op !== "status" && op !== "event") {
                this.raiseError(sinfo.line, `unknown call ${op} on Task`);
            }

            const args = this.parseArguments(SYM_lparen, SYM_rparen);
            if(args.length !== 1) {
                this.raiseError(sinfo.line, `Task::${op} takes a single argument`);
            }

            this.ensureAndConsumeToken(SYM_semicolon, `Task::${op} operation`);
                    
            if(op === "status") {
                return new TaskSetStatusStatement(sinfo, args[0]);
            }
            else {
                return new TaskEventEmitStatement(sinfo, args[0]);
            }
        }
        else if(tk === TokenStrings.Namespace && this.peekTokenData() === "Log") {
            this.ensureTaskOpOk();

            this.consumeToken();
            this.ensureAndConsumeToken(SYM_coloncolon, "Task operation");
            this.ensureToken(TokenStrings.Identifier, "Task operation");
            const op = this.consumeTokenAndGetValue();

            if(op === "setLevel") {
                const levels = this.parseArgumentsNamed(SYM_lparen, SYM_rparen);
                if(levels.some((nn) => ["emit", "buffer"].includes(nn.name))) {
                    this.raiseError(sinfo.line, "Valid logger output names are \"emit\" and \"buffer\"");
                }

                const largs = levels.map((nn) => {
                    return {lname: nn.name, lvalue: nn.value};
                });

                this.ensureAndConsumeToken(KW_in, "setLevel");
                const block = this.parseBlockStatement("setLevel");
                return new LoggerLevelStatement(sinfo, largs, block);
            }
            else if(op === "setCategory") {
                const ctgs = this.parseArgumentsNamed(SYM_lparen, SYM_rparen);

                const cargs = ctgs.map((nn) => {
                    return {cname: nn.name, cvalue: nn.value};
                });

                this.ensureAndConsumeToken(KW_in, "setCategory");
                const block = this.parseBlockStatement("setCategory");
                return new LoggerCategoryStatement(sinfo, cargs, block);
            }
            else if(op === "scope") {
                const pfxargs = this.parseArguments(SYM_lparen, SYM_rparen);

                if(pfxargs.length === 0 || !(pfxargs[0] instanceof AccessFormatInfoExpression)) {
                    this.raiseError(sinfo.line, "Missing format specifier");
                }

                this.ensureAndConsumeToken(KW_in, "scope");
                const block = this.parseBlockStatement("scope");

                return new LoggerPrefixStatement(sinfo, pfxargs[0] as AccessFormatInfoExpression, pfxargs.slice(1), block);
            }
            else if(LoggerConditionalActions.includes(op)) {
                const pfxargs = this.parseArguments(SYM_lparen, SYM_rparen);

                if(pfxargs.length === 0 || !(pfxargs[0] instanceof AccessFormatInfoExpression)) {
                    this.raiseError(sinfo.line, "Missing format specifier");
                }

                return new LoggerEmitStatement(sinfo, logLevelNumber(op.slice(0, op.length - 2)), pfxargs[0] as AccessFormatInfoExpression, pfxargs.slice(1));
            }
            else if(LoggerActions.includes(op)) {
                const pfxargs = this.parseArguments(SYM_lparen, SYM_rparen);

                if(pfxargs.length < 2 || !(pfxargs[1] instanceof AccessFormatInfoExpression)) {
                    this.raiseError(sinfo.line, "Missing format specifier");
                }

                return new LoggerEmitConditionalStatement(sinfo, logLevelNumber(op), pfxargs[0], pfxargs[1] as AccessFormatInfoExpression, pfxargs.slice(2));
            }
            else {
                this.raiseError(sinfo.line, `Unknown logger operation ${op}`);
                return new InvalidStatement(sinfo);
            }
        }
        else if(tk === SYM_lbrace) {
            return this.parseScopedBlockStatement();
        }
        else if (tk === SYM_lbracebar) {
            return this.parseUnscopedBlockStatement();
        }
        else {
            const [exp, tsccinfo] = this.parseSCAssignExpression();
            if(tsccinfo === undefined) {
                this.raiseError(line, `expected short-circuit return guard but did not find it`);
            }
            const sccinfo = tsccinfo as {sctest: ITest | Expression, scaction: Expression | undefined, binderinfo: string | undefined};

            this.ensureAndConsumeToken(SYM_semicolon, "short-circuit return guard");
            return new ExpressionSCReturnStatement(sinfo, exp, sccinfo.sctest, sccinfo.scaction, sccinfo.binderinfo);
        }
    }

    private parseUnscopedBlockStatement(): UnscopedBlockStatement {
        const sinfo = this.getCurrentSrcInfo();

        this.m_penv.getCurrentFunctionScope().pushLocalScope();
        let stmts: Statement[] = [];
        try {
            this.setRecover(this.scanMatchingParens(SYM_lbracebar, SYM_rbracebar));

            this.consumeToken();
            while (!this.testAndConsumeTokenIf(SYM_rbracebar)) {
                stmts.push(this.parseStatement());
            }

            this.m_penv.getCurrentFunctionScope().popLocalScope();

            if (stmts.length === 0) {
                this.raiseError(this.getCurrentLine(), "No empty blocks -- requires at least ';'");
            }

            this.clearRecover();
            return new UnscopedBlockStatement(sinfo, stmts);
        }
        catch (ex) {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
            this.processRecover();
            return new UnscopedBlockStatement(sinfo, [new InvalidStatement(sinfo)]);
        }
    }

    private parseScopedBlockStatement(): ScopedBlockStatement {
        const sinfo = this.getCurrentSrcInfo();

        this.m_penv.getCurrentFunctionScope().pushLocalScope();
        let stmts: Statement[] = [];
        try {
            this.setRecover(this.scanMatchingParens(SYM_lbrace, SYM_rbrace));

            this.consumeToken();
            while (!this.testAndConsumeTokenIf(SYM_rbrace)) {
                stmts.push(this.parseStatement());
            }

            this.m_penv.getCurrentFunctionScope().popLocalScope();

            if (stmts.length === 0) {
                this.raiseError(this.getCurrentLine(), "No empty blocks -- requires at least ';'");
            }

            this.clearRecover();
            return new ScopedBlockStatement(sinfo, stmts);
        }
        catch (ex) {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
            this.processRecover();
            return new ScopedBlockStatement(sinfo, [new InvalidStatement(sinfo)]);
        }
    }

    private parseScopedBlockStatementWithBinder(): [boolean, ScopedBlockStatement] {
        try {
            this.m_penv.getCurrentFunctionScope().pushLocalScope();
            this.m_penv.getCurrentFunctionScope().defineLocalVar("$", `$_$_${this.m_penv.getBinderExtension("$")}`, true);

            const ss = this.parseScopedBlockStatement();
            const isbind = this.m_penv.getCurrentFunctionScope().getUsedImplicitBinder();

            return [isbind, ss];
        }
        finally {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
        }
    }

    private parseIfElseStatement(): Statement {
        const sinfo = this.getCurrentSrcInfo();
        const bindername = `$_$_${this.m_penv.getBinderExtension("$")}`;

        let conds: {cond: IfTest, value: ScopedBlockStatement, binderinfo: string | undefined }[] = [];

        this.ensureAndConsumeToken(KW_if, "if statement cond");
        const iftest = this.parseIfTest(bindername);
        const [ifbind, ifbody] = this.parseScopedBlockStatementWithBinder();
        conds.push({cond: iftest, value: ifbody, binderinfo: ifbind ? bindername : undefined});

        while (this.testAndConsumeTokenIf(KW_elif)) {
            const eliftest = this.parseIfTest(bindername);
            const [elifbind, elifbody] = this.parseScopedBlockStatementWithBinder();
            conds.push({cond: eliftest, value: elifbody, binderinfo: elifbind ? bindername : undefined});
        }

        if(!this.testAndConsumeTokenIf(KW_else)) {
            return new IfStatement(sinfo, conds, undefined);
        }
        else {
            const [elsebind, elsebody] = this.parseScopedBlockStatementWithBinder();
            return new IfStatement(sinfo, conds, {value: elsebody, binderinfo: elsebind ? bindername : undefined} );
        }
    }

    private parseStatementActionInBlock(): [boolean, ScopedBlockStatement] {
        try {
            this.m_penv.getCurrentFunctionScope().pushLocalScope();
            this.m_penv.getCurrentFunctionScope().defineLocalVar("$", `$_$_${this.m_penv.getBinderExtension("$")}`, true);

            if (this.testToken("{")) {
                const ss = this.parseScopedBlockStatement();
                const isbind = this.m_penv.getCurrentFunctionScope().getUsedImplicitBinder();

                return [isbind, ss];
            }
            else {
                const ss = this.parseLineStatement();
                const isbind = this.m_penv.getCurrentFunctionScope().getUsedImplicitBinder();

                return [isbind, new ScopedBlockStatement(this.getCurrentSrcInfo(), [ss])];
            }
        }
        finally {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
        }
    }

    private parseSwitchStatement(): Statement {
        const sinfo = this.getCurrentSrcInfo();
        const bindername = `$_$_${this.m_penv.getBinderExtension("$")}`;

        this.ensureAndConsumeToken(KW_switch, "switch statement dispatch value");

        this.ensureAndConsumeToken(SYM_lparen, "switch statement dispatch value");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(SYM_rparen, "switch statement dispatch value");

        let entries: { condlit: LiteralExpressionValue | undefined, value: ScopedBlockStatement, binderinfo: string | undefined }[] = [];
        this.ensureAndConsumeToken(SYM_lbrace, "switch statement options");
        
        const swlit = this.parseSwitchLiteralGuard();
        this.ensureAndConsumeToken(SYM_bigarrow, "switch statement entry");
        const [swbind, swvalue] = this.parseStatementActionInBlock();

        entries.push({ condlit: swlit, value: swvalue, binderinfo: swbind ? bindername : undefined});
        while (this.testToken(SYM_bar)) {
            this.consumeToken();

            const swlitx = this.parseSwitchLiteralGuard();
            this.ensureAndConsumeToken(SYM_bigarrow, "switch statement entry");
            const [swbindx, swvaluex] = this.parseStatementActionInBlock();

            entries.push({ condlit: swlitx, value: swvaluex, binderinfo: swbindx ? bindername : undefined });
        }
        this.ensureAndConsumeToken(SYM_rbrace, "switch statement options");

        return new SwitchStatement(sinfo, mexp, entries);
    }

    private parseMatchStatement(): Statement {
        const sinfo = this.getCurrentSrcInfo();
        const bindername = `$_$_${this.m_penv.getBinderExtension("$")}`;

        this.ensureAndConsumeToken(KW_match, "match statement dispatch value");

        this.ensureAndConsumeToken(SYM_lparen, "match statement dispatch value");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(SYM_rparen, "match statement dispatch value");
 
        let entries: { mtype: TypeSignature | undefined, value: ScopedBlockStatement, binderinfo: string | undefined  }[] = [];
        this.ensureAndConsumeToken(SYM_lbrace, "match statement options");

        const mtype = this.parseMatchTypeGuard();
        this.ensureAndConsumeToken(SYM_bigarrow, "match statement entry");
        const [mbind, mvalue] = this.parseStatementActionInBlock();

        entries.push({ mtype: mtype, value: mvalue, binderinfo: mbind ? bindername : undefined });
        while (this.testToken(SYM_bar)) {
            this.consumeToken();
            
            const mtypex = this.parseMatchTypeGuard();
            this.ensureAndConsumeToken(SYM_bigarrow, "match statement entry");
            const [mbindx, mvaluex] = this.parseStatementActionInBlock();


            entries.push({ mtype: mtypex, value: mvaluex, binderinfo: mbindx ? bindername : undefined });
        }
        this.ensureAndConsumeToken(SYM_rbrace, "switch statment options");

        return new MatchStatement(sinfo, mexp, entries);
    }

    private parseStatement(): Statement {
        if (this.testToken(KW_if)) {
            return this.parseIfElseStatement();
        }
        else if (this.testToken(KW_switch)) {
            return this.parseSwitchStatement();
        }
        else if (this.testToken(KW_match)) {
            return this.parseMatchStatement();
        }
        else {
            return this.parseLineStatement();
        }
    }

    private parseBody(file: string): BodyImplementation {
        if(this.testToken(SYM_eq)) {
            this.consumeToken();
            const iname = this.consumeTokenAndGetValue();
            this.ensureAndConsumeToken(SYM_semicolon, "body");
            
            return new BodyImplementation(file, iname);
        }
        else if(this.testFollows(SYM_lbrace, KW_synth)) {
            this.consumeToken();
            this.consumeToken();
            this.ensureAndConsumeToken(SYM_semicolon, "synth body");
            this.ensureAndConsumeToken(SYM_rbrace, "synth body");

            return new BodyImplementation(file, new SynthesisBody(file, this.getCurrentSrcInfo()));
        }
        else if (this.testToken(SYM_lbrace)) {
            return new BodyImplementation(file, this.parseScopedBlockStatement());
        }
        else {
            return new BodyImplementation(file, this.parseExpression());
        }
    }

    ////
    //Decl parsing

    private parseAttributes(): string[] {
        let attributes: string[] = [];
        while (Lexer.isAttributeKW(this.peekTokenData())) {
            attributes.push(this.consumeTokenAndGetValue());
        }
        return attributes;
    }

    private parseTemplateConstraint(hasconstraint: boolean): TypeSignature {
        if(!hasconstraint) {
            return this.m_penv.SpecialAnySignature;
        }
        else {
            return this.parseTypeSignature();
        }
    }

    private parseTermDeclarations(): TemplateTermDecl[] {
        let terms: TemplateTermDecl[] = [];
        if (this.testToken("<")) {
            terms = this.parseListOf<TemplateTermDecl>("template term declarations", SYM_le, SYM_ge, SYM_coma, () => {
                this.ensureToken(TokenStrings.Template, "template term declaration entry");
                const templatename = this.consumeTokenAndGetValue();

                const isunique = this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "unique";
                if(isunique) {
                    this.consumeToken();
                }

                const isgrounded = this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "grounded";
                if(isgrounded) {
                    this.consumeToken();
                }

                const isnumeric = this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "numeric";
                if(isgrounded) {
                    this.consumeToken();
                }

                const tconstraint = this.parseTemplateConstraint(!this.testToken(SYM_coma) && !this.testToken(SYM_ge));
                return new TemplateTermDecl(templatename, isunique, isgrounded, isnumeric, tconstraint);
            });
        }
        return terms;
    }

    private parseSingleTermRestriction(): TemplateTypeRestriction {
        const sinfo = this.getCurrentSrcInfo();

        this.ensureToken(TokenStrings.Template, "template restriction");
        const templatename = this.consumeTokenAndGetValue();

        const isunique = this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "unique";
        if(isunique) {
            this.consumeToken();
        }
        
        const isgrounded = this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "grounded";
        if(isgrounded) {
            this.consumeToken();
        }

        const tconstraint = this.parseTemplateConstraint(true);

        return new TemplateTypeRestriction(new TemplateTypeSignature(sinfo, templatename), isunique, isgrounded, tconstraint);
    }

    private parseTermRestrictionList(): TemplateTypeRestriction[] {
        const trl = this.parseSingleTermRestriction();
        if (this.testAndConsumeTokenIf(SYM_ampamp)) {
            const ands = this.parseTermRestrictionList();
            return [trl, ...ands];
        }
        else {
            return [trl];
        }
    }

    private parseTermRestriction(parencheck: boolean): TypeConditionRestriction | undefined {
        if(parencheck && !this.testToken(SYM_lbrace)) {
            return undefined;
        }
        this.testAndConsumeTokenIf(SYM_lbrace);

        if(parencheck) {
            this.testAndConsumeTokenIf(KW_when);
        }
        
        const trl = this.parseTermRestrictionList();

        if(parencheck) {
            this.ensureAndConsumeToken(SYM_rbrace, "template term restiction");
        }

        return new TypeConditionRestriction(trl);
    }

    private parsePreAndPostConditions(sinfo: SourceInfo, argnames: Set<string>, boundtemplates: Set<string>, rtype: TypeSignature): [PreConditionDecl[], PostConditionDecl[]] {
        let preconds: PreConditionDecl[] = [];
        try {
            this.m_penv.pushFunctionScope(new FunctionScope(argnames, boundtemplates, rtype, false));
            while (this.testToken(KW_requires)) {
                this.consumeToken();
                
                const level = this.parseBuildInfo(KW_release);
                const exp = this.parseExpression();

                preconds.push(new PreConditionDecl(sinfo, level, exp));

                this.ensureAndConsumeToken(SYM_semicolon, "requires");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }

        let postconds: PostConditionDecl[] = [];
        try {
            const rargs = new Set<string>(argnames).add("$return").add("$this");
            this.m_penv.pushFunctionScope(new FunctionScope(rargs, boundtemplates, rtype, true));
            while (this.testToken(KW_ensures)) {
                this.consumeToken();

                const level = this.parseBuildInfo(KW_release);
                const exp = this.parseExpression();

                postconds.push(new PostConditionDecl(sinfo, level, exp));

                this.ensureAndConsumeToken(SYM_semicolon, "ensures");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }

        return [preconds, postconds];
    }

    private parseSamples(sinfo: SourceInfo): (InvokeSampleDeclInline | InvokeSampleDeclFile)[] {
        let samples: (InvokeSampleDeclInline | InvokeSampleDeclFile)[] = [];
        while (this.testToken(KW_test) || this.testToken(KW_example)) {
            const istest = this.testAndConsumeTokenIf(KW_test);
            this.ensureAndConsumeToken(KW_example, "example");

            if (this.testToken(TokenStrings.BSQON_EXAMPLE_FILE)) {
                const fp = this.consumeTokenAndGetValue();

                samples.push(new InvokeSampleDeclFile(sinfo, istest, fp));
            }
            else {
                this.ensureToken(TokenStrings.BSQON_EXAMPLE_ARGS, "example");
                const args = this.consumeTokenAndGetValue();

                this.ensureToken(TokenStrings.BSQON_EXAMPLE_RESULT, "example");
                const result = this.consumeTokenAndGetValue();

                samples.push(new InvokeSampleDeclInline(sinfo, istest, args, result));
            }

            this.ensureAndConsumeToken(SYM_semicolon, "example");
        }

        return samples;
    }

    private parseNamespaceDep(): {fromns: string, asns: string} {
        //import NS;
        //import NS as NS;

        this.ensureAndConsumeToken(KW_import, "namespace import");
        this.ensureToken(TokenStrings.ScopeName, "namespace import");
        const fromns = this.consumeTokenAndGetValue();

        let nsp = {fromns: fromns, asns: fromns}; //case of import NS;
        if(this.testToken(TokenStrings.Identifier)) {
            const nn = this.consumeTokenAndGetValue();
            if(nn !== "as") {
                this.raiseError(this.getCurrentLine(), "Expected keyword 'as'");
            }

            this.ensureToken(TokenStrings.ScopeName, "namespace import");
            const asns = this.consumeTokenAndGetValue();

            nsp = {fromns: fromns, asns: asns};
        }
        
        this.ensureAndConsumeToken(SYM_semicolon, "namespce import");

        return nsp;
    }

    private parseNamespaceUsing(currentDecl: NamespaceDeclaration) {
        //import NS;
        //import NS as NS;

        this.ensureAndConsumeToken(KW_import, "namespce import");
        this.ensureToken(TokenStrings.Namespace, "namespce import");
        const fromns = this.consumeTokenAndGetValue();

        let asns = fromns; //case of import NS;
        if(this.testToken(TokenStrings.Identifier)) {
            const nn = this.consumeTokenAndGetValue();
            if(nn !== "as") {
                this.raiseError(this.getCurrentLine(), "Expected keyword 'as'");
            }

            this.ensureToken(TokenStrings.Namespace, "namespace import");
            asns = this.consumeTokenAndGetValue();
        }
        
        this.ensureAndConsumeToken(SYM_semicolon, "namespace import");

        const ffns = this.m_penv.assembly.getNamespace(fromns);
        const names = [...ffns.declaredNames];

        //
        //TODO: Packaging!!!!
        //
        //Our versioning trick is going to be looking at the imported types and signatures (including transative dependencies). We will split up the 
        //package dependencies into "public" and "internal" -- internal dependencies can be resolved by finding a satisfying version OR cloning. The 
        //public dependences can be part of the exported signatures and must be resolved by finding satifying versions with other packages. 
        //
        //The full NS SHOULD include a part like packageVN, where N is the major version number of the root package. This will allow multiple 
        //coexisting major versions of a package to be used in an application. 
        //Good design practice would be put the public API type decls in one package and the API sigs + impls in thier own -- this way changing 
        //an API sig only forces updates to that package and the types + impl can be shared with the older versions if needed.
        //

        currentDecl.usings.push(new NamespaceUsing(fromns, asns, names));
    }

    private parseNamespaceTypedef(currentDecl: NamespaceDeclaration) {
        //typedef NAME = TypeConstraint;

        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken(KW_typedef, "typedef");
        this.ensureToken(TokenStrings.Type, "typedef");
        const tyname = this.consumeTokenAndGetValue();

        if (currentDecl.checkDeclNameClash(tyname)) {
            this.raiseError(this.getCurrentLine(), "Collision between typedef and other names");
        }

        this.ensureAndConsumeToken(SYM_eq, "typedef");
        const rpos = this.scanToken(SYM_semicolon);
        if (rpos === this.m_epos) {
            this.raiseError(this.getCurrentLine(), "Missing ; on typedef");
        }

        const btype = this.parseTypeSignature();
        this.consumeToken();

        currentDecl.typeDefs.set((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + tyname, new NamespaceTypedef(attributes, currentDecl.ns, tyname, btype));
    }

    private parseProvides(sinfo: SourceInfo, iscorens: boolean, endtoken: string[]): [TypeSignature, TypeConditionRestriction | undefined][] {
        let provides: [TypeSignature, TypeConditionRestriction | undefined][] = [];
        if (this.testAndConsumeTokenIf(KW_provides)) {
            while (!endtoken.some((tok) => this.testToken(tok))) {
                this.consumeTokenIf(SYM_coma);

                const pv = this.parseTypeSignature();
                let res: TypeConditionRestriction | undefined = undefined;
                if(this.testAndConsumeTokenIf(KW_when)) {
                    res = this.parseTermRestriction(false);
                }
                provides.push([pv, res]);
            }
        }
        
        if (!iscorens) {
            provides.push([new NominalTypeSignature(sinfo, "Core", ["Object"]), undefined]);
        }

        return provides;
    }

    private parseConstMember(staticMembers: StaticMemberDecl[], allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] const NAME: T = exp;
        this.ensureAndConsumeToken(KW_const, "const member");

        this.ensureToken(TokenStrings.Identifier, "const member");
        const sname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(SYM_colon, "const member");
        const stype = this.parseTypeSignature();

        this.ensureAndConsumeToken(SYM_eq, "const member");
        const value = this.parseConstExpression(false);

        this.ensureAndConsumeToken(SYM_semicolon, "const member");

        if (allMemberNames.has(sname)) {
            this.raiseError(this.getCurrentLine(), "Collision between const and other names");
        }

        allMemberNames.add(sname);
        staticMembers.push(new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), attributes, sname, stype, value));
    }

    private parseControlMember(controlMembers: ControlFieldDecl[], allControlNames: Set<string>, attributes: string[]) {
        this.ensureTaskOpOk();

        const sinfo = this.getCurrentSrcInfo();

        //[attr] control NAME: T = exp;
        this.ensureAndConsumeToken(KW_control, "control task value");

        this.ensureToken(TokenStrings.Identifier, "control task value");
        const sname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(SYM_colon, "control task value");
        const stype = this.parseTypeSignature();

        let dval: ConstantExpressionValue | undefined = undefined;
        if (this.testAndConsumeTokenIf(SYM_eq)) {
            dval = this.parseConstExpression(true);
        }

        this.ensureAndConsumeToken(SYM_semicolon, "control task value");

        if (allControlNames.has(sname)) {
            this.raiseError(this.getCurrentLine(), "Collision between control names");
        }

        allControlNames.add(sname);
        controlMembers.push(new ControlFieldDecl(sinfo, this.m_penv.getCurrentFile(), [...attributes], sname, stype, dval));
    }

    private parseStaticFunction(staticFunctions: StaticFunctionDecl[], allMemberNames: Set<string>, attributes: string[], typetemplates: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] function NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        this.ensureAndConsumeToken(KW_function, "function member");
        const termRestrictions = this.parseTermRestriction(true);

        this.ensureToken(TokenStrings.Identifier, "function member");
        const fname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(InvokableKind.Basic, Parser.attributeSetContains("abstract", attributes) || Parser.attributeSetContains("opaque", attributes), attributes, recursive, terms, typetemplates, termRestrictions, false);

        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(fname);

        staticFunctions.push(new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), attributes, fname, sig));
    }

    private parseMemberField(memberFields: MemberFieldDecl[], allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] field NAME: T = exp;
        this.ensureAndConsumeToken(KW_field, "member field");

        this.ensureToken(TokenStrings.Identifier, "member field");
        const fname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(SYM_colon, "member field");
        const stype = this.parseTypeSignature();

        this.ensureAndConsumeToken(SYM_semicolon, "member field");

        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between const and other names");
        }

        memberFields.push(new MemberFieldDecl(sinfo, this.m_penv.getCurrentFile(), attributes, fname, stype));
    }

    private parseMemberMethod(istask: boolean, thisType: TypeSignature, memberMethods: MemberMethodDecl[], allMemberNames: Set<string>, attributes: string[], typetemplates: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] method ref NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        this.ensureAndConsumeToken(KW_method, "member method");
        const refrcvr = this.testAndConsumeTokenIf(KW_ref);
        const termRestrictions = this.parseTermRestriction(true);

        this.ensureToken(TokenStrings.Identifier, "member method");
        const mname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(istask ? InvokableKind.SelfMember : InvokableKind.Member, Parser.attributeSetContains("abstract", attributes), attributes, recursive, terms, typetemplates, termRestrictions, refrcvr);

        allMemberNames.add(mname);

        memberMethods.push(new MemberMethodDecl(sinfo, this.m_penv.getCurrentFile(), attributes, mname, sig));
    }

    private parseMemberAction(thisType: TypeSignature, memberMethods: MemberMethodDecl[], allMemberNames: Set<string>, attributes: string[], typetemplates: string[]) {
        this.ensureTaskOpOk();

        const sinfo = this.getCurrentSrcInfo();

        //[attr] action NAME<T where C...>(params): type { ... }
        this.ensureAndConsumeToken("action", "task action");
        const termRestrictions = this.parseTermRestriction(true);

        this.ensureToken(TokenStrings.Identifier, "task action");
        const mname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const sig = this.parseInvokableCommon(InvokableKind.SelfMember, false, ["task_action", ...attributes], "no", terms, typetemplates, termRestrictions, true);

        allMemberNames.add(mname);

        memberMethods.push(new MemberMethodDecl(sinfo, this.m_penv.getCurrentFile(), ["task_action", ...attributes], mname, sig));
    }

    private parseInvariantsInto(sinfo: SourceInfo, invs: InvariantDecl[], vdates: ValidateDecl[], boundtemplates: Set<string>) {
        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(), boundtemplates, new NominalTypeSignature(sinfo, "Core", ["Bool"]), false));
            while (this.testToken(KW_invariant) || this.testToken(KW_validate)) {
                if(this.testToken(KW_validate)) {
                    this.consumeToken();

                    const sinfo = this.getCurrentSrcInfo();
                    const exp = this.parseConstExpression(true);

                    vdates.push(new ValidateDecl(sinfo, exp));
                }
                else {
                    this.consumeToken();

                    const level = this.parseBuildInfo(KW_release);
                    const sinfo = this.getCurrentSrcInfo();
                    const exp = this.parseConstExpression(true);

                    invs.push(new InvariantDecl(sinfo, level, exp));
                }

                this.ensureAndConsumeToken(SYM_semicolon, "invariant");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }
    }

    private parseEffect(statuseffect: TaskStatusEffect, eventeffect: TaskEventEffect, enveffect: TaskEnvironmentEffect, resourceeffects: TaskResourceEffect[]) {
        this.ensureTaskOpOk();

        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken(KW_effect, "effect");

        this.ensureAndConsumeToken(SYM_plus, "effect notation");
        this.ensureToken(TokenStrings.Identifier, "effect type");
        const effect = this.consumeTokenAndGetValue();

        if(effect === "status") {
            this.ensureToken(SYM_lbrack, "status effect");
            const enames = this.parseListOf("status effect", SYM_lbrack, SYM_rbrack, SYM_coma, () => {
                return this.parseTypeSignature();
            }); 
            
            statuseffect.statusinfo.push(...enames);
        }
        else if(effect === "event") {
            this.ensureToken(SYM_lbrack, "event effect");
            const enames = this.parseListOf("event effect", SYM_lbrack, SYM_rbrack, SYM_coma, () => {
                return this.parseTypeSignature();
            }); 
            
            eventeffect.eventinfo.push(...enames);
        }
        else if(effect === "environment") {
            this.ensureToken(SYM_lbrack, "environment effect");
            const enames = this.parseListOf("environment effect", SYM_lbrack, SYM_rbrack, SYM_coma, () => {
                this.ensureToken(TokenStrings.String, "environment variable name");
                const vv = this.consumeTokenAndGetValue();

                let isw = false;
                if(this.testAndConsumeTokenIf(SYM_plus)) {
                    this.ensureToken(TokenStrings.Identifier, "environment effect write");
                    const tt = this.consumeTokenAndGetValue();
                    if(tt !== "w") {
                        this.raiseError(this.getCurrentLine(), `expected a "w" modifier`);
                    }
                    isw = true;
                }
                return {vv: vv, isw: isw};
            });

            enveffect.evars.push(...enames);
        }
        else if(effect === "resource") {
            let isread = true;
            let iswrite = true;
            if(this.testToken(TokenStrings.Identifier)) {
                const rw = this.consumeTokenAndGetValue();

                isread = rw.includes("r");
                iswrite = rw.includes("w");
                if (rw.length > 2 || (rw[0] !== "r" && rw[0] !== "w") || (rw[1] !== "r" && rw[1] !== "w")) {
                    this.raiseError(sinfo.line, `Unknown read/write value "${rw}" on effect`);
                }
            }

            const rtype = this.parseTypeSignature();
            let rpathexp: ConstantExpressionValue | undefined = undefined;
            if(this.testToken(SYM_lbrack)) {
                this.ensureAndConsumeToken(SYM_lbrack, "Resource effect");
                    
                if(this.testAndConsumeTokenIf(SYM_coma)) {
                    rpathexp = this.parseConstExpression(true);
                }

                this.ensureAndConsumeToken(SYM_rbrack, "Resource effect");
            }

            resourceeffects.push(new TaskResourceEffect(rtype, rpathexp, isread, iswrite));
        }
        else {
            this.raiseError(sinfo.line, `Unknon effect kind ${effect}`);
        }


        this.ensureAndConsumeToken(SYM_semicolon, "effect notation");
    }

    private parseOOPMembersCommon(sinfo: SourceInfo, istask: boolean, thisType: TypeSignature, currentNamespace: NamespaceDeclaration, currentTypeNest: string[], currentTermNest: TemplateTermDecl[], currentTerms: Set<string>, 
        nestedEntities: Map<string, EntityTypeDecl>, invariants: InvariantDecl[], validates: ValidateDecl[],
        staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[], 
        memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[], 
        controlFields: ControlFieldDecl[] | undefined,
        statuseffects: TaskStatusEffect, eventeffects: TaskEventEffect, enveffects: TaskEnvironmentEffect, resourceeffects: TaskResourceEffect[]) {
        let allMemberNames = new Set<string>();
        let allControlNames = new Set<string>();
        while (!this.testToken(SYM_rbrace)) {
            const attributes = this.parseAttributes();

            if(this.testToken(KW_entity)) {
                this.parseObject(currentNamespace, nestedEntities, currentTypeNest, currentTermNest);
            }
            else if(this.testToken(KW_task)) {
                this.parseTask(currentNamespace, currentTermNest);
            }
            else if (this.testToken(KW_invariant) || this.testToken(KW_validate)) {
                this.parseInvariantsInto(sinfo, invariants, validates, currentTerms);
            }
            else if (this.testToken(KW_const)) {
                this.parseConstMember(staticMembers, allMemberNames, attributes);
            }
            else if (this.testToken(KW_control)) {
                if(controlFields === undefined) {
                    this.raiseError(this.getCurrentLine(), "control fields not allowed on declaration of non-task type");
                }
                this.parseControlMember(controlFields as ControlFieldDecl[], allControlNames, attributes);
            }
            else if (this.testToken(KW_function)) {
                this.parseStaticFunction(staticFunctions, allMemberNames, attributes, currentTermNest.map((tt) => tt.name));
            }
            else if (this.testToken(KW_field)) {
                this.parseMemberField(memberFields, allMemberNames, attributes);
            }
            else if(this.testToken(KW_method)) {
                this.parseMemberMethod(istask, thisType, memberMethods, allMemberNames, attributes, currentTermNest.map((tt) => tt.name));
            }
            else if(this.testToken(KW_action)) {
                this.parseMemberAction(thisType, memberMethods, allMemberNames, attributes, currentTermNest.map((tt) => tt.name))
            }
            else if(this.testToken(KW_effect)) {
                this.parseEffect(statuseffects, eventeffects, enveffects, resourceeffects);
            }
            else {
                this.raiseError(this.getCurrentLine(), `Unknown member ${this.peekTokenData()}`);
            }
        }
    }

    private parseConcept(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] concept NAME[T where C...] provides {...}
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken(KW_concept, "concept declaration");
        this.ensureToken(TokenStrings.Type, "concept declaration");

        const cname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const provides = this.parseProvides(sinfo, currentDecl.ns === "Core", [SYM_lbrace]);

        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken(SYM_lbrace, "concept declaration");

            const thisType = new NominalTypeSignature(sinfo, currentDecl.ns, [cname], terms.map((term) => new TemplateTypeSignature(sinfo, term.name)));

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
            const nestedEntities = new Map<string, EntityTypeDecl>();
            const statuseffect = new TaskStatusEffect([]);
            const eventeffect = new TaskEventEffect([]);
            const enveffect = new TaskEnvironmentEffect([]);
            this.parseOOPMembersCommon(sinfo, false, thisType, currentDecl, [cname], [...terms], new Set<string>(terms.map((tt) => tt.name)), nestedEntities, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, [], statuseffect, eventeffect, enveffect, []);

            this.ensureAndConsumeToken(SYM_rbrace, "concept declaration");

            if (currentDecl.checkDeclNameClash(cname)) {
                this.raiseError(line, "Collision between concept and other names");
            }

            this.clearRecover();

            if(currentDecl.ns === "Core") {
                if(cname === "Result") {
                    attributes.push("__result_type");
                }
                else if(cname === "Option") {
                    attributes.push("__option_type");
                }
                else {
                    //not special
                }
            }

            const cdecl = new ConceptTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, cname, terms, provides, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, nestedEntities);
            currentDecl.concepts.set(cname, cdecl);
            this.m_penv.assembly.addConceptDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + cname, cdecl);
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseObject(currentDecl: NamespaceDeclaration, enclosingMap: Map<string, EntityTypeDecl> | undefined, currentTypeNest: string[], currentTermNest: TemplateTermDecl[]) {
        const line = this.getCurrentLine();

        //[attr] object NAME[T where C...] provides {...}
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken(KW_entity, "entity declaration");
        this.ensureToken(TokenStrings.Type, "entity declaration");

        const ename = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const provides = this.parseProvides(sinfo, currentDecl.ns === "Core", [SYM_lbrace]);

        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken(SYM_lbrace, "entity declaration");

            const thisType = new NominalTypeSignature(sinfo, currentDecl.ns, [...currentTypeNest, ename], [...terms, ...currentTermNest].map((term) => new TemplateTypeSignature(sinfo, term.name)));

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
            const nestedEntities = new Map<string, EntityTypeDecl>();
            const statuseffect = new TaskStatusEffect([]);
            const eventeffect = new TaskEventEffect([]);
            const enveffect = new TaskEnvironmentEffect([]);
            this.parseOOPMembersCommon(sinfo, false, thisType, currentDecl, [...currentTypeNest, ename], [...currentTermNest, ...terms], new Set<string>([...currentTermNest, ...terms].map((tt) => tt.name)), nestedEntities, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, [], statuseffect, eventeffect, enveffect, []);

            this.ensureAndConsumeToken(SYM_rbrace, "entity declaration");

            if (currentDecl.checkDeclNameClash([...currentTypeNest, ename].join("::"))) {
                this.raiseError(line, "Collision between object and other names");
            }

            if(currentDecl.ns === "Core") {
                if(ename === "StringOf") {
                    attributes.push("__stringof_type");
                }
                else if(ename === "ASCIIStringOf") {
                    attributes.push("__asciistringof_type");
                }
                else if(ename === "Ok") {
                    attributes.push("__ok_type");
                }
                else if(ename === "Err") {
                    attributes.push("__err_type");
                }
                else if(ename === "Nothing") {
                    attributes.push("__nothing_type");
                }
                else if(ename === "Something") {
                    attributes.push("__something_type");
                }
                else if(ename === "MapEntry") {
                    attributes.push("__mapentry_type");
                }
                else if(ename === "List") {
                    attributes.push("__list_type");
                }
                else if(ename === "Stack") {
                    attributes.push("__stack_type");
                }
                else if(ename === "Queue") {
                    attributes.push("__queue_type");
                }
                else if(ename === "Set") {
                    attributes.push("__set_type");
                }
                else if(ename === "Map") {
                    attributes.push("__map_type");
                }
                else if(ename === "SeqList") {
                    attributes.push("__seqlist_type");
                }
                else if(ename === "SeqMap") {
                    attributes.push("__seqmap_type");
                }
                else if(ename === "Path") {
                    attributes.push("__path_type");
                }
                else if(ename === "PathFragment") {
                    attributes.push("__pathfragment_type");
                }
                else if(ename === "PathGlob") {
                    attributes.push("__pathglob_type");
                }
                else {
                    //not special
                }
            }

            this.clearRecover();

            const fename = [...currentTypeNest, ename].join("::");
            const feterms = [...currentTermNest, ...terms];

            const edecl = new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, fename, feterms, provides, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, nestedEntities);
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + fename, edecl);
            currentDecl.objects.set(ename, edecl);
            
            if(enclosingMap !== undefined) {
                enclosingMap.set(ename, edecl);
            }
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseTask(currentDecl: NamespaceDeclaration, currentTermNest: TemplateTermDecl[]) {
        const line = this.getCurrentLine();

        //[attr] task NAME[T where C...] provides {...}
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken(KW_task, "task declaration");
        this.ensureToken(TokenStrings.Type, "task declaration");

        const ename = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();

        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken(SYM_lbrace, "task declaration");

            const thisType = new NominalTypeSignature(sinfo, currentDecl.ns, [ename], [...terms, ...currentTermNest].map((term) => new TemplateTypeSignature(sinfo, term.name)));

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
            const nestedEntities = new Map<string, EntityTypeDecl>();
            
            const controlfields: ControlFieldDecl[] = [];

            const statuseffect = new TaskStatusEffect([]);
            const eventeffect = new TaskEventEffect([]);
            const enveffect = new TaskEnvironmentEffect([]);
            const resourceeffects: TaskResourceEffect[] = [];
            this.parseOOPMembersCommon(sinfo, true, thisType, currentDecl, [ename], [...currentTermNest, ...terms], new Set<string>([...currentTermNest, ...terms].map((tt) => tt.name)), nestedEntities, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, controlfields, statuseffect, eventeffect, enveffect, resourceeffects);

            if(invariants.length !== 0) {
                this.raiseError(sinfo.line, "Cannot define invariants on tasks (only validates)");
            }

            if(nestedEntities.size !== 0) {
                this.raiseError(sinfo.line, "Cannot define nested types on tasks");
            }

            this.ensureAndConsumeToken(SYM_rbrace, "task declaration");

            if (currentDecl.checkDeclNameClash(ename)) {
                this.raiseError(line, "Collision between task and other names");
            }

            this.clearRecover();

            const feterms = [...currentTermNest, ...terms];

            const mainfunc = staticFunctions.find((ff) => ff.name === "main");
            if(mainfunc === undefined) {
                this.raiseError(sinfo.line, "Does not have a \"main\" function defined")
            }

            const actions = memberMethods.filter((mf) => mf.attributes.includes("task_action"));
            const onfuncs = {
                onCanel: memberMethods.find((mf) => mf.name === "onCancel"),
                onFailure: memberMethods.find((mf) => mf.name === "onFailure"), 
                onTimeout: memberMethods.find((mf) => mf.name === "onTimeout")
            };

            const lfuncs = {
                logStart: memberMethods.find((mf) => mf.name === "logStart"),
                logEnd: memberMethods.find((mf) => mf.name === "logEnd"), 
                taskEnsures: memberMethods.find((mf) => mf.name === "taskEnsures"),
                taskWarns: memberMethods.find((mf) => mf.name === "taskWarns")
            };

            const edecl = new TaskTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, ename, feterms, validates, staticMembers, staticFunctions, memberFields, memberMethods, controlfields, mainfunc as StaticFunctionDecl, actions, onfuncs, lfuncs, statuseffect, eventeffect, enveffect, resourceeffects);
            this.m_penv.assembly.addTaskDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + ename, edecl);
            currentDecl.tasks.set(ename, edecl);
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseEnum(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] enum NAME {...} [& {...}]
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken(KW_enum, "enum declaration");
        this.ensureToken(TokenStrings.Type, "enum declaration");

        const ename = this.consumeTokenAndGetValue();
        const etype = new NominalTypeSignature(sinfo, currentDecl.ns, [ename]);

        if (currentDecl.checkDeclNameClash(ename)) {
            this.raiseError(line, "Collision between object and other names");
        }

        try {
            this.setRecover(this.scanCodeParens());

            const enums = this.parseListOf<string>("enum declaration", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                this.ensureToken(TokenStrings.Identifier, "enum member");
                return this.consumeTokenAndGetValue();
            });
            
            const provides = [
                [new NominalTypeSignature(sinfo, "Core", ["Some"]), undefined],
                [new NominalTypeSignature(sinfo, "Core", ["KeyType"]), undefined]
            ] as [TypeSignature, TypeConditionRestriction | undefined][];

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
    
            for(let i = 0; i < enums.length; ++i) {
                const exp = new LiteralIntegralExpression(sinfo, i.toString() + "n", this.m_penv.SpecialNatSignature);
                const enm = new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), ["__enum"], enums[i], etype, new ConstantExpressionValue(exp, new Set<string>()));
                staticMembers.push(enm);
            }

            if(this.testAndConsumeTokenIf(SYM_amp)) {
                this.setRecover(this.scanCodeParens());
                this.ensureAndConsumeToken(SYM_lbrace, "enum extension code");
    
                const thisType = new NominalTypeSignature(sinfo, currentDecl.ns, [ename], []);
    
                const nestedEntities = new Map<string, EntityTypeDecl>();
                const statuseffect = new TaskStatusEffect([]);
                const eventeffect = new TaskEventEffect([]);
                const enveffect = new TaskEnvironmentEffect([]);
                this.parseOOPMembersCommon(sinfo, false, thisType, currentDecl, [ename], [], new Set<string>(), nestedEntities, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, [], statuseffect, eventeffect, enveffect, []);
    
                if(invariants.length !== 0 || validates.length !== 0) {
                    this.raiseError(sinfo.line, "cannot declare invariants on enum");
                }

                if(memberFields.length !== 0) {
                    this.raiseError(sinfo.line, "cannot declare member fields on enum");
                }

                this.ensureAndConsumeToken(SYM_rbrace, "enum extension code");
    
                this.clearRecover();
            }

            if (currentDecl.checkDeclNameClash(ename)) {
                this.raiseError(line, "Collision between object and other names");
            }

            if(invariants.length !== 0) {
                this.raiseError(line, "Cannot have invariant function on Enum types");
            }

            attributes.push("__enum_type", "__constructable");

            this.clearRecover();
            currentDecl.objects.set(ename, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, ename, [], provides, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, new Map<string, EntityTypeDecl>()));
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + ename, currentDecl.objects.get(ename) as EntityTypeDecl);
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseTypeDecl(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
       
        this.ensureAndConsumeToken(KW_typedecl, "typedecl");

        const iname = this.consumeTokenAndGetValue();
        if (currentDecl.checkDeclNameClash(iname)) {
            this.raiseError(line, "Collision between object and other names");
        }

        this.ensureAndConsumeToken(SYM_eq, "typedecl");
        if (this.testToken(TokenStrings.Regex)) {
            //[attr] typedecl NAME = regex;

            const vregex = this.consumeTokenAndGetValue();
            this.ensureAndConsumeToken(SYM_semicolon, "Validator");

            const re = BSQRegex.parse(this.m_penv.getCurrentNamespace(), iname, vregex);
            if (typeof (re) === "string") {
                this.raiseError(this.getCurrentLine(), re);
            }

            const param = new FunctionParameter("arg", new NominalTypeSignature(sinfo, "Core", ["String"]), undefined);

            const acceptsbody = new BodyImplementation(this.m_penv.getCurrentFile(), "validator_accepts");
            const acceptsinvoke = new InvokeDecl("Core", sinfo, sinfo, this.m_penv.getCurrentFile(), ["__safe"], "no", [], undefined, [param], false, new NominalTypeSignature(sinfo, "Core", ["Bool"]), [], [], [], false, false, new Set<string>(), new Set<string>(), acceptsbody);
            const accepts = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), ["__safe"], "accepts", acceptsinvoke);
            const provides = [[new NominalTypeSignature(sinfo, "Core", ["Some"]), undefined], [new NominalTypeSignature(sinfo, "Core", ["Validator"]), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            const validatortype = new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), ["__validator_type", ...attributes], currentDecl.ns, iname, [], provides, [], [], [], [accepts], [], [], new Map<string, EntityTypeDecl>());

            currentDecl.objects.set(iname, validatortype);
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + iname, currentDecl.objects.get(iname) as EntityTypeDecl);
            this.m_penv.assembly.addValidatorRegex(re as BSQRegex);
        }
        else if(this.testToken(SYM_lbrace)) {
            //[attr] typedecl NAME = pathvalidator;
            
            const vv = this.parsePathValidator(currentDecl, iname);
            this.ensureAndConsumeToken(SYM_semicolon, "PathValidator");

            const param = new FunctionParameter("arg", new NominalTypeSignature(sinfo, "Core", ["String"]), undefined);

            const acceptsbody = new BodyImplementation(this.m_penv.getCurrentFile(), "pathvalidator_accepts");
            const acceptsinvoke = new InvokeDecl("Core", sinfo, sinfo, this.m_penv.getCurrentFile(), ["__safe"], "no", [], undefined, [param], false, new NominalTypeSignature(sinfo, "Core", ["Bool"]), [], [], [], false, false, new Set<string>(), new Set<string>(), acceptsbody);
            const accepts = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), ["__safe"], "accepts", acceptsinvoke);
            const provides = [[new NominalTypeSignature(sinfo, "Core", ["Some"]), undefined], [new NominalTypeSignature(sinfo, "Core", ["PathValidator"]), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            const validatortype = new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), ["__pathvalidator_type", ...attributes], currentDecl.ns, iname, [], provides, [], [], [], [accepts], [], [], new Map<string, EntityTypeDecl>());

            currentDecl.objects.set(iname, validatortype);
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + iname, currentDecl.objects.get(iname) as EntityTypeDecl);
            this.m_penv.assembly.addValidatorPath(vv);
        }
        else {
            //[attr] typedecl NAME = PRIMITIVE [& {...}];

            const idval = this.parseNominalType() as NominalTypeSignature;

            let provides = [[new NominalTypeSignature(sinfo, "Core", ["Some"]), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            provides.push([new NominalTypeSignature(sinfo, "Core", ["KeyType"]), new TypeConditionRestriction([new TemplateTypeRestriction(idval, false, false, new NominalTypeSignature(sinfo, "Core", ["KeyType"]))])]);

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];

            if (this.testAndConsumeTokenIf(SYM_amp)) {
                this.setRecover(this.scanCodeParens());
                this.ensureAndConsumeToken(SYM_lbrace, "typedecl");

                const thisType = new NominalTypeSignature(sinfo, currentDecl.ns, [iname], []);

                const nestedEntities = new Map<string, EntityTypeDecl>();
                const statuseffect = new TaskStatusEffect([]);
                const eventeffect = new TaskEventEffect([]);
                const enveffect = new TaskEnvironmentEffect([]);
                this.parseOOPMembersCommon(sinfo, false, thisType, currentDecl, [iname], [], new Set<string>(), nestedEntities, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, [], statuseffect, eventeffect, enveffect, []);

                this.ensureAndConsumeToken(SYM_rbrace, "typedecl");

                if (currentDecl.checkDeclNameClash(iname)) {
                    this.raiseError(line, "Collision between concept and other names");
                }

                this.clearRecover();
            }
            else {
                this.ensureAndConsumeToken(SYM_semicolon, "typedecl");
            }

            if(memberFields.length !== 0) {
                this.raiseError(sinfo.line, "Cannot declare additional member fields on typedecl");
            }

            const valuebody = new BodyImplementation(this.m_penv.getCurrentFile(), "special_extract");
            const valuedecl = new InvokeDecl("Core", sinfo, sinfo, this.m_penv.getCurrentFile(), ["__safe"], "no", [], undefined, [], false, idval, [], [], [], false, false, new Set<string>(), new Set<string>(), valuebody);
            const value = new MemberMethodDecl(sinfo, this.m_penv.getCurrentFile(), ["__safe"], "value", valuedecl);

            //
            //TODO: maybe want to do a special underlying operator that looks like a method to just get the base type
            //      we will need to do some fancy resolution on the type since we don't know the base type yet
            //      maybe even make this a string, int, float as the name of the method
            //

            memberMethods.push(value);

            attributes.push("__typedprimitive", "__constructable");

            currentDecl.objects.set(iname, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, iname, [], provides, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, new Map<string, EntityTypeDecl>()));
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + iname, currentDecl.objects.get(iname) as EntityTypeDecl);
        }
    }

    private parseDataTypeDecl(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();
       
        this.ensureAndConsumeToken(KW_datatype, "datatype");

        const iname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        if (currentDecl.checkDeclNameClash(iname)) {
            this.raiseError(line, "Collision between object and other names");
        }

        //[attr] datatype NAME<...> [provides ... ] [using {...}] of
        // Foo {...}
        // | ...
        // [& {...}] | ;

        const concepttype = new NominalTypeSignature(sinfo, currentDecl.ns, [iname]);

        const provides = this.parseProvides(sinfo, currentDecl.ns === "Core", [KW_of, KW_using]);

        let complexheader = false;
        let cinvariants: InvariantDecl[] = [];
        let cvalidates: ValidateDecl[] = [];
        let cstaticMembers: StaticMemberDecl[] = [];
        let cstaticFunctions: StaticFunctionDecl[] = [];
        let cusing: MemberFieldDecl[] = [];
        let cmemberMethods: MemberMethodDecl[] = [];
        if (this.testAndConsumeTokenIf("using")) {
            if (this.testFollows(SYM_lbrace, TokenStrings.Identifier) && !Lexer.isAttributeKW(this.peekTokenData(1))) {
                cusing = this.parseListOf<MemberFieldDecl>("datatype concept", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                    const mfinfo = this.getCurrentSrcInfo();

                    this.ensureToken(TokenStrings.Identifier, "datatype concept field");
                    const name = this.consumeTokenAndGetValue();
                    this.ensureAndConsumeToken(SYM_colon, "datatype concept field");

                    const ttype = this.parseTypeSignature();
                    return new MemberFieldDecl(mfinfo, this.m_penv.getCurrentFile(), [], name, ttype);
                });
            }
            else {
                this.setRecover(this.scanCodeParens());
                this.ensureAndConsumeToken(SYM_lbrace, "datatype declaration");

                const thisType = new NominalTypeSignature(sinfo, currentDecl.ns, [iname], []);

                const nestedEntities = new Map<string, EntityTypeDecl>();
                const statuseffect = new TaskStatusEffect([]);
                const eventeffect = new TaskEventEffect([]);
                const enveffect = new TaskEnvironmentEffect([]);
                this.parseOOPMembersCommon(sinfo, false, thisType, currentDecl, [iname], [...terms], new Set<string>(terms.map((tt) => tt.name)), nestedEntities, cinvariants, cvalidates, cstaticMembers, cstaticFunctions, cusing, cmemberMethods, [], statuseffect, eventeffect, enveffect, []);

                this.ensureAndConsumeToken(SYM_rbrace, "datatype declaration");
                complexheader = cstaticMembers.length !== 0 || cstaticFunctions.length !== 0 || cmemberMethods.length !== 0;
            }
        }

        this.ensureAndConsumeToken(KW_of, "datatype");

        const edecls: EntityTypeDecl[] = [];
        while (!this.testToken(SYM_semicolon) && !this.testToken(SYM_amp)) {
            if (this.testToken(SYM_bar)) {
                this.consumeToken();
            }
            let esinfo = this.getCurrentSrcInfo();

            this.ensureToken(TokenStrings.Type, "datatype entities");
            const ename = this.consumeTokenAndGetValue();
            if (currentDecl.checkDeclNameClash(ename)) {
                this.raiseError(line, "Collision between object and other names");
            }

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            let memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
            if (this.testToken(SYM_lbrace)) {
                if (this.testFollows(SYM_lbrace, TokenStrings.Identifier) && !Lexer.isAttributeKW(this.peekTokenData(1))) {
                    memberFields = this.parseListOf<MemberFieldDecl>("datatype entity", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                        const mfinfo = this.getCurrentSrcInfo();

                        this.ensureToken(TokenStrings.Identifier, "datatype entity field");
                        const name = this.consumeTokenAndGetValue();
                        this.ensureAndConsumeToken(SYM_colon, "datatype entity field");

                        const ttype = this.parseTypeSignature();
                        return new MemberFieldDecl(mfinfo, this.m_penv.getCurrentFile(), [], name, ttype);
                    });
                }
                else {
                    this.setRecover(this.scanCodeParens());
                    this.ensureAndConsumeToken(SYM_lbrace, "datatype entry");

                    const thisType = new NominalTypeSignature(esinfo, currentDecl.ns, [ename], []);

                    const nestedEntities = new Map<string, EntityTypeDecl>();
                    const statuseffect = new TaskStatusEffect([]);
                    const eventeffect = new TaskEventEffect([]);
                    const enveffect = new TaskEnvironmentEffect([]);
                    this.parseOOPMembersCommon(esinfo, false, thisType, currentDecl, [ename], [...terms], new Set<string>(terms.map((tt) => tt.name)), nestedEntities, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, [], statuseffect, eventeffect, enveffect, []);

                    this.ensureAndConsumeToken(SYM_rbrace, "datatype entry");
                }
            }

            const eprovides = [[concepttype, undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            const edecl = new EntityTypeDecl(esinfo, this.m_penv.getCurrentFile(), ["__adt_entity_type"], currentDecl.ns, ename, terms, eprovides, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, new Map<string, EntityTypeDecl>());

            edecls.push(edecl);
            currentDecl.objects.set(ename, edecl);
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + ename, currentDecl.objects.get(ename) as EntityTypeDecl);
        }

        if (this.testAndConsumeTokenIf(SYM_amp)) {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken(SYM_lbrace, "datatype");

            if (complexheader) {
                this.raiseError(this.getCurrentLine(), "Cannot define complex ADT++ concept in multiple parts");
            }

            const thisType = new NominalTypeSignature(sinfo, currentDecl.ns, [iname], []);

            const nestedEntities = new Map<string, EntityTypeDecl>();
            const memberFields: MemberFieldDecl[] = [];
            const statuseffect = new TaskStatusEffect([]);
            const eventeffect = new TaskEventEffect([]);
            const enveffect = new TaskEnvironmentEffect([]);
            this.parseOOPMembersCommon(sinfo, false, thisType, currentDecl, [iname], [...terms], new Set<string>(terms.map((tt) => tt.name)), nestedEntities, cinvariants, cvalidates, cstaticMembers, cstaticFunctions, memberFields, cmemberMethods, [], statuseffect, eventeffect, enveffect, []);

            if (cusing.length !== 0 && memberFields.length !== 0) {
                this.raiseError(this.getCurrentLine(), "Cannot define fields in multiple places in ADT++ decl");
            }
            cusing = [...cusing, ...memberFields];

            this.ensureAndConsumeToken(SYM_rbrace, "datatype");

            if (currentDecl.checkDeclNameClash(iname)) {
                this.raiseError(line, "Collision between concept and other names");
            }

            this.clearRecover();
        }
        else {
            this.ensureAndConsumeToken(SYM_semicolon, "datatype");
        }

        //
        //TODO: may want to do a bit more linking of adt concept and entities for things like exhaustive checking
        //

        const cdecl = new ConceptTypeDecl(sinfo, this.m_penv.getCurrentFile(), ["__adt_concept_type"], currentDecl.ns, iname, terms, provides, cinvariants, cvalidates, cstaticMembers, cstaticFunctions, cusing, cmemberMethods, new Map<string, EntityTypeDecl>());
        currentDecl.concepts.set(iname, cdecl);
        this.m_penv.assembly.addConceptDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + iname, cdecl);
    }

    private parseNamespaceConst(currentDecl: NamespaceDeclaration) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] const NAME = exp;
        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken(KW_const, "namespace const declaration");
        this.ensureToken(TokenStrings.Identifier, "namespace const declaration");
        const gname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(SYM_colon, "namespace const declaration");
        const gtype = this.parseTypeSignature();

        this.ensureAndConsumeToken(SYM_eq, "namespace const declaration");
        const value = this.parseConstExpression(false);

        this.ensureAndConsumeToken(SYM_semicolon, "namespace const declaration");

        if (currentDecl.checkDeclNameClash(gname)) {
            this.raiseError(this.getCurrentLine(), "Collision between global and other names");
        }

        currentDecl.consts.set(gname, new NamespaceConstDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, gname, gtype, value));
    }

    private parseNamespaceFunction(currentDecl: NamespaceDeclaration) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] function NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken(KW_function, "namespace function declaration");
        this.ensureToken(TokenStrings.Identifier, "namespace function declaration");
        const fname = this.consumeTokenAndGetValue();

        const terms = this.parseTermDeclarations();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(InvokableKind.Basic, Parser.attributeSetContains("opaque", attributes), attributes, recursive, terms, [], undefined, false);

        currentDecl.functions.set(fname, new NamespaceFunctionDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, fname, sig));
    }

    private parseEndOfStream() {
        if(!this.testToken(TokenStrings.EndOfStream)) {
            this.raiseError(this.getCurrentLine(), "Expected end-of-file");
        }

        this.consumeToken();
    }

    ////
    //Public methods
    parseCompilationUnitGetNamespaceDeps(file: string, contents: string, macrodefs: string[]): {ns: string, deps: string[], remap: Map<string, string>} | undefined {
        this.setNamespaceAndFile("[No Namespace]", file);

        const lexer = new Lexer(contents, macrodefs, undefined);
        this.initialize(lexer.lex());

        //namespace NS; ...
        this.ensureAndConsumeToken(KW_namespace, "missing namespace declaration");
        this.ensureToken(TokenStrings.ScopeName, "namespace declaration");
        const ns = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(SYM_semicolon, "namespace declaration");

        this.setNamespaceAndFile(ns, file);

        let deps: string[] = [];
        let remap = new Map<string, string>();
        while (this.m_cpos < this.m_epos) {
            try {
                this.m_cpos = this.scanTokenOptions("import");
                if (this.m_cpos === this.m_epos) {
                    break;
                }

                const dep = this.parseNamespaceDep();
                deps.push(dep.fromns);
                remap.set(dep.asns, dep.fromns);
            }
            catch(ex) {
                return undefined;
            }
        }

        return {ns: ns, deps: deps, remap: remap};
    }

    parseCompilationUnitPass1(file: string, contents: string, macrodefs: string[]): boolean {
        this.setNamespaceAndFile("[No Namespace]", file);

        const lexer = new Lexer(contents, macrodefs, undefined);
        this.initialize(lexer.lex());

        //namespace NS; ...
        this.ensureAndConsumeToken(KW_namespace, "namespace declaration");
        this.ensureToken(TokenStrings.ScopeName, "namespace declaration");
        const ns = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(SYM_semicolon, "namespace declaration");

        this.setNamespaceAndFile(ns, file);
        const nsdecl = this.m_penv.assembly.ensureNamespace(ns);

        let parseok = true;
        while (this.m_cpos < this.m_epos) {
            try {
                this.m_cpos = this.scanTokenOptions(...NS_KW);
                if (this.m_cpos === this.m_epos) {
                    const tokenIndexBeforeEOF = this.m_cpos - 2;
                    if (tokenIndexBeforeEOF >= 0 && tokenIndexBeforeEOF < this.m_tokens.length) {
                        const tokenBeforeEOF = this.m_tokens[tokenIndexBeforeEOF];
                        if (tokenBeforeEOF.kind === TokenStrings.Error) {
                            this.raiseError(tokenBeforeEOF.line, `Expected */ but found EOF`);
                        }
                    }
                    break;
                }

                const op = this.peekToken();
                if(this.testToken(KW_import)) {
                    this.consumeToken();
                    //then don't care about the rest of the usings
                }
                else if (this.testToken(KW_function)  || this.testToken(KW_const) || this.testToken(KW_format)) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Identifier, op);
                    const fname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(fname)) {
                        this.raiseError(this.getCurrentLine(), `Duplicate definition of name "${fname}"`);
                    }

                    nsdecl.declaredNames.add(fname);
                }
                else if(this.testToken(KW_logmsg) || this.testToken(KW_eventmsg) || this.testToken(KW_statusmsg)) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Type, op);
                    const tname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), `Duplicate definition of name "${tname}"`);
                    }

                    nsdecl.declaredNames.add(tname);
                }
                else if (this.testToken(KW_operator)) {
                    this.consumeToken();

                    let nns = ns;
                    if (this.testToken(TokenStrings.ScopeName)) {
                        nns = this.consumeTokenAndGetValue();
                        this.ensureAndConsumeToken(SYM_coloncolon, op);
                    }

                    const fname = this.consumeTokenAndGetValue();

                    if (nns === ns) {
                        nsdecl.declaredNames.add(fname);
                    }
                }
                else if (this.testToken(KW_typedef)) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.ScopeName, op);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), `Duplicate definition of name "${tname}"`);
                    }
                    nsdecl.declaredNames.add(tname);
                }
                else if (this.testToken(KW_typedecl)) {            
                    this.consumeToken();

                    this.ensureToken(TokenStrings.ScopeName, op);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), `Duplicate definition of name "${tname}"`);
                    }
                    nsdecl.declaredNames.add(tname);

                    this.ensureAndConsumeToken(SYM_eq, op);
                    if (this.testToken(TokenStrings.Regex)) {
                        this.consumeToken();
                        this.ensureAndConsumeToken(SYM_semicolon, op);
                    }
                    else {
                        if (this.testAndConsumeTokenIf(SYM_amp)) {
                            this.ensureToken(SYM_lbrace, op); //we should be at the opening left paren 
                            this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                        }
                    }
                }
                else if (this.testToken(KW_datatype)) {            
                    this.consumeToken();

                    this.ensureToken(TokenStrings.ScopeName, op);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), `Duplicate definition of name "${tname}"`);
                    }
                    nsdecl.declaredNames.add(tname);

                    //[attr] typedecl NAME<...> [provides ... ] [using {...}] of
                    // Foo {...}
                    // | ...
                    // [& {...}] | ;

                    this.parseProvides(this.getCurrentSrcInfo(), false /*Doesn't matter since we arejust scanning*/, [KW_of, KW_using]);

                    if (this.testAndConsumeTokenIf(KW_using)) {
                        this.ensureToken(SYM_lbrace, op); //we should be at the opening left paren 
                        this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                    }

                    this.ensureAndConsumeToken(KW_of, op);

                    while (!this.testToken(SYM_semicolon) && !this.testToken(SYM_amp)) {
                        if (this.testToken(SYM_bar)) {
                            this.consumeToken();
                        }

                        this.ensureToken(TokenStrings.ScopeName, op);
                        const ename = this.consumeTokenAndGetValue();

                        if (!lexer.isDeclTypeName(ename)) {
                            this.raiseError(this.getCurrentLine(), `Not a valid type name "${ename}" to define`);
                        }
                        if (nsdecl.declaredNames.has(ename)) {
                            this.raiseError(this.getCurrentLine(), `Duplicate definition of name "${ename}"`);
                        }
                        nsdecl.declaredNames.add(ename);

                        if (this.testToken(SYM_lbrace)) {
                            this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                        }
                    }

                    if (this.testAndConsumeTokenIf(SYM_amp)) {
                        this.ensureToken(SYM_lbrace, op); //we should be at the opening left paren 
                        this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                    }
                    else {
                        this.ensureAndConsumeToken(SYM_semicolon, op);
                    }
                }
                else if (this.testToken(KW_enum)) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.ScopeName, op);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), `Not a valid type name "${tname}" to define`);
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), `Duplicate definition of name "${tname}"`);
                    }
                    nsdecl.declaredNames.add(tname);

                    this.ensureToken(SYM_lbrace, op); //we should be at the opening left paren 
                    this.m_cpos = this.scanCodeParens(); //scan to the closing paren

                    if (this.testToken(SYM_amp)) {
                        this.ensureToken(SYM_rbrace, op); //we should be at the opening left paren 
                        this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                    }
                }
                else if (this.testToken(KW_concept) || this.testToken(KW_entity)) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.ScopeName, op);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), `Not a valid type name "${tname}" to define`);
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), `Duplicate definition of name "${tname}"`);
                    }
                    nsdecl.declaredNames.add(tname);

                    this.parseTermDeclarations();
                    this.parseProvides(this.getCurrentSrcInfo(), ns === "Core", [SYM_lbrace]);
            
                    this.ensureToken(SYM_lbrace, op); //we should be at the opening left paren 
                    this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                }
                else {
                    this.raiseError(this.getCurrentLine(), "Failed to parse top-level namespace declaration");
                }
            }
            catch (ex) {
                this.m_cpos++;
                parseok = false;
            }
        }

        return parseok;
    }

    parseCompilationUnitPass2(file: string, contents: string, macrodefs: string[], namespacestrings: Set<string>): boolean {
        this.setNamespaceAndFile("[No Namespace]", file);
        const lexer = new Lexer(contents, macrodefs, namespacestrings);
        this.initialize(lexer.lex());

        //namespace NS; ...
        this.ensureAndConsumeToken("namespace", "namespace declaration");
        this.ensureToken(TokenStrings.Namespace, "namespace declaration");
        const ns = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(SYM_semicolon, "namespace declaration");

        this.setNamespaceAndFile(ns, file);
        const nsdecl = this.m_penv.assembly.ensureNamespace(ns);

        let importok = true;
        let parseok = true;
        while (this.m_cpos < this.m_epos) {
            const rpos = this.scanTokenOptions(...NS_KW, TokenStrings.EndOfStream);

            try {
                if (rpos === this.m_epos) {
                    break;
                }

                const tk = this.m_tokens[rpos].kind;
                importok = importok && tk === KW_import;
                if (tk === KW_import) {
                    if (!importok) {
                        this.raiseError(this.getCurrentLine(), "Using statements must come before other declarations");
                    }

                    this.parseNamespaceUsing(nsdecl);
                }
                else if (tk === KW_function) {
                    this.parseNamespaceFunction(nsdecl);
                }
                else if (tk === KW_operator) {
                    this.parseNamespaceOperator(nsdecl);
                }
                else if (tk === KW_const) {
                    this.parseNamespaceConst(nsdecl);
                }
                else if(this.testToken(KW_logmsg)) {
                    this.parseNamespaceLogMsg(nsdecl);
                }
                else if(this.testToken(KW_eventmsg)) {
                    this.parseNamespaceEventMsg(nsdecl);
                }
                else if(this.testToken(KW_statusmsg)) {
                    this.parseNamespaceStatusMsg(nsdecl);
                }
                else if(this.testToken(KW_format)) {
                    this.parseNamespaceFormatString(nsdecl);
                }
                else if (tk === KW_typedef) {
                    this.parseNamespaceTypedef(nsdecl);
                }
                else if (tk === KW_concept) {
                    this.parseConcept(nsdecl);
                }
                else if (tk === KW_entity) {
                    this.parseObject(nsdecl, undefined, [], []);
                }
                else if (tk === KW_enum) {
                    this.parseEnum(nsdecl);
                }
                else if (tk === KW_typedecl) {
                    this.parseTypeDecl(nsdecl);
                }
                else if (tk === KW_datatype) {
                    this.parseDataTypeDecl(nsdecl);
                }
                else if (tk === TokenStrings.EndOfStream) {
                    this.parseEndOfStream();
                }
                else {
                    this.raiseError(this.getCurrentLine(), "Invalid top-level definiton");
                }
            }
            catch (ex) {
                this.m_cpos = rpos + 1;
                parseok = false;
            }
        }

        return parseok;
    }

    getParseErrors(): [string, number, string][] | undefined {
        return this.m_errors.length !== 0 ? this.m_errors : undefined;
    }
}

export { 
    ParseError, Parser
};
