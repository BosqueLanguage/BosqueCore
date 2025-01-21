"use strict;"


////////////////////////////////////////////////////////////////////////////////
//Support

function SourceInfo(line, column, pos, span) {
    this.line = line;
    this.column = column;
    this.pos = pos;
    this.span = span;
}

function Token(line, column, cpos, span, kind, data) {
    this.line = line;
    this.column = column;
    this.pos = cpos;
    this.span = span;
    this.kind = kind;
    this.data = data;
}
Token.prototype.getSourceInfo = function() {
    return new SourceInfo(this.line, this.column, this.pos, this.span);
}

function ParserError(sinfo, message) {
    this.sinfo = sinfo;
    this.message = message;
}

const TokenStrings = {
    Clear: "[CLEAR]",
    Error: "[ERROR]",

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
    CString: "[LITERAL_EX_STRING]",
    TemplateString: "[LITERAL_TEMPLATE_STRING]",
    TemplateCString: "[LITERAL_TEMPLATE_EX_STRING]",

    Regex: "[LITERAL_REGEX]",
    PathItem: "[LITERAL_PATH_ITEM]",
    PathTemplateItem: "[LITERAL_TEMPLATE_PATH_ITEM]",

    TZDateTime: "[LITERAL_TZTIME]",
    TAITime: "[LITERAL_TAI_TIME]",
    PlainDate: "[LITERAL_PLAIN_DATE]",
    PlainTime: "[LITERAL_PLAIN_TIME]",
    LogicalTime: "[LITERAL_LOGICAL_TIME]",
    Timestamp: "[LITERAL_TIMESTAMP]",

    DeltaDateTime: "[LITERAL_DELTA_DATETIME]",
    DeltaSeconds: "[LITERAL_DELTA_SECONDS]",
    DeltaLogicalTime: "[LITERAL_DELTA_LOGICAL_TIME]",
    DeltaTimestamp: "[LITERAL_DELTA_TIMESTAMP]",

    IdentifierName: "[IDENTIFIER]",
    Attribute: "[ATTRIBUTE]",

    EndOfStream: "[EOS]"
};

////////////////////////////////////////////////////////////////////////////////
//Keywords

const KW_SRC = "$src";
const KW_none = "none";
const KW_true = "true";
const KW_false = "false";
const KW_SOME = "some";
const KW_OK = "ok";
const KW_FAIL = "fail";
const KW_LET = "let";
const KW_IN = "in";

const KeywordStrings = [
    KW_SRC,
    KW_none,
    KW_true,
    KW_false,
    KW_SOME,
    KW_OK,
    KW_FAIL,
    KW_LET,
    KW_IN
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });

////////////////////////////////////////////////////////////////////////////////
//Symbols

const SYM_lbrack = "[";
const SYM_lparen = "(";
const SYM_lbrace = "{";
const SYM_lbrackbar = "[|";
const SYM_lparenbar = "(|";

const SYM_rbrack = "]";
const SYM_rparen = ")";
const SYM_rbrace = "}";
const SYM_rbrackbar = "|]";
const SYM_rparenbar = "|)";
const SYM_langle = "<";
const SYM_rangle = ">";

const SYM_coloncolon = "::";
const SYM_hash = "#";
const SYM_bigarrow = " => ";
const SYM_colon = ":";
const SYM_coma = ",";
const SYM_dot = ".";
const SYM_eq = "=";

const StandardSymbols = [
    SYM_colon,
    SYM_coloncolon,
    SYM_coma,
    SYM_dot,
    SYM_eq,
    SYM_HOLE,
    
    SYM_hash,
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });

const SpaceRequiredSymbols = [
    SYM_bigarrow,
].map((s) => { return s.trim(); })
.sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });

const ParenSymbols = [
    SYM_lbrack,
    SYM_lparen,
    SYM_lbrace,
    SYM_lbrackbar,
    SYM_lparenbar,
    SYM_langle,

    SYM_rbrack,
    SYM_rparen,
    SYM_rbrace,
    SYM_rparenbar,
    SYM_rbrackbar,
    SYM_rangle

].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });

////////////////////////////////////////////////////////////////////////////////
//BSQON Lexer and parser

const _s_whitespaceRe = new RegExp('\\s+', "y");

function BSQONLexer(input) {
    this.input = input;
    this.jsStrPos = 0;
    
    this.cline = 0;
    this.linestart = 0;
    
    this.tokens = [];
}
BSQONLexer.prototype.advancePosition = function(epos) {
    this.jsStrPos += epos - this.jsStrPos;
}
BSQONLexer.prototype.trylex = function(re) {
    re.lastIndex = this.jsStrPos;
    const mm = re.exec(this.input);
    if(mm === null) {
        return null;
    }
    else {
        return mm[0];
    }
}
BSQONLexer.prototype.trylexWSPlus = function(options, suffix) {
    Lexer._s_whitespaceRe.lastIndex = this.jsStrPos;
    const mmpre = Lexer._s_whitespaceRe.exec(this.input);
    if(mmpre === null) {
        return null;
    }
    
    const mopt = options.find((opt) => this.input.startsWith(opt, this.jsStrPos + mmpre[0].length));
    if(mopt === undefined) {
        return null;
    }

    suffix.lastIndex = this.jsStrPos + mmpre[0].length + mopt.length;
    const mmsuf = suffix.exec(this.input);
    if(mmsuf === null) {
        return null;
    }

    return this.input.slice(this.jsStrPos, this.jsStrPos + mmpre[0].length + mopt.length + mmsuf[0].length);
}
pushError(sinfo: SourceInfo, message: string) {
    const cmode = this.scanmode[this.scanmode.length - 1];
    if(cmode === LexerStateScanMode.Enabled || cmode === LexerStateScanMode.EnabledIf || cmode === LexerStateScanMode.EnabledElse) {
        this.errors.push(new ParserError(this.srcfile, sinfo, message));
    }
}

pushToken(token: Token) {
    const cmode = this.scanmode[this.scanmode.length - 1];
    if(cmode === LexerStateScanMode.Enabled || cmode === LexerStateScanMode.EnabledIf || cmode === LexerStateScanMode.EnabledElse) {
        this.tokens.push(token);
    }
}

private recordLexToken(jsepos: number, kind: string) {
    this.pushToken(new Token(this.cline, this.jsStrPos - this.linestart, this.jsStrPos, jsepos - this.jsStrPos, kind, kind)); //set data to kind string
    this.advancePosition(jsepos);
}

private recordLexTokenWData(jsepos: number, kind: string, data: string) {
    this.pushToken(new Token(this.cline, this.jsStrPos - this.linestart, this.jsStrPos, jsepos - this.jsStrPos, kind, data));
    this.advancePosition(jsepos);
}

private updatePositionInfo(jspos: number, jepos: number) {
    for (let i = jspos; i < jepos; ++i) {
        if (this.input[i] === "\n") {
            this.cline++;
            this.linestart = i + 1;
        }
    }
}