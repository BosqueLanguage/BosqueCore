"use strict;"

import { validateStringLiteral, escapeStringLiteral, validateCStringLiteral, escapeCStringLiteral } from "@bosque/jsbrex";

////////////////////////////////////////////////////////////////////////////////
//Support

let _$none_lit = null;
let _$parsemap = {};
let _$emitmap = {};

function resolveParseMapEntry(name) {
    return _$parsemap[name];
}

function NOT_IMPLEMENTED(name) {
    throw new ParseError(new SourceInfo(0, 0, 0, 0) `Not implemented: ${name}`);
}

const s_coreTypes = {
    "None": true, 
    "Bool": true, 
    "Nat": true, 
    "Int": true, 
    "BigInt": true, 
    "BigNat": true, 
    "Rational": true, 
    "Float": true, 
    "Decimal": true, 
    "DecimalDegree": true, 
    "LatLongCoordinate": true, 
    "Complex": true,
    "ByteBuffer": true, 
    "UUIDv4": true, 
    "UUIDv7": true, 
    "SHAContentHash": true, 
    "TZDateTime": true, 
    "TAITime": true, 
    "PlainDate": true, 
    "PlainTime": true, 
    "LogicalTime": true, 
    "ISOTimestamp": true,
    "DeltaDateTime": true, 
    "DeltaSeconds": true, 
    "DeltaLogicalTime": true, 
    "DeltaISOTimestamp": true,
    "String": true, 
    "CString": true, 
    "CChar": true,
    "UnicodeChar": true,
    "Regex": true, 
    "CRegex": true, 
    "PathRegex": true,
    "Path": true, 
    "PathItem": true, 
    "Glob": true
};

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

    CChar: "[LITERAL_CCHAR]",
    UnicodeChar: "[LITERAL_UNICODECHAR]",

    String: "[LITERAL_STRING]",
    CString: "[LITERAL_EX_STRING]",

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


const s_typeTokens = [
    TokenStrings.IdentifierName, 
    SYM_coloncolon, 
    SYM_langle,
    SYM_rangle,
    SYM_lparenbar,
    SYM_rparenbar,
    SYM_coma
];

function isTypeIdentifierName(nstr) {
    return /^[A-Z][_a-zA-Z0-9]+$/.test(nstr);
}

////////////////////////////////////////////////////////////////////////////////
//BSQON Lexer and parser

const _s_whitespaceRe = new RegExp('\\s+', "y");

const _s_nonzeroIntValNoSign = '[1-9][0-9]*';
const _s_nonzeroIntVal = `[+-]?${_s_nonzeroIntValNoSign}`;
const _s_intValueNoSign = `(0|${_s_nonzeroIntValNoSign})`;
const _s_intValue = `(0|[+]0|${_s_nonzeroIntVal})`;

const _s_floatValueNoSign = '[0-9]+[.][0-9]+([eE][-+]?[0-9]+)?';
const _s_floatValue = `[+-]?${_s_floatValueNoSign}([eE][-+]?[0-9]+)?`;

const _s_floatSimpleValueNoSign = '[0-9]+[.][0-9]+';
const _s_floatSimpleValue = `[+-]?${_s_floatSimpleValueNoSign}`;

const _s_intNumberinoRe = new RegExp(`${_s_intValue}`, "y");

const _s_intRe = new RegExp(`(${_s_intValue})i`, "y");
const _s_natRe = new RegExp(`(${_s_intValue})n`, "y");
const _s_bigintRe = new RegExp(`(${_s_intValue})I`, "y");
const _s_bignatRe = new RegExp(`(${_s_intValue})N`, "y");

const _s_floatRe = new RegExp(`(${_s_floatValue})f`, "y");

/*
    private static readonly _s_decimalRe = new RegExp(`(${Lexer._s_floatValue})d`, "y");
    private static readonly _s_rationalRe = new RegExp(`(${Lexer._s_intValue})(/(${Lexer._s_nonzeroIntValNoSign}))?R`, "y");
    private static readonly _s_complexRe = new RegExp(`(${Lexer._s_floatValue})[+-](${Lexer._s_floatValueNoSign})j`, "y");

    private static readonly _s_decimalDegreeRe = new RegExp(`(${Lexer._s_floatSimpleValue})dd`, "y");
    private static readonly _s_latlongRe = new RegExp(`(${Lexer._s_floatSimpleValue})lat[+-]${Lexer._s_floatSimpleValueNoSign}long`, "y");
    
    private static readonly _s_logicaltimeRe = new RegExp(`(${Lexer._s_intValue})l`, "y");

    private static readonly _s_deltasecondsRE = new RegExp(`[+-](${Lexer._s_floatValueNoSign})ds`, "y");
    private static readonly _s_deltalogicaltimeRE = new RegExp(`[+-](${Lexer._s_intValueNoSign})dl`, "y");

    private static readonly _s_zerodenomRationalNumberinoRe = new RegExp(`(${Lexer._s_intValue})/0`, "y");
    private static readonly _s_zerodenomRationalRe = new RegExp(`(${Lexer._s_intValue})/0R`, "y");

    private static _s_bytebufferRe = new RegExp('0x\\[[0-9a-fA-F]+\\]', "y");
    private static _s_uuidRe = new RegExp('uuid[47]\\{[a-fA-F0-9]{8}-[a-fA-F0-9]{4}-[a-fA-F0-9]{4}-[a-fA-F0-9]{4}-[a-fA-F0-9]{12}\\}', "y");
    private static _s_shaRe = new RegExp('sha3\\{[a-fA-F0-9]{64}\\}', "y");
*/

const _s_validCStringChars = /^[ -~\t\n]*$/;
const _s_validRegexChars = /([!-.0-~]|\s)+/;

/*
    private static _s_datevalue = '([0-9]{4})-([0-9]{2})-([0-9]{2})';
    private static _s_timevalue = '([0-9]{2}):([0-9]{2}):([0-9]{2})';
    private static _s_tzvalue = '((\{[a-zA-Z0-9/, _-]+\})|[A-Z]+)';

    private static _s_datatimeRE = new RegExp(`${Lexer._s_datevalue}T${Lexer._s_timevalue}@${Lexer._s_tzvalue}`, "y");
    private static _s_taitimeRE = new RegExp(`${Lexer._s_datevalue}T${Lexer._s_timevalue}?`, "y");
    private static _s_plaindateRE = new RegExp(`${Lexer._s_datevalue}`, "y");
    private static _s_plaintimeRE = new RegExp(`${Lexer._s_timevalue}`, "y");
    private static _s_timestampRE = new RegExp(`${Lexer._s_datevalue}T${Lexer._s_timevalue}[.]([0-9]{3})Z`, "y");
*/


const _s_identiferName = new RegExp('[$]?[_a-zA-Z][_a-zA-Z0-9]*', "y");

const _s_redundantSignRE = /[+-]{2,}/y;

const MIN_SAFE_INT = -4611686018427387903n;
const MAX_SAFE_INT = 4611686018427387903n;

//negation and conversion are always safe
const MAX_SAFE_NAT = 4611686018427387903n;

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
/**
 * @param {RegExp} re
 * @returns {string | null}
 */
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
/**
 * 
 * @param {string[]} options 
 * @param {RegExp} suffix 
 * @returns {string | null}
 */
BSQONLexer.prototype.trylexWSPlus = function(options, suffix) {
    _s_whitespaceRe.lastIndex = this.jsStrPos;
    const mmpre = _s_whitespaceRe.exec(this.input);
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
/**
 * @param {SourceInfo} sinfo 
 * @param {string} message 
 * @throws {ParserError}
 */
BSQONLexer.prototype.raiseError = function(sinfo, message) {
    throw new ParserError(sinfo, message);
}
/**
 * @param {number} jsepos
 * @param {string} kind
 * @returns {Token}
 */
BSQONLexer.prototype.recordLexToken = function(jsepos, kind) {
    this.tokens.push(new Token(this.cline, this.jsStrPos - this.linestart, this.jsStrPos, jsepos - this.jsStrPos, kind, kind)); //set data to kind string
    this.advancePosition(jsepos);
}
/**
 * @param {number} jsepos
 * @param {string} kind
 * @param {string} data
 * @returns {Token}
 */
BSQONLexer.prototype.recordLexTokenWData = function(jsepos, kind, data) {
    this.tokens.push(new Token(this.cline, this.jsStrPos - this.linestart, this.jsStrPos, jsepos - this.jsStrPos, kind, data));
    this.advancePosition(jsepos);
}
/**
 * @param {number} jspos
 * @param {number} jepos
 * @returns {void}
 */
BSQONLexer.prototype.updatePositionInfo = function(jspos, jepos) {
    for (let i = jspos; i < jepos; ++i) {
        if (this.input[i] === "\n") {
            this.cline++;
            this.linestart = i + 1;
        }
    }
}
/**
 * @returns {boolean}
 */
BSQONLexer.prototype.tryLexWS = function() {
    const arop = this.trylexWSPlus(SpaceRequiredSymbols, _s_whitespaceRe);
    if (arop !== null) {
        return false;
    }

    const m = this.trylex(_s_whitespaceRe);
    if (m === null) {
        return false;
    }

    this.updatePositionInfo(this.jsStrPos, this.jsStrPos + m.length);
    this.advancePosition(this.jsStrPos + m.length);

    return true;
}
/**
 * @returns {boolean}
 */
BSQONLexer.prototype.tryLexLineComment = function() {
    const m = this.input.startsWith("%%", this.jsStrPos);
    if (!m) {
        return false;
    }

    let jepos = this.input.indexOf("\n", this.jsStrPos);

    if (jepos === -1) {
        this.updatePositionInfo(this.jsStrPos, this.input.length);
        this.advancePosition(this.input.length);
    }
    else {
        jepos++;

        this.updatePositionInfo(this.jsStrPos, jepos);
        this.advancePosition(jepos);
    }

    return true;
}
/**
 * @returns {void}
 * @throws {ParserError}
 */
BSQONLexer.prototype.checkRedundantSigns = function() {
    if(this.jsStrPos !== this.input.length && (this.input[this.jsStrPos] === "+" || this.input[this.jsStrPos] === "-")) {
        _s_redundantSignRE.lastIndex = this.jsStrPos;
        const mm = _s_redundantSignRE.exec(this.input);
        if(mm !== null) {
            this.raiseError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, mm[0].length), "Redundant sign in number");
        }
    }
}
/**
 * @returns {boolean}
 */
BSQONLexer.prototype.tryLexFloatCompositeLikeToken = function() {
    return false;
}
/**
 * @returns {boolean}
 */
BSQONLexer.prototype.tryLexFloatLikeToken = function() {
    const mfloat = this.trylex(_s_floatRe);
    if(mfloat !== null) {
        this.recordLexTokenWData(this.jsStrPos + mfloat.length, TokenStrings.Float, mfloat);
        return true;
    }

    return false;
}
/**
 * @returns {boolean}
 */
BSQONLexer.prototype.tryLexIntegralCompositeLikeToken = function() {
    return false;
}
/**
 * @returns {boolean}
 */
BSQONLexer.prototype.tryLexIntegralLikeToken = function() {
    const mint = this.trylex(_s_intRe);
    if(mint !== null) {
        this.recordLexTokenWData(this.jsStrPos + mint.length, TokenStrings.Int, mint);
        return true;
    }

    const mnat = this.trylex(_s_natRe);
    if(mnat !== null) {
        this.recordLexTokenWData(this.jsStrPos + mnat.length, TokenStrings.Nat, mnat);
        return true;
    }

    const mbigint = this.trylex(_s_bigintRe);
    if(mbigint !== null) {
        this.recordLexTokenWData(this.jsStrPos + mbigint.length, TokenStrings.BigInt, mbigint);
        return true;
    }

    const mbignat = this.trylex(_s_bignatRe);
    if(mbignat !== null) {
        this.recordLexTokenWData(this.jsStrPos + mbignat.length, TokenStrings.BigNat, mbignat);
        return true;
    }

    const mnumberino = this.trylex(_s_intNumberinoRe);
    if(mnumberino !== null) {
        this.recordLexTokenWData(this.jsStrPos + mnumberino.length, TokenStrings.NumberinoInt, mnumberino);
        return true;
    }

    return false;
}
/**
 * @returns {boolean}
 * @throws {ParserError}
 */
BSQONLexer.prototype.tryLexNumberLikeToken = function() {
    this.checkRedundantSigns();

    const cft = this.tryLexFloatCompositeLikeToken();
    if(cft) {
        return true;
    }
    
    const ft = this.tryLexFloatLikeToken();
    if(ft) {
        return true;
    }

    const cit = this.tryLexIntegralCompositeLikeToken();
    if(cit) {
        return true;
    }

    const it = this.tryLexIntegralLikeToken();
    if(it) {
        return true;
    }

    return false;
}
/**
 * @returns {boolean}
 */
BSQONLexer.prototype.tryLexByteBuffer = function() {
    return false;
}
/**
 * @returns {boolean}
 */
BSQONLexer.prototype.tryLexUUID = function() {
    return false;
}
/**
 * @returns {boolean}
 */
BSQONLexer.prototype.tryLexHashCode = function() {
    return false;
}
/**
 * @returns {boolean}
 * @throws {ParserError}
 */
BSQONLexer.prototype.tryLexCChar = function() {
    if(!this.input.startsWith('b\'', this.jsStrPos)) {
        return false;
    }

    let ncpos = this.jsStrPos + 2;
        
    let jepos = this.input.indexOf("'", ncpos);
    if(jepos === -1) {
        this.raiseError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, this.input.length - this.jsStrPos), "Unterminated CChar literal");
    }
    
    const mstr = this.input.slice(ncpos, jepos);
    if(!_s_validCStringChars.test(mstr)) {
        this.raiseError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, jepos - this.jsStrPos), "Invalid chacaters in CChar literal");
    }

    if((jepos - ncpos) > 1) {
        this.raiseError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, jepos - this.jsStrPos), "More than one character detected in CChar literal");
    }

    jepos++;
    let strval = this.input.slice(this.jsStrPos, jepos);

    this.updatePositionInfo(this.jsStrPos, jepos);
    this.recordLexTokenWData(jepos, TokenStrings.CChar, strval);
    return true;
}
/**
 * @returns {boolean}
 * @throws {ParserError}
 */
BSQONLexer.prototype.tryLexUnicodeChar = function() {
    if(!this.input.startsWith('u\'', this.jsStrPos)) {
        return false;
    }

    let ncpos = this.jsStrPos + 2;
        
    let jepos = this.input.indexOf("'", ncpos);
    if(jepos === -1) {
        this.raiseError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, this.input.length - this.jsStrPos), "Unterminated UnicodeChar literal");
    }
    
    const mstr = this.input.slice(ncpos, jepos);
    if(!_s_validCStringChars.test(mstr)) {
        this.raiseError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, jepos - this.jsStrPos), "Invalid chacaters in UnicodeChar literal");
    }

    if((jepos - ncpos) > 1) {
        this.raiseError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, jepos - this.jsStrPos), "More than one character detected in UnicodeChar literal");
    }

    jepos++;
    let strval = this.input.slice(this.jsStrPos, jepos);

    this.updatePositionInfo(this.jsStrPos, jepos);
    this.recordLexTokenWData(jepos, TokenStrings.UnicodeChar, strval);
    return true;
}
/**
 * @returns {boolean}
 * @throws {ParserError}
 */
BSQONLexer.prototype.tryLexUnicodeString = function() {
    if(!this.input.startsWith('"', this.jsStrPos)) {
        return false;
    }

    let ncpos = this.jsStrPos + 1;
    
    let jepos = this.input.indexOf('"', ncpos);
    if(jepos === -1) {
        this.raiseError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, this.input.length - this.jsStrPos), "Unterminated string literal");
    }

    jepos++;
    let strval = this.input.slice(this.jsStrPos, jepos);

    this.updatePositionInfo(this.jsStrPos, jepos);
    this.recordLexTokenWData(jepos, TokenStrings.String, strval);
    return true;
}
/**
 * @returns {boolean}
 * @throws {ParserError}
 */
BSQONLexer.prototype.tryLexCString = function() {
    if(!this.input.startsWith('\'', this.jsStrPos)) {
        return false;
    }

    let ncpos = this.jsStrPos + 1;
        
    let jepos = this.input.indexOf("'", ncpos);
    if(jepos === -1) {
        this.raiseError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, this.input.length - this.jsStrPos), "Unterminated CString literal");
    }
    
    const mstr = this.input.slice(ncpos, jepos);
    if(!_s_validCStringChars.test(mstr)) {
        this.raiseError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, jepos - this.jsStrPos), "Invalid chacaters in CString literal");
    }

    jepos++;
    let strval = this.input.slice(this.jsStrPos, jepos);

    this.updatePositionInfo(this.jsStrPos, jepos);
    this.recordLexTokenWData(jepos, TokenStrings.CString, strval);
    return true;
}
/**
 * @returns {boolean}
 * @throws {ParserError}
 */
BSQONLexer.prototype.tryLexCharLike = function() {
    const cc = this.tryLexCChar();
    if(cc) {
        return true;
    }

    const uc = this.tryLexUnicodeChar();
    if(uc) {
        return true;
    }

    return false;
}
/**
 * @returns {boolean}
 * @throws {ParserError}
 */
BSQONLexer.prototype.tryLexStringLike = function() {
    const us = this.tryLexUnicodeString();
    if(us) {
        return true;
    }

    const as = this.tryLexCString();
    if(as) {
        return true;
    }

    return false;
}
/**
 * @returns {boolean}
 * @throws {ParserError}
 */
BSQONLexer.prototype.tryLexRegex = function() {
    if(!this.input.startsWith("/", this.jsStrPos)) {
        return false;
    }

    let jepos = this.input.indexOf("/", this.jsStrPos + 1);
    if(jepos === -1) {
            this.raiseError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, this.input.length - this.jsStrPos), "Unterminated Regex literal");
    }
    
    const mstr = this.input.slice(this.jsStrPos + 1, jepos);
    if(!_s_validRegexChars.test(mstr)) {
        this.raiseError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, jepos - this.jsStrPos), "Invalid characters in (or empty) Regex literal");
    }

    jepos++;
    if(this.input.startsWith("c", jepos) || this.input.startsWith("p", jepos)) {
        jepos++;
    }

    let strval = this.input.slice(this.jsStrPos, jepos);

    this.updatePositionInfo(this.jsStrPos, jepos);
    this.recordLexTokenWData(jepos, TokenStrings.Regex, strval);
    return true;
}
/**
 * @returns {boolean}
 * @throws {ParserError}
 */
BSQONLexer.prototype.tryLexPath = function() {
    return false;
}
/**
 * @returns {boolean}
 * @throws {ParserError}
 */
BSQONLexer.prototype.tryLexDateTime = function() {
    return false;
}
/**
 * @returns {boolean}
 * @throws {ParserError}
 */
BSQONLexer.prototype.tryLexDateTimeDelta = function() {
    return false;
}
/**
 * @returns {boolean}
 * @throws {ParserError}
 */
BSQONLexer.prototype.tryLexDateLike = function() {
    const mdd = this.tryLexDateTimeDelta();
    if(mdd) {
        return true;
    }

    const mdt = this.tryLexDateTime();
    if(mdt) {
        return true;
    }

    return false;
}
/**
 * @returns {boolean}
 * @throws {ParserError}
 */
BSQONLexer.prototype.tryLexSymbol = function() {
    const spaceop = this.trylexWSPlus(SpaceRequiredSymbols, _s_whitespaceRe);
    if(spaceop !== null) {
        const realstr = " " + spaceop.trim() + " ";

        this.recordLexToken(this.jsStrPos + spaceop.length, realstr);
        return true; 
    }
    else {
        const mm = ParenSymbols.find((value) => this.input.startsWith(value, this.jsStrPos)) || StandardSymbols.find((value) => this.input.startsWith(value, this.jsStrPos));
        if(mm !== undefined) {
            this.recordLexToken(this.jsStrPos + mm.length, mm);
            return true;
        }

        
        return false;
    }
}
/**
 * @returns {boolean}
 */
BSQONLexer.prototype.tryLexName = function() {
    const identifiermatch = this.trylex(_s_identiferName);
    const kwmatch = KeywordStrings.find((value) => this.input.startsWith(value, this.jsStrPos));

    if(identifiermatch === null && kwmatch === undefined) {
        return false;
    }

    if (identifiermatch !== null && kwmatch === undefined) {
        this.recordLexTokenWData(this.jsStrPos + identifiermatch.length, TokenStrings.IdentifierName, identifiermatch);
    }
    else if(identifiermatch === null && kwmatch !== undefined) {
        this.recordLexToken(this.jsStrPos + kwmatch.length, kwmatch);
    }
    else {
        const nnid = identifiermatch;
        const nnkw = kwmatch;

        if (nnid.length > nnkw.length) {
            this.recordLexTokenWData(this.jsStrPos + nnid.length, TokenStrings.IdentifierName, nnid);
        }
        else {
            this.recordLexToken(this.jsStrPos + nnkw.length, nnkw);
        }
    }

    return true;
}
/**
 * @returns {boolean}
 * @throws {ParserError}
 */
BSQONLexer.prototype.lex = function() {
    while (this.jsStrPos < this.input.length) {
        if (this.tryLexWS() || this.tryLexLineComment()) {
            //continue
        }
        else if(this.tryLexDateLike()) {
            //continue
        }
        else if(this.tryLexCharLike()) {
            //continue
        }
        else if(this.tryLexStringLike()) {
            //continue
        }
        else if(this.tryLexByteBuffer() || this.tryLexUUID() || this.tryLexHashCode()) {
            //continue
        }
        else if (this.tryLexNumberLikeToken()) {
            //continue
        }
        else if (this.tryLexSymbol() || this.tryLexName()) {
            //continue
        }
        else if (this.tryLexPath() || this.tryLexRegex()) {
            //continue
        }
        else {
            this.raiseError(new ParserError(this.srcfile, new SourceInfo(this.cline, this.linestart, this.jsStrPos, 1), "Unrecognized token"));
        }
    }
    this.recordLexToken(this.input.length, TokenStrings.EndOfStream);
    
    return this.tokens;
}

/**
 * @param {string} nv 
 * @param {BigInt | null} upper
 * @returns {BigInt}
 * @throws {ParserError}
 */
function isValidNat(nv, upper) {
    try {
        const vv = BigInt(nv);
        if(vv < 0) {
            throw new ParserError(new SourceInfo(0, 0, 0, 0), "Nat value outside of valid range");
        }
        if(upper !== null && vv > upper) {
            throw new ParserError(new SourceInfo(0, 0, 0, 0), "Nat value outside of valid range");
        }

        return vv;
    }
    catch(e) {
        throw new ParserError(new SourceInfo(0, 0, 0, 0), "Invalid Nat value");
    }
}

/**
 * @param {string} nv 
 * @param {BigInt | null} lower
 * @param {BigInt | null} upper
 * @returns {BigInt}
 * @throws {ParserError}
 */
function isValidInt(nv, lower, upper) {
    try {
        const vv = BigInt(nv);
        if(lower !== null && vv < lower) {
            throw new ParserError(new SourceInfo(0, 0, 0, 0), "Int value outside of valid range");
        }
        if(upper !== null && vv > upper) {
            throw new ParserError(new SourceInfo(0, 0, 0, 0), "Int value outside of valid range");
        }
        
        return vv;
    }
    catch(e) {
        throw new ParserError(new SourceInfo(0, 0, 0, 0), "Invalid Int");
    }
}

/**
 * @param {string} nv 
 * @returns {number}
 * @throws {ParserError}
 */
function isValidFloat(nv) {
    try {
        return parseFloat(nv);
    }
    catch(e) {
        throw new ParserError(new SourceInfo(0, 0, 0, 0), "Invalid Float");
    }
}

function BSQONParser(tokens) {
    this.tokens = tokens;
    this.idx = 0;

    this.vbinds = [];
}
/**
 * @returns {Token}
 */
BSQONParser.prototype.peek = function() {
    if(this.idx >= this.tokens.length) {
        return new Token(0, 0, 0, 0, TokenStrings.EndOfStream, TokenStrings.EndOfStream);
    }
    else {
        return this.tokens[this.idx];
    }
}
/**
 * @returns {Token}
 */
BSQONParser.prototype.consume = function() {
    if(this.idx >= this.tokens.length) {
        return new Token(0, 0, 0, 0, TokenStrings.EndOfStream, TokenStrings.EndOfStream);
    }
    else {
        return this.tokens[this.idx++];
    }
}
/**
 * @returns {string}
 * @throws {ParserError}
 */
BSQONParser.prototype.consumeAndGetData = function() {
    if(this.idx >= this.tokens.length) {
        throw new ParserError(new SourceInfo(0, 0, 0, 0), "Unexpected end of stream");
    }
    else {
        return this.tokens[this.idx++].data;
    }
}
/**
 * @param {string} kind
 * @throws {ParserError}
 */
BSQONParser.prototype.consumeExpected = function(kind) {
    const tok = this.consume();
    if(tok.kind !== kind) {
        throw new ParserError(tok.sinfo, `Expected token ${kind} but found ${tok.kind}`);
    }
}
/**
 * @param {string} kind
 * @throws {ParserError}
 */
BSQONParser.prototype.consumeExpectedAndGetData = function(kind) {
    const tok = this.consume();
    if(tok.kind !== kind) {
        throw new ParserError(tok.sinfo, `Expected token ${kind} but found ${tok.kind}`);
    }

    return tok.data;
}
/**
 * @param {string} kind
 * @returns {boolean}
 */
BSQONParser.prototype.test = function(kind) {
    return this.peek().kind === kind;
}
/**
 * @param {string} kind
 * @returns {boolean}
 */
BSQONParser.prototype.testTokens = function(...kinds) {
    if(this.idx + kinds.length > this.tokens.length) {
        return false;
    }

    for(let i = 0; i < kinds.length; ++i) {
        if(this.tokens[this.idx + i].kind !== kinds[i]) {
            return false;
        }
    }

    return true;
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseNone = function() {
    this.consumeExpected(KW_none);
    return _$none_lit;
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseBool = function() {
    if(!(this.test(KW_true) || this.test(KW_false))) {
        throw new ParserError(this.peek().sinfo, "Expected boolean literal");
    }
    else {
        this.consumeAndGetData() === KW_true ? true : false;
    }
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseNat = function() {
    const nv = this.consumeExpectedAndGetData(TokenStrings.Nat);
    return isValidNat(nv.slice(0, -1), MAX_SAFE_NAT);
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseInt = function() {
    const nv = this.consumeExpectedAndGetData(TokenStrings.Int);
    return isValidInt(nv.slice(0, -1), MIN_SAFE_INT, MAX_SAFE_INT);
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseBigNat = function() {
    const nv = this.consumeExpectedAndGetData(TokenStrings.BigNat);
    return isValidNat(nv.slice(0, -1), null);
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseBigInt = function() {
    const nv = this.consumeExpectedAndGetData(TokenStrings.BigInt);
    return isValidInt(nv.slice(0, -1), null, null);
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseRational = function() {
    NOT_IMPLEMENTED("parseRational");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseFloat = function() {
    const nv = this.consumeExpectedAndGetData(TokenStrings.Float);
    return isValidFloat(nv.slice(0, -1));
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseDecimal = function() {
    NOT_IMPLEMENTED("parseDecimal");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseDecimalDegree = function() {
    NOT_IMPLEMENTED("parseDecimalDegree");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseLatLong = function() {
    NOT_IMPLEMENTED("parseLatLong");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseComplex = function() {
    NOT_IMPLEMENTED("parseComplex");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseCChar = function() {
    const ss = this.consumeExpectedAndGetData(TokenStrings.CChar);
    try {
        return ss.slice(2, -1);
    }
    catch(e) {
        throw new ParserError(this.peek().sinfo, "Invalid CChar literal");
    }
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseUnicodeChar = function() {
    const ss = this.consumeExpectedAndGetData(TokenStrings.UnicodeChar);
    try {
        return ss.slice(2, -1);
    }
    catch(e) {
        throw new ParserError(this.peek().sinfo, "Invalid UnicodeChar literal");
    }
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseString = function() {
    const ss = this.consumeExpectedAndGetData(TokenStrings.String);
    try {
        return validateStringLiteral(ss.slice(1, -1));
    }
    catch(e) {
        throw new ParserError(this.peek().sinfo, "Invalid Unicode string literal");
    }
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseCString = function() {
    const ss = this.consumeExpectedAndGetData(TokenStrings.CString);
    try {
        return validateCStringLiteral(ss.slice(1, -1));
    }
    catch(e) {
        throw new ParserError(this.peek().sinfo, "Invalid CString literal");
    }
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseByteBuffer = function() {
    NOT_IMPLEMENTED("parseByteBuffer");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseUUIDv4 = function() {
    NOT_IMPLEMENTED("parseUUIDv4");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseUUIDv7 = function() {
    NOT_IMPLEMENTED("parseUUIDv7");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseSHAHashcode = function() {
    NOT_IMPLEMENTED("parseSHAHashcode");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseTZDateTime = function() {
    NOT_IMPLEMENTED("parseTZDateTime");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseTIATime = function() {
    NOT_IMPLEMENTED("parseTIATime");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parsePlainDate = function() {
    NOT_IMPLEMENTED("parsePlainDate");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parsePlainTime = function() {
    NOT_IMPLEMENTED("parsePlainTime");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseLogicalTime = function() {
    NOT_IMPLEMENTED("parseLogicalTime");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseISOTimeStamp = function() {
    NOT_IMPLEMENTED("parseISOTimeStamp");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseDeltaDateTime = function() {
    NOT_IMPLEMENTED("parseDeltaDateTime");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseDeltaSeconds = function() {
    NOT_IMPLEMENTED("parseDeltaSeconds");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseDeltaLogical = function() {
    NOT_IMPLEMENTED("parseDeltaLogical");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseDeltaISOTimeStamp = function() {
    NOT_IMPLEMENTED("parseDeltaISOTimeStamp");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseUnicodeRegex = function() {
    //TODO: We need to do better here...
    return this.consumeExpectedAndGetData(TokenStrings.Regex);
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseCRegex = function() {
    //TODO: We need to do better here...
    return this.consumeExpectedAndGetData(TokenStrings.CRegex);
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parsePathRegex = function() {
    NOT_IMPLEMENTED("parsePathRegex");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parsePath = function() {
    NOT_IMPLEMENTED("parsePath");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parsePathItem = function() {
    NOT_IMPLEMENTED("parsePathItem");
}
/**
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parsePathGlob = function() {
    NOT_IMPLEMENTED("parsePathGlob");
}
/**
 * @param {string} tkey
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseValuePrimitive = function(tkey) {
    if(tkey === "None") {
        return this.parseNone();
    }
    else if(tkey === "Bool") {
        return this.parseBool();
    }
    else if(tkey === "Int") {
        return this.parseInt();
    }
    else if(tkey === "Nat") {
        return this.parseNat();
    }
    else if(tkey === "BigInt") {
        return this.parseBigInt();
    }
    else if(tkey === "BigNat") {
        return this.parseBigNat();
    }
    else if(tkey === "Rational") {
        return this.parseRational();
    }
    else if(tkey === "Float") {
        return this.parseFloat();
    }
    else if(tkey === "Decimal") {
        return this.parseDecimal();
    }
    else if(tkey === "DecimalDegree") {
        return this.parseDecimalDegree();
    }
    else if(tkey === "LatLongCoordinate") {
        return this.parseLatLong();
    }
    else if(tkey === "Complex") {
        return this.parseComplex();
    }
    else if(tkey === "CChar") {
        return this.parseCChar();
    }
    else if(tkey === "UnicodeChar") {
        return this.parseUnicodeChar();
    }
    else if(tkey === "String") {
        return this.parseString();
    }
    else if(tkey === "CString") {
        return this.parseCString();
    }
    else if(tkey === "ByteBuffer") {
        return this.parseByteBuffer();
    }
    else if(tkey === "TZDateTime") {
        return this.parseTZDateTime();
    }
    else if(tkey === "TIATime") {
        return this.parseTIATime();
    }
    else if(tkey === "PlainDate") {
        return this.parsePlainDate();
    }
    else if(tkey === "PlainTime") {
        return this.parsePlainTime();
    }
    else if(tkey === "LogicalTime") {
        return this.parseLogicalTime();
    }
    else if(tkey === "ISOTimeStamp") {
        return this.parseISOTimeStamp();
    }
    else if(tkey === "UUIDv4") {
        return this.parseUUIDv4();
    }
    else if(tkey === "UUIDv7") {
        return this.parseUUIDv7();
    }
    else if(tkey === "SHAContentHash") {
        return this.parseSHAHashcode();
    }
    else if(tkey === "DataTimeDelta") {
        return this.parseDeltaDateTime();
    }
    else if(tkey === "SecondsDelta") {
        return this.parseDeltaSeconds();
    }
    else if(tkey === "ISOTimestampDelta") {
        return this.parseDeltaISOTimeStamp();
    }
    else if(tkey === "LogicalTimeDelta") {
        return this.parseDeltaLogical();
    }      
    else if(tkey === "UnicodeRegex") {
        return this.parseUnicodeRegex();
    }
    else if(tkey === "CRegex") {
        return this.parseCRegex();
    }
    else if(tkey === "PathRegex") {
        return this.parsePathRegex();
    }
    else if(tkey === "Path") {
        return this.parsePath();
    }
    else if(tkey === "PathItem") {
        return this.parsePathItem();
    }
    else if(tkey === "Glob") {
        return this.parseGlob();
    }
    else {
        throw new ParserError(this.peek().sinfo, `Unknown primitive type: ${tkey}`);
    }
}
/**
 * @param {string} tkey
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseIdentifier = function(tkey) {
    const idinfo = this.peek().sinfo;
    const vname = this.consumeExpectedAndGetData(TokenStrings.IdentifierName);
    
    const vbind = this.vbinds.find((mm) => mm.vname === vname);
    if(vbind === undefined) {
        throw new ParserError(idinfo, `Unknown identifier: ${vname}`);
    }
    else {
        if(vbind.tkey !== tkey) {
            throw new ParserError(idinfo, `Expected type ${tkey} but found ${vbind.tkey}`);
        }

        return vbind.value;
    }
}
/**
 * @returns {string | null}
 */
BSQONParser.prototype.peekScopedType = function() {
    if(!this.test(TokenStrings.IdentifierName)) {
        return null;
    }

    if(!isTypeIdentifierName(this.peek().data)) {
        return null;
    }

    let ii = this.idx;
    let sctype = this.tokens[ii].data;
    ii++;

    while(ii < this.tokens.length && s_typeTokens.includes(this.tokens[ii].kind)) {
        const tkval = this.tokens[ii].data;
        sctype += tkval;

        if(tkval === ",") {
            sctype += " ";
        }

        ii++;
    }

    return sctype;
}
/**
 * @returns {string}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseScopedType = function() {
    if(!this.test(TokenStrings.IdentifierName)) {
        throw new ParserError(this.peek().sinfo, "Expected scoped type");
    }

    if(!isTypeIdentifierName(this.peek().data)) {
        throw new ParserError(this.peek().sinfo, "Expected scoped type");
    }

    let sctype = this.tokens[this.idx].data;
    this.idx++;

    while(this.idx < this.tokens.length && s_typeTokens.includes(this.tokens[this.idx].kind)) {
        const tkval = this.tokens[this.idx].data;
        sctype += tkval;

        if(tkval === ",") {
            sctype += " ";
        }

        this.idx++;
    }

    return sctype;
}
/**
 * @returns {string | null}
 */
BSQONParser.prototype.peekScopedTypeTailing = function() {
    if(this.idx + 3 >= this.tokens.length || this.tokens[this.idx].kind !== SYM_langle || this.tokens[this.idx + 1].kind !== TokenStrings.IdentifierName) {
        return null;
    }

    let ii = this.idx + 1;
    let sctype = "";

    while(ii < this.tokens.length && (this.tokens[ii].kind === SYM_coloncolon || this.tokens[ii].kind === TokenStrings.IdentifierName)) {
        sctype += this.tokens[ii].data;
        ii++;
    }

    if(ii >= this.tokens.length || this.tokens[ii].kind !== SYM_rangle) {
        return null;
    }

    return sctype;
}
/**
 * @returns {string}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseScopedTypeTailing = function() {
    if(this.idx + 3 >= this.tokens.length || this.tokens[this.idx].kind !== SYM_langle || this.tokens[this.idx + 1].kind !== TokenStrings.IdentifierName) {
        throw new ParserError(this.peek().sinfo, "Expected tailing scoped type");
    }
    this.idx++;

    let sctype = "";
    while(this.idx < this.tokens.length && (this.tokens[this.idx].kind === SYM_coloncolon || this.tokens[this.idx].kind === TokenStrings.IdentifierName)) {
        sctype += this.tokens[this.idx].data;
        this.idx++;
    }

    if(this.idx >= this.tokens.length || this.tokens[this.idx].kind !== SYM_rangle) {
        throw new ParserError(this.peek().sinfo, "Expected tailing scoped type");
    }
    this.idx++;

    return sctype;
}
/**
 * @param {string} tkey
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseLetIn = function(tkey) {
    this.consumeExpected(KW_LET);
    
    const vname = this.consumeExpectedAndGetData(TokenStrings.IdentifierName);
    this.consumeExpected(SYM_colon);
    const ttype = this.parseScopedType();

    this.consumeExpected(SYM_eq);
    const vval = this.parseValue(ttype);
    
    this.vbinds.push({vname: vname, tkey: ttype, value: vval});
    const res = this.parseValue(tkey);
    this.vbinds.pop();

    return res;
}
/**
 * @param {string} tkey 
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseValue = function(tkey) {
    const hasparen = this.test("(");

    if(hasparen) {
        this.consumeExpected(SYM_lparen);
    }

    let res = null;
    if(this.test(TokenStrings.IdentifierName)) {
        const tt = this.peekScopedType();

        if(tt === null) {
            res = this.parseIdentifier(tkey);
        }
        else {
            const pf = resolveParseMapEntry(tkey)
            res = pf(this);
        }
    }
    else if(this.test(KW_LET)) {
        res = this.parseLetIn(tkey);
    }
    else if(s_coreTypes[tkey]) {
        res = this.parseValuePrimitive(tkey);
    }
    else {
        const pf = resolveParseMapEntry(tkey)
        res = pf(this);
    }

    if(hasparen) {
        this.consumeExpected(SYM_rparen);
    }

    return res;
}
/**
 * @returns {boolean}
 */
BSQONParser.prototype.testAndConsumeIfNone = function() {
    if(!this.test(KW_none)) {
        return false;
    }

    this.consume();
    return true;
}
/**
 * @returns {boolean}
 */
BSQONParser.prototype.testIfOk = function() {
    return this.test(KW_ok);
}
/**
 * @returns {boolean}
 */
BSQONParser.prototype.testIfFail = function() {
    return this.test(KW_fail);
}
/**
 * @param {string} token
 * @throws {ParserError}
 */
BSQONParser.prototype.checkSpecialCons = function(token) {
    this.consumeExpected(token);
}
/**
 * @param {string} tkey
 * @throws {ParserError}
 */
BSQONParser.prototype.checkConsType = function(tkey) {
    const tt = this.parseScopedType();
    if(tt !== tkey) {
        throw new ParserError(this.peek().sinfo, `Expected type ${tkey} but found ${tt}`);
    }
}
/**
 * @param {string} tkey
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseSingleArg = function(tkey) {
    this.consumeExpected(SYM_lbrace);
    const res = this.parseValue(tkey);
    this.consumeExpected(SYM_rbrace);

    return res;
}
/**
 * @param {string} tkey
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseSingleOrDefaultArg = function(tkey) {
    this.consumeExpected(SYM_lbrace);
    const res = !this.test(SYM_rbrace) ? this.parseValue(tkey) : undefined;
    this.consumeExpected(SYM_rbrace);

    return res;
}
/**
 * @param {object[]} tkeys
 * @returns {any[]}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseArgListGeneral = function(tkeys) {
    const res = [];
    for(let i = 0; i < tkeys.length; i++) {
        res.push(undefined);
    }

    if(!this.test(SYM_lbrace)) {
        throw new ParserError(this.peek().sinfo, "Expected argument list");
    }
    this.consume();

    if(this.test(SYM_rbrace)) {
        this.consume();
        return res;
    }
    else {
        let first = true;
        let positional = true;
        let pval = 0;
        while(first || this.test(SYM_coma)) {
            first = false;
            if(this.test(SYM_coma)) {
                this.consume();
            }

            if(this.testTokens(TokenStrings.IdentifierName, SYM_eq)) {
                positional = false;

                const nval = this.consumeAndGetData();
                this.consume();

                const ffidx = tkeys.findIndex((mm) => mm[0] === nval);
                if(ffidx === -1) {
                    throw new ParserError(this.peek().sinfo, `Unknown named argument: ${nval}`);
                }

                if(res[ffidx] !== undefined) {
                    throw new ParserError(this.peek().sinfo, `Duplicate argument: ${nval}`);
                }

                res[ffidx] = this.parseValue(tkeys[ffidx][1]);
            }
            else {
                if(!positional) {
                    throw new ParserError(this.peek().sinfo, "All positional arguments must come before named arguments");
                }

                res[pval] = this.parseValue(tkeys[pval][1]);
                pval++;
            }
        }

        this.consumeExpected(SYM_rbrace);
        return res;
    }
}
/**
 * @param {string} ktype
 * @param {string} vtype
 * @returns {any}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseMapEnty = function(ktype, vtype) {
    const kval = this.parseValue(ktype);
    this.consumeExpected(SYM_bigarrow);
    const vval = this.parseValue(vtype);

    return [kval, vval];
}
/**
 * @param {string} etype
 * @returns {any[]}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseCollectionConsArgs = function(etype) {
    const res = [];
    if(!this.test(SYM_lbrace)) {
        throw new ParserError(this.peek().sinfo, "Expected collection argument list");
    }
    this.consume();

    if(this.test(SYM_rbrace)) {
        this.consume();
        return res;
    }
    else {
        res.push(this.parseValue(etype));

        while(this.test(SYM_coma)) {
            this.consume();

            res.push(this.parseValue(etype));
        }

        this.consumeExpected(SYM_rbrace);
        return res;
    }
}
/**
 * @returns {string}
 * @throws {ParserError}
 */
BSQONParser.prototype.parseEnumNameComponent = function() {
    this.consumeExpected(SYM_hash); 
    return this.consumeExpectedAndGetData(TokenStrings.IdentifierName);
}

////////////////////////////////////////////////////////////////////////////////
//BSQON Emitter

function BSQONEmitter() {
    this.nl = "\n";
    this.istr = "";
}
/**
 * @param {string} v
 * @returns {string}
 */ 
BSQONEmitter.prototype.indent = function(v) {
    return this.istr + v;
}
/**
 * @returns {string}
 */
BSQONEmitter.prototype.emitNone = function() {
    return KW_none;
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitBool = function(v) {
    return v ? KW_true : KW_false;
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitNat = function(v) {
    return v.toString() + "n";
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitInt = function(v) {
    return v.toString() + "i";
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitBigNat = function(v) {
    return v.toString() + "N";
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitBigInt = function(v) {
    return v.toString() + "I";
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitRational = function(v) {
    NOT_IMPLEMENTED("emitRational");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitFloat = function(v) {
    const fs = v.toString();
    if(!fs.includes(".")) {
        return fs + ".0f";
    }
    else {
        if(fs.startsWith(".")) {
            return "0" + fs + "f";
        }
        else {
            return fs + "f";
        }
    }
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitDecimal = function(v) {
    NOT_IMPLEMENTED("emitDecimal");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitDecimalDegree = function(v) {
    NOT_IMPLEMENTED("emitDecimalDegree");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitLatLong = function(v) {
    NOT_IMPLEMENTED("emitLatLong");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitComplex = function(v) {
    NOT_IMPLEMENTED("emitComplex");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitCChar = function(v) {
    return `'${v.toString()}'`;
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitUnicodeChar = function(v) {
    return `'${v.toString()}'`;
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitString = function(v) {
    return `"${escapeStringLiteral(v)}"`;
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitCString = function(v) {
    return `'${escapeCStringLiteral(v)}'`;
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitByteBuffer = function(v) {
    NOT_IMPLEMENTED("emitByteBuffer");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitUUIDv4 = function(v) {
    NOT_IMPLEMENTED("emitUUIDv4");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitUUIDv7 = function(v) {
    NOT_IMPLEMENTED("emitUUIDv7");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitSHAHashcode = function(v) {
    NOT_IMPLEMENTED("emitSHAHashcode");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitTZDateTime = function(v) {
    NOT_IMPLEMENTED("emitTZDateTime");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitTIATime = function(v) {
    NOT_IMPLEMENTED("emitTIATime");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitPlainDate = function(v) {
    NOT_IMPLEMENTED("emitPlainDate");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitPlainTime = function(v) {
    NOT_IMPLEMENTED("emitPlainTime");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitLogicalTime = function(v) {
    NOT_IMPLEMENTED("emitLogicalTime");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitISOTimeStamp = function(v) {
    NOT_IMPLEMENTED("emitISOTimeStamp");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitDeltaDateTime = function(v) {
    NOT_IMPLEMENTED("emitDeltaDateTime");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitDeltaSeconds = function(v) {
    NOT_IMPLEMENTED("emitDeltaSeconds");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitDeltaLogical = function(v) {
    NOT_IMPLEMENTED("emitDeltaLogical");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitDeltaISOTimeStamp = function(v) {
    NOT_IMPLEMENTED("emitDeltaISOTimeStamp");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitUnicodeRegex = function(v) {
    //TODO: We need to do better here...
    NOT_IMPLEMENTED("emitUnicodeRegex");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitCRegex = function(v) {
    //TODO: We need to do better here...
    NOT_IMPLEMENTED("emitCRegex");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitPathRegex = function(v) {
    NOT_IMPLEMENTED("emitPathRegex");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitPath = function(v) {
    NOT_IMPLEMENTED("emitPath");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitPathItem = function(v) {
    NOT_IMPLEMENTED("emitPathItem");
}
/**
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitPathGlob = function(v) {
    NOT_IMPLEMENTED("emitPathGlob");
}
/**
 * @param {string} tkey
 * @param {any} v
 * @returns {string}
 */
BSQONEmitter.prototype.emitValuePrimitive = function(tkey, v) {
    if(tkey === "None") {
        return this.emitNone();
    }
    else if(tkey === "Bool") {
        return this.emitBool(v);
    }
    else if(tkey === "Int") {
        return this.emitInt(v);
    }
    else if(tkey === "Nat") {
        return this.emitNat(v);
    }
    else if(tkey === "BigInt") {
        return this.emitBigInt(v);
    }
    else if(tkey === "BigNat") {
        return this.emitBigNat(v);
    }
    else if(tkey === "Rational") {
        return this.emitRational(v);
    }
    else if(tkey === "Float") {
        return this.emitFloat(v);
    }
    else if(tkey === "Decimal") {
        return this.emitDecimal(v);
    }
    else if(tkey === "DecimalDegree") {
        return this.emitDecimalDegree(v);
    }
    else if(tkey === "LatLongCoordinate") {
        return this.emitLatLong(v);
    }
    else if(tkey === "Complex") {
        return this.emitComplex(v);
    }
    else if(tkey === "CChar") {
        return this.emitCChar(v);
    }
    else if(tkey === "UnicodeChar") {
        return this.emitUnicodeChar(v);
    }
    else if(tkey === "String") {
        return this.emitString(v);
    }
    else if(tkey === "CString") {
        return this.emitCString(v);
    }
    else if(tkey === "ByteBuffer") {
        return this.emitByteBuffer(v);
    }
    else if(tkey === "TZDateTime") {
        return this.emitTZDateTime(v);
    }
    else if(tkey === "TIATime") {
        return this.emitTIATime(v);
    }
    else if(tkey === "PlainDate") {
        return this.emitPlainDate(v);
    }
    else if(tkey === "PlainTime") {
        return this.emitPlainTime(v);
    }
    else if(tkey === "LogicalTime") {
        return this.emitLogicalTime(v);
    }
    else if(tkey === "ISOTimeStamp") {
        return this.emitISOTimeStamp(v);
    }
    else if(tkey === "UUIDv4") {
        return this.emitUUIDv4(v);
    }
    else if(tkey === "UUIDv7") {
        return this.emitUUIDv7(v);
    }
    else if(tkey === "SHAContentHash") {
        return this.emitSHAHashcode(v);
    }
    else if(tkey === "DataTimeDelta") {
        return this.emitDeltaDateTime(v);
    }
    else if(tkey === "SecondsDelta") {
        return this.emitDeltaSeconds(v);
    }
    else if(tkey === "ISOTimestampDelta") {
        return this.emitDeltaISOTimeStamp(v);
    }
    else if(tkey === "LogicalTimeDelta") {
        return this.emitDeltaLogical(v);
    }      
    else if(tkey === "UnicodeRegex") {
        return this.emitUnicodeRegex(v);
    }
    else if(tkey === "CRegex") {
        return this.emitCRegex(v);
    }
    else if(tkey === "PathRegex") {
        return this.emitPathRegex(v);
    }
    else if(tkey === "Path") {
        return this.emitPath(v);
    }
    else if(tkey === "PathItem") {
        return this.emitPathItem(v);
    }
    else if(tkey === "Glob") {
        return this.emitGlob(v);
    }
    else {
        return "[UNKNOWN PRIMTIVE TYPE -- " + tkey + "]";
    }
}
/**
 * @param {string} tkey
 * @param {any} v 
 * @returns {string}
 */
BSQONEmitter.prototype.emitValue = function(tkey, v) {
    if(s_coreTypes[tkey]) {
        return this.emitValuePrimitive(tkey, v);
    }
    else {
        return _$emitmap[tkey](this, v);
    }
}

////////////////////////////////////////////////////////////////////////////////
//Exposed functions

/**
 * @param {string[]} tkeys
 * @param {string} input
 * @returns {any[]}
 * @throws {ParserError}
 */
function _$parseBSQON(tkeys, input) {
    const lexer = new BSQONLexer(input);
    const tokens = lexer.lex();

    const parser = new BSQONParser(tokens);
    let res = [];
    for(let i = 0; i < tkeys.length; i++) {
        res.push(parser.parseValue(tkeys[i]));
    }

    return res;
}

/**
 * @param {string} tkey
 * @param {any} v
 * @returns {string}
 */
function _$emitBSQON(tkey, v) {
    const emitter = new BSQONEmitter();
    return emitter.emitValue(tkey, v);
}

/**
 * @param {any} nonelit
 */
function _$setnone_lit(nonelit) {
    return _$none_lit = nonelit;
}

export { 
    _$setnone_lit,
    _$parsemap, _$emitmap,
    _$parseBSQON, _$emitBSQON 
};