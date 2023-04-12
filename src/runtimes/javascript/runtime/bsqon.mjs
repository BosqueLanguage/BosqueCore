"use strict";

const TOKEN_NULL = "null";
const TOKEN_NONE = "none";
const TOKEN_NOTHING = "nothing";
const TOKEN_TYPE = "type";
const TOKEN_UNDER = "_";

const TOKEN_LBRACE = "{";
const TOKEN_RBRACE = "}";
const TOKEN_LBRACKET = "[";
const TOKEN_RBRACKET = "]";
const TOKEN_LPAREN = "(";
const TOKEN_RPAREN = ")";
const TOKEN_COLON = ":";
const TOKEN_COMMA = ",";
const TOKEN_EQUALS = "=";
const TOKEN_LET = "let";

const TOKEN_SRC = "$SRC";
const TOKEN_REFERENCE = "#REF";
const TOKEN_NAME = "DOT_NAME";
const TOKEN_IDX = "DOT_IDX";

const TOKEN_TRUE = "true"; 
const TOKEN_FALSE = "false";
const TOKEN_NAT = "NAT";
const TOKEN_INT = "INT";
const TOKEN_BIG_NAT = "BIG_NAT";
const TOKEN_BIG_INT = "BIG_INT";
const TOKEN_FLOAT = "FLOAT";
const TOKEN_DECIMAL = "DECIMAL";
const TOKEN_RATIONAL = "RATIONAL";
const TOKEN_STRING = "STRING";
const TOKEN_ASCII_STRING = "ASCII_STRING";
const TOKEN_STRING_OF = "STRING_OF";
const TOKEN_ASCII_STRING_OF = "ASCII_STRING_OF"; 
const TOKEN_BYTE_BUFFER = "BYTE_BUFFER";
const TOKEN_REGEX = "REGEX";
const TOKEN_DATE_TIME = "DATE_TIME";
const TOKEN_UTC_DATE_TIME = "UTC_DATE_TIME";
const TOKEN_PLAIN_DATE = "PLAIN_DATE";
const TOKEN_PLAIN_TIME = "PLAIN_TIME";
const TOKEN_TICK_TIME = "TICK_TIME";
const TOKEN_LOGICAL_TIME = "LOGICAL_TIME";
const TOKEN_ISO_TIME_STAMP = "ISO_TIME_STAMP";
const TOKEN_UUID_V4 = "UUID_V4";
const TOKEN_UUID_V7 = "UUID_V7";
const TOKEN_SHA_CONTENT_HASH = "SHA_CONTENT_HASH";
const TOKEN_LAT_LONG_COORDINATE = "LAT_LONG_COORDINATE";
const TOKEN_PATH = "PATH";
const TOKEN_PATH_FRAGMENT = "PATH_FRAGMENT"; 
const TOKEN_PATH_GLOB = "PATH_GLOB";

function createToken(type, value, extra) {
    return {
        type: type,
        value: value,
        extra: extra || undefined
    };
}

function BSQONParseError(msg, pos) {
    this.msg = msg;
    this.pos = pos;
}

const _s_whitespaceRe = /\s+/y;
const _s_commentRe = /(\/\/.*)|(\/\*(.|\s)*?\*\/)/uy;

const _s_intRe = /(0|-?[1-9][0-9]*)i/y;
const _s_natRe = /(0|[1-9][0-9]*)n/y;

const _s_floatRe = /([+-]?[0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?f/y;
const _s_decimalRe = /([+-]?[0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?d/y;

const _s_bigintRe = /(0|-?[1-9][0-9]*)I/y;
const _s_bignatRe = /(0|[1-9][0-9]*)N/y;
const _s_rationalRe = /((0|-?[1-9][0-9]*)|(0|-?[1-9][0-9]*)\/([1-9][0-9]*))R/y;

const _s_intNumberinoRe = /0|-?[1-9][0-9]*/y;
const _s_floatNumberinoRe = /([+-]?[0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?/y;

const _s_dotidxRe = /([.][0-9]+)/y;

const _s_stringRe = /"[^"\\\r\n]*(\\(.|\r?\n)[^"\\\r\n]*)*"/uy;
const _s_ascii_stringRe = /ascii\{"[^"\\\r\n]*(\\(.|\r?\n)[^"\\\r\n]*)*"\}/uy;
const _s_template_stringRe = /'[^'\\\r\n]*(\\(.|\r?\n)[^'\\\r\n]*)*'/uy;
const _s_ascii_template_stringRe = /ascii\{'[^'\\\r\n]*(\\(.|\r?\n)[^'\\\r\n]*)*'\}/uy;

const _s_regexRe = /\/[^"\\\r\n]*(\\(.)[^"\\\r\n]*)*\//y;

const _s_symbolRe = /[\W]+/y;
const _s_nameSrcRe = /[$]src/y;
const _s_nameRefRe = /[#]\w+/y;
const _s_nameTypeRe = /([A-Z]([a-zA-Z0-9_]|::)*)/y;
const _s_nameTypeReChk = /^([A-Z]([a-zA-Z0-9_]|::)*)$/;

const _s_dotNameAccessRe = /[.][a-z_][a-zA-Z0-9_]*/y;
const _s_dotIdxAccessRe = /[.][0-9]+/y;

const SymbolStrings = [
    TOKEN_NULL,
    TOKEN_NONE,
    TOKEN_NOTHING,
    TOKEN_TYPE,
    TOKEN_UNDER,

    TOKEN_LBRACE,
    TOKEN_RBRACE,
    TOKEN_LBRACKET,
    TOKEN_RBRACKET,
    TOKEN_LPAREN,
    TOKEN_RPAREN,
    TOKEN_COLON,
    TOKEN_COMMA,
    TOKEN_EQUALS,
    TOKEN_LET
];

function BSQON(str, asjson) {
    this.m_json = asjson || false;

    this.m_str = str;
    this.m_cpos = 0;
    this.m_epos = str.length;

    this.m_lastToken = undefined;
}
BSQON.prototype.lexWS = function () {
    _s_whitespaceRe.lastIndex = this.m_cpos;
    const m = _s_whitespaceRe.exec(this.m_input);
    if (m === null) {
        return false;
    }
    else {
        this.m_cpos += m[0].length;
        return true;
    }
}
BSQON.prototype.lexComment = function () {
    _s_commentRe.lastIndex = this.m_cpos;
    const m = _s_commentRe.exec(this.m_input);
    if (m === null) {
        return false;
    }
    else {
        this.m_cpos += m[0].length;
        return true;
    }
}
BSQON.prototype.lexNumber = function () {
    if (this.m_json) {
        _s_intNumberinoRe.lastIndex = this.m_cpos;
        const inio = _s_intNumberinoRe.exec(this.m_input);
        if (inio !== null) {
            this.m_cpos += inio[0].length;
            this.m_lastToken = createToken(TOKEN_INT, inio[0]);
            return true;
        }

        _s_floatNumberinoRe.lastIndex = this.m_cpos;
        const fnio = _s_floatNumberinoRe.exec(this.m_input);
        if (fnio !== null) {
            this.m_cpos += fnio[0].length;
            this.m_lastToken = createToken(TOKEN_FLOAT, fnio[0]);
            return true;
        }
    }
    else {
        _s_rationalRe.lastIndex = this.m_cpos;
        const mr = _s_rationalRe.exec(this.m_input);
        if (mr !== null) {
            this.m_cpos += mr[0].length;
            this.m_lastToken = createToken(TOKEN_RATIONAL, mr[0]);
            return true;
        }

        _s_bignatRe.lastIndex = this.m_cpos;
        const mbn = _s_bignatRe.exec(this.m_input);
        if (mbn !== null) {
            this.m_cpos += mbn[0].length;
            this.m_lastToken = createToken(TOKEN_BIG_NAT, mbn[0]);
            return true;
        }

        _s_bigintRe.lastIndex = this.m_cpos;
        const mbi = _s_bigintRe.exec(this.m_input);
        if (mbi !== null) {
            this.m_cpos += mbi[0].length;
            this.m_lastToken = createToken(TOKEN_BIG_INT, mbi[0]);
            return true;
        }

        _s_decimalRe.lastIndex = this.m_cpos;
        const md = _s_decimalRe.exec(this.m_input);
        if (md !== null) {
            this.m_cpos += md[0].length;
            this.m_lastToken = createToken(TOKEN_DECIMAL, md[0]);
            return true;
        }

        _s_floatRe.lastIndex = this.m_cpos;
        const mf = _s_floatRe.exec(this.m_input);
        if (mf !== null) {
            this.m_cpos += mf[0].length;
            this.m_lastToken = createToken(TOKEN_FLOAT, mf[0]);
            return true;
        }

        _s_natRe.lastIndex = this.m_cpos;
        const mn = _s_natRe.exec(this.m_input);
        if (mn !== null) {
            this.m_cpos += mn[0].length;
            this.m_lastToken = createToken(TOKEN_NAT, mn[0]);
            return true;
        }

        _s_intRe.lastIndex = this.m_cpos;
        const mi = _s_intRe.exec(this.m_input);
        if (mi !== null) {
            this.m_cpos += mi[0].length;
            this.m_lastToken = createToken(TOKEN_INT, mi[0]);
            return true;
        }

        _s_dotidxRe.lastIndex = this.m_cpos;
        const mdot = _s_dotidxRe.exec(this.m_input);
        if (mdot !== null) {
            this.m_cpos += mdot[0].length;
            this.m_lastToken = createToken(TOKEN_DOTIDX, mdot[0]);
            return true;
        }
    }

    return false;
}
BSQON.prototype.lexString = function () {
    _s_stringRe.lastIndex = this.m_cpos;
    const ms = _s_stringRe.exec(this.m_input);
    if (ms !== null) {
        this.m_cpos += ms[0].length;
        this.m_lastToken = createToken(TOKEN_STRING, ms[0]);
        return true;
    }

    if (!this.m_json) {
        _s_ascii_stringRe.lastIndex = this.m_cpos;
        const mas = _s_ascii_stringRe.exec(this.m_input);
        if (mas !== null) {
            this.m_cpos += mas[0].length;
            this.m_lastToken = createToken(TOKEN_ASCII_STRING, mas[0]);
            return true;
        }

        _s_template_stringRe.lastIndex = this.m_cpos;
        const template_string_m = _s_template_stringRe.exec(this.m_input);
        if (template_string_m !== null) {
            this.m_cpos += template_string_m[0].length;
            this.m_lastToken = createToken(TOKEN_TEMPLATE_STRING, template_string_m[0]);
            return true;
        }

        _s_ascii_template_stringRe.lastIndex = this.m_cpos;
        const ascii_template_string_m = _s_ascii_template_stringRe.exec(this.m_input);
        if (ascii_template_string_m !== null) {
            this.m_cpos += ascii_template_string_m[0].length;
            this.m_lastToken = createToken(TOKEN_ASCII_TEMPLATE_STRING, ascii_template_string_m[0]);
            return true;
        }
    }

    return false;
}
BSQON.prototype.lexRegex = function () {
    _s_regexRe.lastIndex = this.m_cpos;
    const ms = _s_regexRe.exec(this.m_input);
    if (ms !== null) {
        this.m_cpos += ms[0].length;
        this.m_lastToken = createToken(TOKEN_REGEX, ms[0]);
        return true;
    }

    return false;
}
BSQON.prototype.lexSymbol = function () {
    _s_symbolRe.lastIndex = this.m_cpos;
    const ms = _s_symbolRe.exec(this.m_input);
    if (ms !== null) {
        const sym = SymbolStrings.find((value) => ms[0].startsWith(value));
        if (sym !== undefined) {
            this.m_cpos += sym.length;
            this.m_lastToken = createToken(TOKEN_SYMBOL, sym);
            return true;
        }
    }

    return false;
}
BSQON.prototype.lexName = function() {
    _s_nameSrcRe.lastIndex = this.m_cpos;
    const msrc = _s_nameSrcRe.exec(this.m_input);
    if(msrc !== null) {
        this.m_cpos += msrc[0].length;
        this.m_lastToken = createToken(TOKEN_SRC, msrc[0]);
        return true;
    }

    _s_nameRefRe.lastIndex = this.m_cpos;
    const mref = _s_nameRefRe.exec(this.m_input);
    if(mref !== null) {
        this.m_cpos += mref[0].length;
        this.m_lastToken = createToken(TOKEN_REFERENCE, mref[0]);
        return true;
    }

    _s_nameTypeRe.lastIndex = this.m_cpos;
    const mtype = _s_nameTypeRe.exec(this.m_input);
    if(mtype !== null) {
        this.m_cpos += mtype[0].length;
        this.m_lastToken = createToken(TOKEN_TYPE, mtype[0]);
        return true;
    }

    return false;
}
BSQON.prototype.lexAccess = function() {
    _s_dotNameAccessRe.lastIndex = this.m_cpos;
    const dotname = _s_dotNameAccessRe.exec(this.m_input);
    if(doname !== null) {
        this.m_cpos += dotname[0].length;
        this.m_lastToken = createToken(TOKEN_DOTNAME, dotname[0].slice(1));
        return true;
    }

    _s_dotIdxAccessRe.lastIndex = this.m_cpos;
    const dotidx = _s_dotIdxAccessRe.exec(this.m_input);
    if(dotidx !== null) {
        this.m_cpos += dotidx[0].length;
        this.m_lastToken = createToken(TOKEN_DOTIDX, dotidx[0].slice(1));
        return true;
    }

    return false;
}
BSQON.prototype.peekToken = function () {
    if(this.m_lastToken !== undefined) {
        return this.m_lastToken;
    }

    while(this.lexWS() || this.lexComment()) {
        ; //eat the token
    }
    
    if (this.lexNumber() || this.lexString() || this.lexRegex() || this.lexSymbol() || this.lexName() || this.lexAccess()) {
        return this.m_lastToken;
    }
    else {
        return undefined;
    }
}
BSQON.prototype.popToken = function () {
    while(this.lexWS() || this.lexComment()) {
        ; //eat the token
    }
    
    if (this.lexNumber() || this.lexString() || this.lexRegex() || this.lexSymbol() || this.lexName() || this.lexAccess()) {
        return this.m_lastToken;
    }
    else {
        return undefined;
    }
}
BSQON.prototype.testToken = function (tkind) {
    return this.peekToken() !== undefined && this.peekToken().type === tkind;
}
BSQON.prototype.raiseError = function (msg) {
    throw new BSQONParseError(msg, this.m_cpos);
}
BSQON.prototype.raiseErrorIf = function (cond, msg) {
    if (cond) {
        this.raiseError(msg);
    }
}
BSQON.prototype.expectToken = function (tkind) {
    this.raiseErrorIf(!this.testToken(tkind), `Expected token ${tkind} but got ${this.peekToken()}`);
}
BSQON.prototype.expectTokenAndPop = function (tkind) {
    this.expectToken(tkind);
    return this.popToken();
}
BSQON.prototype.parseNone = function () {
    if(!this.m_json) {
        this.expectTokenAndPop(TOKEN_NONE);
    }
    else {
        this.expectTokenAndPop(TOKEN_NULL);
    }
    return null;
}
BSQON.prototype.parseNothing = function () {
    if(!this.m_json) {
        this.expectTokenAndPop(TOKEN_NOTHING);
    }
    else {
        this.expectTokenAndPop(TOKEN_NULL);
    }
    return null;
}
BSQON.prototype.parseType = function () {
    if(!this.m_json) {
        const tt = this.expectTokenAndPop(TOKEN_TYPE);
        return tt.value;
    }
    else {
        const tt = this.expectTokenAndPop(TOKEN_STRING).value.slice(1, -1);
        this.raiseErrorIf(!_s_nameTypeReChk.test(tt), `Expected type: but got ${tt}`);
        return tt;
    }
}
export {
    TOKEN_NONE, TOKEN_NOTHING, TOKEN_TYPE, TOKEN_UNDER,
    TOKEN_LBRACE, TOKEN_RBRACE, TOKEN_LBRACKET, TOKEN_RBRACKET, TOKEN_LPAREN, TOKEN_RPAREN, TOKEN_COLON, TOKEN_COMMA, TOKEN_EQUALS, TOKEN_LET,
    TOKEN_SRC, TOKEN_REFERENCE, TOKEN_NAME, TOKEN_IDX,
    TOKEN_TRUE, TOKEN_FALSE, TOKEN_NAT, TOKEN_INT, TOKEN_BIG_NAT, TOKEN_BIG_INT, TOKEN_FLOAT, TOKEN_DECIMAL, TOKEN_RATIONAL,
    TOKEN_STRING, TOKEN_ASCII_STRING, TOKEN_STRING_OF, TOKEN_ASCII_STRING_OF, TOKEN_BYTE_BUFFER, TOKEN_REGEX,
    TOKEN_DATE_TIME, TOKEN_UTC_DATE_TIME, TOKEN_PLAIN_DATE, TOKEN_PLAIN_TIME, TOKEN_TICK_TIME, TOKEN_LOGICAL_TIME, TOKEN_ISO_TIME_STAMP,
    TOKEN_UUID_V4, TOKEN_UUID_V7, TOKEN_SHA_CONTENT_HASH, TOKEN_LAT_LONG_COORDINATE,
    TOKEN_PATH, TOKEN_PATH_FRAGMENT, TOKEN_PATH_GLOB,
    BSQON, BSQONParseError
}