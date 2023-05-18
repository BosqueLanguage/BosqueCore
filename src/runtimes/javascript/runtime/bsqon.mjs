"use strict";

import {Decimal} from "decimal.js";
import Fraction from "fraction.js";

import * as $Limits from "./limits.mjs";
import * as $Runtime from "./runtime.mjs";

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
const TOKEN_LANGLE = "<";
const TOKEN_RANGLE = ">";
const TOKEN_COLON = ":";
const TOKEN_COLON_COLON = "::";
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
const TOKEN_BYTE_BUFFER = "BYTE_BUFFER";
const TOKEN_REGEX = "REGEX";
const TOKEN_ISO_DATE_TIME = "DATE_TIME";
const TOKEN_ISO_UTC_DATE_TIME = "DATE_TIME_UTC";
const TOKEN_ISO_DATE = "DATE";
const TOKEN_ISO_TIME = "TIME";
const TOKEN_TICK_TIME = "TICK_TIME";
const TOKEN_LOGICAL_TIME = "LOGICAL_TIME";
const TOKEN_ISO_TIMESTAMP = "ISO_TIMESTAMP";
const TOKEN_UUID = "UUID";
const TOKEN_SHA_HASH = "HASH";
const TOKEN_PATH_ITEM = "PATH";

function createToken(type, value) {
    return {
        type: type,
        value: value
    };
}

function BSQONParseError(msg, pos) {
    this.msg = msg;
    this.pos = pos;
}

const _s_whitespaceRe = /\s+/y;
const _s_commentRe = /(\/\/.*)|(\/\*(.|\s)*?\*\/)/uy;

const _s_bytebuffRe = /0x\[[a-zA-Z0-9]*\]/uy;
const _s_bytebuffCheckRe = /^[a-zA-Z0-9]*$/;

const _s_fullTimeRE = /([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})\.([0-9]{3})(\[[a-zA-Z/ _-]+\])/y;
const _s_fullTimeUTCRE = /([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})\.([0-9]{3})/y;
const _s_dateOnlyRE = /([0-9]{4})-([0-9]{2})-([0-9]{2})/y;
const _s_timeOnlyRE = /([0-9]{2}):([0-9]{2}):([0-9]{2})\.([0-9]{3})/y;

const _s_fullTimeCheckRE = /^([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})\.([0-9]{3})(\[[a-zA-Z/ _-]+\])?$/;
const _s_fullTimeUTCCheckRE = /^([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})\.([0-9]{3})$/;
const _s_dateOnlyCheckRE = /^([0-9]{4})-([0-9]{2})-([0-9]{2})$/;
const _s_timeOnlyCheckRE = /^([0-9]{2}):([0-9]{2}):([0-9]{2})\.([0-9]{3})$/;

const _s_tickTimeRE = /[0-9]+t/y;
const _s_logicalTimeRE = /[0-9]+l/y;
const _s_isostampRE = /([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})\.([0-9]{3})Z/;

const _s_tickTimeCheckRE = /^[0-9]+t$/;
const _s_logicalTimeCheckRE = /^[0-9]+l$/;
const _s_isoStampCheckRE = /^([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})\.([0-9]{3})Z$/;

const _s_uuidRE = /uuid(4|7)\{[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}\}/y;
const _s_shahashRE = /sha3\{0x[a-z0-9]{128}\}/y;

const _s_uuidCheckRE = /^[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}$/;
const _s_shahashCheckRE = /^0x[a-z0-9]{128}$/;

const _s_pathRe = /(path|fragment|glob)\{[^\}]*\}/uy;

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
const _s_nameTypeRe = /[A-Z]([a-zA-Z0-9_])+/y;

const _s_intCheckRe = /^0|-?[1-9][0-9]*$/;
const _s_natCheckRe = /^0|[1-9][0-9]*$/;
const _s_floatCheckRe = /^([+-]?[0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?$/;
const _s_rationalCheckRe = /^((0|-?[1-9][0-9]*)|(0|-?[1-9][0-9]*)\/([1-9][0-9]*))$/;

const _s_asciiStringCheckRe = /^\"[.]*\"$/;

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
    TOKEN_LANGLE, 
    TOKEN_RANGLE,

    TOKEN_COLON,
    TOKEN_COLON_COLON,
    TOKEN_COMMA,
    TOKEN_EQUALS,
    TOKEN_LET
];

const PARSE_MODE_DEFAULT = "BSQ_OBJ_NOTATION_DEFAULT";
const PARSE_MODE_JSON = "BSQ_OBJ_NOTATION_JSON";
const PARSE_MODE_FULL = "BSQ_OBJ_NOTATION_FULL";

const _s_core_types = [
    "None", "Bool", "Int", "Nat", "BigInt", "BigNat", "Rational", "Float", "Decimal", "String", "ASCIIString",
    "ByteBuffer", "DateTime", "UTCDateTime", "PlainDate", "PlainTime", "TickTime", "LogicalTime", "ISOTimeStamp", "UUIDv4", "UUIDv7", "SHAContentHash", 
    "LatLongCoordinate", "Regex", "Nothing", "Something"
];

const _s_core_types_with_templates = [
    "StringOf", "ASCIIStringOf", "Something", "Option", "Ok", "Error", "Result", "Path", "PathFragment", "PathGlob", "List", "Stack", "Queue", "Set", "MapEntry", "Map"
]

const _s_dateTimeNamedExtractRE = /^(?<year>[0-9]{4})-(?<month>[0-9]{2})-(?<day>[0-9]{2})T(?<hour>[0-9]{2}):(?<minute>[0-9]{2}):(?<second>[0-9]{2})\.(?<millis>[0-9]{3})(?<timezone>\[[a-zA-Z/ _-]+\]|Z)$/;

function _extractDateTimeYear(m) {
    const year = Number.parseInt(m.groups.year);
    return (1900 <= year && year <= 2200) ? year : undefined; 
}

function _extractDateTimeMonth(m) {
    const month = Number.parseInt(m.groups.month);
    return (0 <= month && month <= 11) ? month : undefined;
}

function _extractDateTimeDay(m) {
    const year = Number.parseInt(m.groups.year);
    const month = Number.parseInt(m.groups.month);
    const day = Number.parseInt(m.groups.day);
    
    if(month !== 1) {
        return (month === 3 || month === 5 || month === 8 || month === 10) ? (day <= 30) : (day <= 31);
    }
    else {
        const isleapyear = !(y === 1900 || y === 2100 || year === 2200) && (year % 4 === 0);
        return isleapyear ? (day <= 29) : (day <= 28);
    }
}

function _extractDateTimeHour(m) {
    const hour = Number.parseInt(m.groups.hour);
    return (0 <= hour && hour <= 23) ? hour : undefined;
}

function _extractDateTimeMinute(m) {
    const minute = Number.parseInt(m.groups.minute);
    return (0 <= minute && minute <= 59) ? minute : undefined;
}

function _extractDateTimeSecond(m) {
    const second = Number.parseInt(m.groups.second);
    return (0 <= second && second <= 60) ? second : undefined;
}

function _extractDateTimeMillis(dstr) {
    const millis = Number.parseInt(m.groups.millis);
    return (0 <= millis && millis <= 999) ? millis : undefined;
}

function _extractDateTimeTZ(dstr) {
    const tzinfo = m.groups.timezone;
    if(tzinfo === "Z") {
        return "UTC";
    }
    else {
        return tzinfo.slice(1, -1);
    }
}

function isValidBSQDate(dstr) {
    if(/0-9/.test(dstr)) {
        dstr = dstr + "Z";
    }

    const m = _s_dateTimeNamedExtractRE.exec(dstr);
    if(m === null) {
        return false;
    }

    const year = _extractDateTimeYear(m);
    const month = _extractDateTimeMonth(m);
    const day = _extractDateTimeDay(m);
    const hour = _extractDateTimeHour(m);
    const minute = _extractDateTimeMinute(m);
    const second = _extractDateTimeSecond(m);
    const millis = _extractDateTimeMillis(m);

    return (year !== undefined && month !== undefined && day !== undefined && hour !== undefined && minute !== undefined && second !== undefined && millis !== undefined);
}

function generateDate(dstr) {
    dstr = dstr + "T00:00:00.000Z";
    if(!isValidBSQDate(dstr)) {
        return undefined;
    }

    const m = _s_dateTimeNamedExtractRE.exec(dstr);
    const year = _extractDateTimeYear(m);
    const month = _extractDateTimeMonth(m);
    const day = _extractDateTimeDay(m);

    return new $Runtime.BSQDate.create(year, month, day);
}

function generateTime(dstr) {
    dstr = "2000-01-01" + "T" + dstr + "Z";
    if(!isValidBSQDate(dstr)) {
        return undefined;
    }

    const m = _s_dateTimeNamedExtractRE.exec(dstr);
    const hour = _extractDateTimeHour(m);
    const minute = _extractDateTimeMinute(m);
    const second = _extractDateTimeSecond(m);
    const millis = _extractDateTimeMillis(m);

    return new $Runtime.BSQTime.create(hour, minute, second, millis);
}

function generateDateTime(dstr) {
    if(!isValidBSQDate(dstr)) {
        return undefined;
    }

    const m = _s_dateTimeNamedExtractRE.exec(dstr);
    const year = _extractDateTimeYear(m);
    const month = _extractDateTimeMonth(m);
    const day = _extractDateTimeDay(m);
    const hour = _extractDateTimeHour(m);
    const minute = _extractDateTimeMinute(m);
    const second = _extractDateTimeSecond(m);
    const millis = _extractDateTimeMillis(m);
    const tz = _extractDateTimeTZ(m);

    return new $Runtime.BSQDateTime.create(year, month, day, hour, minute, second, millis, tz);
}

function BSQON(ns, aliasmap, str, srcbind, mode) {
    this.m_parsemode = mode || PARSE_MODE_DEFAULT;

    this.m_ns = ns;
    this.m_aliasmap = aliasmap;

    this.m_str = str;
    this.m_cpos = 0;
    this.m_epos = str.length;

    this.m_lastToken = undefined;

    this.m_srcbind = srcbind;
    this.m_refs = new Map();
}
BSQON.prototype.isDefaultMode = function () {
    return this.m_parsemode === PARSE_MODE_DEFAULT;
}
BSQON.prototype.isJSONMode = function () {
    return this.m_parsemode === PARSE_MODE_JSON;
}
BSQON.prototype.isFullMode = function () {
    return this.m_parsemode === PARSE_MODE_FULL;
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
BSQON.prototype.lexBytebuff = function () {
    _s_bytebuffRe.lastIndex = this.m_cpos;
    const m = _s_bytebuffRe.exec(this.m_input);
    if (m === null) {
        return false;
    }
    else {
        this.m_cpos += m[0].length;
        this.m_lastToken = createToken(TOKEN_BYTE_BUFFER, m[0]);
        return true;
    }
}
BSQON.prototype.lexTimeInfo = function () {
    _s_fullTimeRE.lastIndex = this.m_cpos;
    const ftm = _s_fullTimeRE.exec(this.m_input);
    if(ftm !== null) {
        this.m_cpos += ftm[0].length;
        this.m_lastToken = createToken(TOKEN_ISO_DATE_TIME, ftm[0]);
        return true;
    }

    _s_fullTimeUTCRE.lastIndex = this.m_cpos;
    const ftutc = _s_fullTimeUTCRE.exec(this.m_input);
    if(ftutc !== null) {
        this.m_cpos += ftutc[0].length;
        this.m_lastToken = createToken(TOKEN_ISO_UTC_DATE_TIME, ftutc[0]);
        return true;
    }

    _s_dateOnlyRE.lastIndex = this.m_cpos;
    const dm = _s_dateOnlyRE.exec(this.m_input);
    if(dm !== null) {
        this.m_cpos += dm[0].length;
        this.m_lastToken = createToken(TOKEN_ISO_DATE, dm[0]);
        return true;
    }

    _s_timeOnlyRE.lastIndex = this.m_cpos;
    const tm = _s_timeOnlyRE.exec(this.m_input);
    if(tm !== null) {
        this.m_cpos += tm[0].length;
        this.m_lastToken = createToken(TOKEN_ISO_TIME, tm[0]);
        return true;
    }

    return false;
}
BSQON.prototype.lexLogicalTime = function () {
    _s_logicalTimeRE.lastIndex = this.m_cpos;
    const m = _s_logicalTimeRE.exec(this.m_input);
    if (m === null) {
        return false;
    }
    else {
        this.m_cpos += m[0].length;
        this.m_lastToken = createToken(TOKEN_LOGICAL_TIME, m[0]);
        return true;
    }
}
BSQON.prototype.lexTickTime = function () {
    _s_tickTimeRE.lastIndex = this.m_cpos;
    const m = _s_tickTimeRE.exec(this.m_input);
    if (m === null) {
        return false;
    }
    else {
        this.m_cpos += m[0].length;
        this.m_lastToken = createToken(TOKEN_TICK_TIME, m[0]);
        return true;
    }
}
BSQON.prototype.lexISOTimestamp = function () {
    _s_isostampRE.lastIndex = this.m_cpos;
    const m = _s_isostampRE.exec(this.m_input);
    if (m === null) {
        return false;
    }
    else {
        this.m_cpos += m[0].length;
        this.m_lastToken = createToken(TOKEN_ISO_TIMESTAMP, m[0]);
        return true;
    }
}
BSQON.prototype.lexUUID = function () {
    _s_uuidRE.lastIndex = this.m_cpos;
    const m = _s_uuidRE.exec(this.m_input);
    if (m === null) {
        return false;
    }
    else {
        this.m_cpos += m[0].length;
        this.m_lastToken = createToken(TOKEN_UUID, m[0]);
        return true;
    }
}
BSQON.prototype.lexSHACode = function () {
    _s_shahashRE.lastIndex = this.m_cpos;
    const m = _s_shahashRE.exec(this.m_input);
    if (m === null) {
        return false;
    }
    else {
        this.m_cpos += m[0].length;
        this.m_lastToken = createToken(TOKEN_SHA_HASH, m[0]);
        return true;
    }
}
BSQON.prototype.lexPath = function () {
    _s_pathRe.lastIndex = this.m_cpos;
    const m = _s_pathRe.exec(this.m_input);
    if (m === null) {
        return false;
    }
    else {
        this.m_cpos += m[0].length;
        this.m_lastToken = createToken(TOKEN_PATH_ITEM, m[0]);
        return true;
    }
}
BSQON.prototype.lexNumber = function () {
    if (this.isJSONMode()) {
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

    if (!this.isJSONMode()) {
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
        this.m_lastToken = createToken(TOKEN_TYPE, mtype[0].trim());
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
    
    if (this.lexBytebuff() || this.lexTimeInfo() || this.lexLogicalTime() || this.lexTickTime() || this.lexISOTimestamp() ||
        this.lexUUID() || this.lexSHACode() || this.lexPath() ||
        this.lexNumber() || this.lexString() || this.lexRegex() || 
        this.lexSymbol() || this.lexName() || this.lexAccess()) {
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
    
    if (this.lexBytebuff() || this.lexTimeInfo() || this.lexLogicalTime() || this.lexTickTime() || this.lexISOTimestamp() ||
        this.lexUUID() || this.lexSHACode() || this.lexPath() ||
        this.lexNumber() || this.lexString() || this.lexRegex() || 
        this.lexSymbol() || this.lexName() || this.lexAccess()) {
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
BSQON.prototype.resolveType = function (tt) {
    xxxx;
}
BSQON.prototype.parseType = function (expectedOpt) {
    if(this.isFullMode()) {
        let tt = this.expectTokenAndPop(TOKEN_TYPE).value;
        if(!tt.startsWith())

        return tt;
    }
    else if(this.isDefaultMode()) {
        let tt = this.expectTokenAndPop(TOKEN_TYPE).value;
        xxx;

        this.raiseErrorIf(expectedOpt !== undefined && expectedOpt !== tt, `Expected type: but got ${tt.value}`);
        return tt;
    }
    else {
        let tt = this.expectTokenAndPop(TOKEN_STRING).value.slice(1, -1);
        this.raiseErrorIf(!_s_nameTypeReChk.test(tt), `Expected type: but got ${tt}`);

        xxx;
        return tt;
    }
}
BSQON.prototype.parseSrc = function () {
    this.expectTokenAndPop(TOKEN_SRC);

    this.raiseErrorIf(this.m_srcbind === undefined, "Invalid use of $SRC binding");
    return this.m_srcbind;
}
BSQON.prototype.parseReference = function () {
    const ref = this.expectTokenAndPop(TOKEN_REFERENCE).value;

    this.raiseErrorIf(!this.m_refs.has(ref), `Reference ${ref} not found`);
    return this.m_refs.get(ref);
}
BSQON.prototype.parseNone = function () {
    if(!this.isJSONMode()) {
        this.expectTokenAndPop(TOKEN_NONE);
    }
    else {
        this.expectTokenAndPop(TOKEN_NULL);
    }
    return null;
}
BSQON.prototype.parseNothing = function () {
    if(!this.isJSONMode()) {
        this.expectTokenAndPop(TOKEN_NOTHING);
    }
    else {
        this.expectTokenAndPop(TOKEN_NULL);
    }
    return null;
}
BSQON.prototype.parseBool = function () {
    const tk = this.popToken();
    return tk.type === TOKEN_TRUE;
}
BSQON.prototype.parseNat = function () {
    let tkval = undefined;
    if(!this.isJSONMode()) {
        tkval = this.expectTokenAndPop(TOKEN_NAT).value.slice(0, -1);
    }
    else {
        tkval = this.expectTokenAndPop(TOKEN_INT).value;
    }

    const bv = Number.parseInt(tkval);
    this.raiseErrorIf(Number.isNaN(bv) || !Number.isFinite(bv), `Expected finite Nat number but got -- ${tkval}`);
    this.raiseErrorIf(bv < 0, `Nat value is negative -- ${tkval}`);
    this.raiseErrorIf(bv > $Limits.FIXED_NUMBER_MAX, `Nat value is larger than max value -- ${tkval}`);

    return bv;
}
BSQON.prototype.parseInt = function () {
    let tkval = undefined;
    if(!this.isJSONMode()) {
        tkval = this.expectTokenAndPop(TOKEN_INT).value.slice(0, -1);
    }
    else {
        tkval = this.expectTokenAndPop(TOKEN_INT).value;
    }

    const bv = Number.parseInt(tkval);
    this.raiseErrorIf(Number.isNaN(bv) || !Number.isFinite(bv), `Expected finite Int number but got -- ${tkval}`);
    this.raiseErrorIf(bv < $Limits.FIXED_NUMBER_MIN, `Int value is smaller than min value -- ${tkval}`);
    this.raiseErrorIf(bv > $Limits.FIXED_NUMBER_MAX, `Int value is larger than max value -- ${tkval}`);
    
    return bv;
}
BSQON.prototype.parseBigNat = function () {
    let tkval = undefined;
    if(!this.isJSONMode()) {
        tkval = this.expectTokenAndPop(TOKEN_BIGNAT).value.slice(0, -1);
    }
    else {
        const tk = this.popToken();
        this.raiseErrorIf(tk.type !== TOKEN_INT && tk.type !== TOKEN_STRING, `Expected BigInt but got ${tk}`);

        if(tk.type === TOKEN_INT) {
            tkval = tk.value;
        }
        else {
            tkval = tk.value.slice(1, -1);
            this.raiseErrorIf(!_s_natCheckRe.test(tkval), `Expected BigInt: but got ${tkval}`);
        }
    }

    return BigInt(tkval);
}
BSQON.prototype.parseBigInt = function () {
    let tkval = undefined;
    if(!this.isJSONMode()) {
        tkval = this.expectTokenAndPop(TOKEN_BIGNAT).value.slice(0, -1);
    }
    else {
        const tk = this.popToken();
        this.raiseErrorIf(tk.type !== TOKEN_INT && tk.type !== TOKEN_STRING, `Expected BigInt but got ${tk}`);

        if(tk.type === TOKEN_INT) {
            tkval = tk.value;
        }
        else {
            tkval = tk.value.slice(1, -1);
            this.raiseErrorIf(!_s_intCheckRe.test(tkval), `Expected BigInt: but got ${tkval}`);
        }
    }

    return BigInt(tkval);
}
BSQON.prototype.parseRational = function () {
    if(!this.isJSONMode()) {
        const tkval = this.expectTokenAndPop(TOKEN_RATIONAL).value.slice(0, -1);
        return Fraction(tkval);
    }
    else {
        const tkval = this.expectTokenAndPop(TOKEN_STRING).value.slice(1, -1);
        this.raiseErrorIf(!_s_rationalCheckRe.test(tkval), `Expected float but got ${tkval}`);

        return Fraction(tkval);
    }
}
BSQON.prototype.parseFloat = function () {
    if(!this.isJSONMode()) {
        const tkval = this.expectTokenAndPop(TOKEN_FLOAT).value.slice(0, -1);
        return parseFloat(tkval);
    }
    else {
        const tkval = this.expectTokenAndPop(TOKEN_FLOAT).value;
        this.raiseErrorIf(!_s_floatCheckRe.test(tkval), `Expected float but got ${tkval}`);

        return parseFloat(tkval);
    }
}
BSQON.prototype.parseDecimal = function () {
    if(!this.isJSONMode()) {
        const tkval = this.expectTokenAndPop(TOKEN_DECIMAL).value.slice(0, -1);
        return Decimal(tkval);
    }
    else {
        const tkval = this.expectTokenAndPop(TOKEN_FLOAT).value;
        this.raiseErrorIf(!_s_floatCheckRe.test(tkval), `Expected float but got ${tkval}`);

        return Decimal(tkval);
    }
}
BSQON.prototype.parseString = function () {
    return this.expectTokenAndPop(TOKEN_STRING).value;
}
BSQON.prototype.parseAsciiString = function () {
    if(!this.isJSONMode()) {
        return this.expectTokenAndPop(TOKEN_ASCII_STRING).value.slice(6, -1);
    }
    else {
        const ts = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_asciiStringCheckRe.test(ts), `Expected ASCII string but got ${ts}`);

        return ts;
    }
}
BSQON.prototype.parseByteBuffer = function () {
    if(!this.isJSONMode()) {
        return this.expectTokenAndPop(TOKEN_BYTE_BUFFER).value.slice(3, -1);
    }
    else {
        const tb = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_bytebuffCheckRe.test(tb), `Expected byte buffer but got ${tb}`);

        return tb;
    }
}
BSQON.prototype.parseDateTime = function () {
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_ISO_DATE_TIME).value;
        const dd = generateDateTime(tk);
        this.raiseErrorIf(dd === undefined, `Expected date+time but got ${tk}`);

        return dd;
    }
    else {
        const tk = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_fullTimeCheckRE.test(tk), `Expected date+time but got ${tk}`);

        const dd = generateDateTime(tk);
        this.raiseErrorIf(dd === undefined, `Expected date+time but got ${tk}`);

        return dd;
    }
}
BSQON.prototype.parseUTCDateTime = function () {
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_ISO_UTC_DATE_TIME).value;
        const dd = generateDateTime(tk);
        this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected UTC date+time but got ${tk}`);

        return dd;
    }
    else {
        const tk = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_fullTimeUTCCheckRE.test(tk), `Expected UTC date+time but got ${tk}`);

        const dd = generateDateTime(tk);
        this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected UTC date+time but got ${tk}`);

        return dd;
    }
}
BSQON.prototype.parsePlainDate = function () {
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_ISO_DATE).value;
        const dd = generateDate(tk);
        this.raiseErrorIf(dd === undefined, `Expected plain date but got ${tk}`);

        return dd;
    }
    else {
        const tk = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_dateOnlyCheckRE.test(tk), `Expected plain date but got ${tk}`);

        const dd = generateDate(tk);
        this.raiseErrorIf(dd === undefined, `Expected plain date but got ${tk}`);

        return dd;
    }
}
BSQON.prototype.parsePlainTime = function () {
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_ISO_TIME).value;
        const dd = generateTime(tk);
        this.raiseErrorIf(dd === undefined, `Expected plain time but got ${tk}`);

        return dd;
    }
    else {
        const tk = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_timeOnlyCheckRE.test(tk), `Expected plain time but got ${tk}`);

        const dd = generateTime(tk);
        this.raiseErrorIf(dd === undefined, `Expected plain time but got ${tk}`);

        return dd;
    }
}
BSQON.prototype.parseTickTime = function () {
    if(!this.isJSONMode()) {
        const tt = this.expectTokenAndPop(TOKEN_TICK_TIME).value;
        return new BigInt(tt.slice(0, -1));
    }
    else {
        const tt = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_tickTimeCheckRE.test(tt), `Expected tick time but got ${tt}`);

        return new BigInt(tt);
    }
}
BSQON.prototype.parseLogicalTime = function () {
    if(!this.isJSONMode()) {
        const tt = this.expectTokenAndPop(TOKEN_LOGICAL_TIME).value;
        return new BigInt(tt.slice(0, -1));
    }
    else {
        const tt = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_logicalTimeCheckRE.test(tt), `Expected logical time but got ${tt}`);

        return new BigInt(tt);
    }
}
BSQON.prototype.parseISOTimeStamp = function () {
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_ISO_TIMESTAMP).value;
        const dd = generateDateTime(tk);
        this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected timestamp but got ${tk}`);

        return dd;
    }
    else {
        const tk = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_isoStampCheckRE.test(tk), `Expected timestamp but got ${tk}`);

        const dd = generateDateTime(tk);
        this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected timestamp but got ${tk}`);

        return dd;
    }
}
BSQON.prototype.parseUUIDv4 = function () {
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_UUID).value;
        this.raiseErrorIf(!tk.startsWith("uuid4{"), `Expected UUIDv4 but got ${tk}`);

        return tk.slice(6, -1);
    }
    else {
        const tk = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_uuidCheckRE.test(tk), `Expected UUIDv4 but got ${tk}`);

        return tk;
    }
}
BSQON.prototype.parseUUIDv7 = function () {
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_UUID).value;
        this.raiseErrorIf(!tk.startsWith("uuid7{"), `Expected UUIDv7 but got ${tk}`);

        return tk.slice(6, -1);
    }
    else {
        const tk = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_uuidCheckRE.test(tk), `Expected UUIDv7 but got ${tk}`);

        return tk;
    }
}
BSQON.prototype.parseSHAContentHash = function () {
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_SHA_HASH).value;
        return tk.slice(5, -1);
    }
    else {
        const tk = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_shahashCheckRE.test(tk), `Expected SHA3 512 hash but got ${tk}`);

        return tk;
    }
}
BSQON.prototype.parseLatLongCoordinate = function () {
    if (!this.isJSONMode()) {
        const ttype = this.expectTokenAndPop(TOKEN_TYPE).value;
        this.raiseErrorIf(ttype !== "LatLongCoordinate", `Expected LatLongCoordinate but got ${ttype}`);

        this.expectTokenAndPop(TOKEN_LBRACE);
        const lat = this.parseFloat();
        this.expectTokenAndPop(TOKEN_COMMA);
        const long = this.parseFloat();
        this.expectTokenAndPop(TOKEN_RBRACE);

        return $Runtime.BSQONLatLongCoordinate.create(lat, long);
    }
    else {
        this.expectTokenAndPop(TOKEN_LBRACKET);
        const lat = this.parseFloat();
        this.expectTokenAndPop(TOKEN_COMMA);
        const long = this.parseFloat();
        this.expectTokenAndPop(TOKEN_RBRACKET);

        return $Runtime.BSQONLatLongCoordinate.create(lat, long);
    }
}
BSQON.prototype.parseStringOf = function (ttype) {
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_STRING).value;
        const vv = this.parseType

        return tk.slice(7, -1);
    }
    else {

    }
}
BSQON.prototype.parseAsciiStringOf = function () {
    xxxx;
}


export {
    BSQON, BSQONParseError
}
