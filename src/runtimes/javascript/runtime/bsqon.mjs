"use strict";

import {Decimal} from "decimal.js";
import Fraction from "fraction.js";

import * as $Constants from "./constants.mjs";
import * as $TypeInfo from "./typeinfo.js";
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
const TOKEN_AMP = "&";
const TOKEN_BAR = "|";
const TOKEN_EQUALS = "=";
const TOKEN_LET = "let";

const TOKEN_SRC = "$SRC";
const TOKEN_REFERENCE = "#REF";
const TOKEN_PROPERTY = "PROPERTY";
const TOKEN_DOT_NAME = "DOT_NAME";
const TOKEN_DOT_IDX = "DOT_IDX";

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

const _s_stringRe = /"[^"\\\r\n]*(\\(.|\r?\n)[^"\\\r\n]*)*"/uy;
const _s_ascii_stringRe = /ascii\{"[^"\\\r\n]*(\\(.|\r?\n)[^"\\\r\n]*)*"\}/uy;
const _s_template_stringRe = /'[^'\\\r\n]*(\\(.|\r?\n)[^'\\\r\n]*)*'/uy;
const _s_ascii_template_stringRe = /ascii\{'[^'\\\r\n]*(\\(.|\r?\n)[^'\\\r\n]*)*'\}/uy;

const _s_regexRe = /\/[^"\\\r\n]*(\\(.)[^"\\\r\n]*)*\//y;

const _s_symbolRe = /[\W]+/y;
const _s_nameSrcRe = /[$]src/y;
const _s_nameRefRe = /[#]\w+/y;
const _s_nameTypeRe = /[A-Z]([a-zA-Z0-9_])+/y;
const _s_namePropertyRE = /[a-z_][a-zA-Z0-9_]*/y;

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
    TOKEN_AMP,
    TOKEN_BAR,
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
    "LatLongCoordinate", "Regex", "Nothing"
];

const _s_core_types_with_one_template = [
    "StringOf", "ASCIIStringOf", "Something", "Option", "Path", "PathFragment", "PathGlob", "List", "Stack", "Queue", "Set"
]

const _s_core_types_with_two_templates = [
    "Result::Ok", "Result::Error", "Result", "MapEntry", "Map"
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

function createBSQONParseResult(value, type, ttree, breq) {
    if(!breq) {
        return value;
    }
    else {
        return [value, {ctype: type, ttree: ttree}];
    }
}
function getBSQONParseValue(parseinfo) {
    return !Array.isArray(parseinfo) ? parseinfo : parseinfo[0];
}
function getBSQONParseInfo(parseinfo) {
    return !Array.isArray(parseinfo) ? undefined : parseinfo[1];
}

function BSQONParse(defaultns, assembly, str, srcbind, mode) {
    this.m_parsemode = mode || PARSE_MODE_DEFAULT;

    this.m_defaultns = defaultns;
    this.m_assembly = assembly;

    this.m_str = str;
    this.m_cpos = 0;
    this.m_epos = str.length;

    this.m_lastToken = undefined;

    this.m_srcbind = srcbind; //a [value, type, ttree] where type is always a concrete type
    this.m_refs = new Map(); //maps from names to [value, type, ttree] where type is always a concrete type
}
BSQONParse.prototype.isDefaultMode = function () {
    return this.m_parsemode === PARSE_MODE_DEFAULT;
}
BSQONParse.prototype.isJSONMode = function () {
    return this.m_parsemode === PARSE_MODE_JSON;
}
BSQONParse.prototype.isFullMode = function () {
    return this.m_parsemode === PARSE_MODE_FULL;
}
BSQONParse.prototype.lexWS = function () {
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
BSQONParse.prototype.lexComment = function () {
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
BSQONParse.prototype.lexBytebuff = function () {
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
BSQONParse.prototype.lexTimeInfo = function () {
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
BSQONParse.prototype.lexLogicalTime = function () {
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
BSQONParse.prototype.lexTickTime = function () {
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
BSQONParse.prototype.lexISOTimestamp = function () {
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
BSQONParse.prototype.lexUUID = function () {
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
BSQONParse.prototype.lexSHACode = function () {
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
BSQONParse.prototype.lexPath = function () {
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
BSQONParse.prototype.lexNumber = function () {
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
    }

    return false;
}
BSQONParse.prototype.lexString = function () {
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
BSQONParse.prototype.lexRegex = function () {
    _s_regexRe.lastIndex = this.m_cpos;
    const ms = _s_regexRe.exec(this.m_input);
    if (ms !== null) {
        this.m_cpos += ms[0].length;
        this.m_lastToken = createToken(TOKEN_REGEX, ms[0]);
        return true;
    }

    return false;
}
BSQONParse.prototype.lexSymbol = function () {
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
BSQONParse.prototype.lexName = function() {
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

    _s_namePropertyRE.lastIndex = this.m_cpos;
    const pname = _s_namePropertyRE.exec(this.m_input);
    if(pname !== null) {
        this.m_cpos += pname[0].length;
        this.m_lastToken = createToken(TOKEN_PROPERTY, mtype[0]);
        return true;
    }

    return false;
}
BSQONParse.prototype.lexAccess = function() {
    _s_dotNameAccessRe.lastIndex = this.m_cpos;
    const dotname = _s_dotNameAccessRe.exec(this.m_input);
    if(doname !== null) {
        this.m_cpos += dotname[0].length;
        this.m_lastToken = createToken(TOKEN_DOT_NAME, dotname[0].slice(1));
        return true;
    }

    _s_dotIdxAccessRe.lastIndex = this.m_cpos;
    const dotidx = _s_dotIdxAccessRe.exec(this.m_input);
    if(dotidx !== null) {
        this.m_cpos += dotidx[0].length;
        this.m_lastToken = createToken(TOKEN_DOT_IDX, dotidx[0].slice(1));
        return true;
    }

    return false;
}
BSQONParse.prototype.peekToken = function () {
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
BSQONParse.prototype.popToken = function () {
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
BSQONParse.prototype.unquoteStringForTypeParse = function () {
    const slen = this.m_lastToken.value.length;
    const str = " " + this.m_lastToken.value.slice(1, -1) + " ";

    this.m_cpos -= slen;
    this.m_str = this.m_str.slice(0, this.m_cpos) + str + this.m_str.slice(this.m_cpos + slen);
}

BSQONParse.prototype.testToken = function (tkind) {
    return this.peekToken() !== undefined && this.peekToken().type === tkind;
}
BSQONParse.prototype.raiseError = function (msg) {
    throw new BSQONParseError(msg, this.m_cpos);
}
BSQONParse.prototype.raiseErrorIf = function (cond, msg) {
    if (cond) {
        this.raiseError(msg);
    }
}
BSQONParse.prototype.expectToken = function (tkind) {
    this.raiseErrorIf(!this.testToken(tkind), `Expected token ${tkind} but got ${this.peekToken()}`);
}
BSQONParse.prototype.expectTokenAndPop = function (tkind) {
    this.expectToken(tkind);
    return this.popToken();
}
BSQONParse.prototype.resolveTypeFromNameList = function (tt) {
    let scopedname = "[uninit]";

    if(this.m_assembly.find((ns) => ns.ns === "Core").types.includes(tt.join("::"))) {
        scopedname = tt.join("::");
    }
    else if(tt.length === 1 || this.m_assembly.namespaces.find((ns) => ns.ns === tt[0]) === undefined || !this.m_assembly.namespaces.find((ns) => ns.ns === tt[0]).types.includes(tt.slice(1).join("::"))) {
        scopedname = `${this.m_defaultns}::${tt.join("::")}`;
    }
    else {
        scopedname = tt.join("::");
    }

    if(!this.m_assembly.aliasmap.has(scopedname)) {
        return tt;
    }
    else {
        return this.m_assembly.aliasmap.get(tt);
    }
}
BSQONParse.prototype.processCoreType = function (tname) {
    return $TypeInfo.createSimpleNominal(tname);
}
BSQONParse.prototype.processCoreTypeW1Term = function (tname, terms, expectedOpt) {
    if(tname === "StringOf") {
        this.raiseErrorIf(terms.length !== 1, `Type ${tname} requires one type argument`);
        return $TypeInfo.createStringOf(terms[0]);
    } 
    else if(tname === "ASCIIStringOf") {
        this.raiseErrorIf(terms.length !== 1, `Type ${tname} requires one type argument`);
        return $TypeInfo.createASCIIStringOf(terms[0]);
    } 
    else if(tname === "Something") {
        let t = $TypeInfo.unresolvedType;
        if(terms.length === 1) {
            t = terms[0];
        }
        else {
            this.raiseErrorIf(expectedOpt === undefined, `Relaxed type resolution required expected type information for ${tname}`);
            const sopts = expectedOpt.tag === $TypeInfo.TYPE_SOMETHING ? expectedOpt : expectedOpt.types.find((t) => t.tag === $TypeInfo.TYPE_SOMETHING);
            const oopts = expectedOpt.tag === $TypeInfo.TYPE_OPTION ? expectedOpt : expectedOpt.types.find((t) => t.tag === $TypeInfo.TYPE_OPTION);

            this.raiseErrorIf(sopts === undefined && oopts === undefined, `Relaxed type resolution cannot infer type for ${tname}`);
            this.raiseErrorIf(sopts !== undefined && oopts !== undefined, `Relaxed type resolution has ambiguous types for ${tname}`);
            t = (sopts ?? oopts).oftype;
        }

        return $TypeInfo.createSomething(t);
    } 
    else if(tname === "Option") {
        let t = $TypeInfo.unresolvedType;
        if(terms.length === 1) {
            t = terms[0];
        }
        else {
            this.raiseErrorIf(expectedOpt === undefined, `Relaxed type resolution required expected type information for ${tname}`);
            const oopts = expectedOpt.tag === $TypeInfo.TYPE_OPTION ? expectedOpt : expectedOpt.types.find((t) => t.tag === $TypeInfo.TYPE_OPTION);

            this.raiseErrorIf(oopts === undefined, `Relaxed type resolution cannot infer type for ${tname}`);
            t = oopts.oftype;
        }

        return $TypeInfo.createOption(t);
    } 
    else if(tname === "Path") {
        this.raiseErrorIf(terms.length !== 1, `Type ${tname} requires one type argument`);
        return $TypeInfo.createPath(terms[0]);
    } 
    else if(tname === "PathFragment") {
        this.raiseErrorIf(terms.length !== 1, `Type ${tname} requires one type argument`);
        return $TypeInfo.createPathFragment(terms[0]);
    } 
    else if(tname === "PathGlob") {
        this.raiseErrorIf(terms.length !== 1, `Type ${tname} requires one type argument`);
        return $TypeInfo.createPathGlob(terms[0]);
    }
    else {
        let ttag = $TypeInfo.TYPE_UNKNOWN;
        if (tname === "List") {
            ttag = $TypeInfo.TYPE_LIST;
        }
        else if (tname === "Stack") {
            ttag = $TypeInfo.TYPE_STACK;
        }
        else if (tname === "Queue") {
            ttag = $TypeInfo.TYPE_QUEUE;
        }
        else {
            ttag = $TypeInfo.TYPE_SET;
        }

        let t = $TypeInfo.unresolvedType;
        if (terms.length === 1) {
            t = terms[0];
        }
        else {
            this.raiseErrorIf(expectedOpt === undefined, `Relaxed type resolution required expected type information for ${tname}`);
            const oopts = expectedOpt.tag === ttag ? expectedOpt : expectedOpt.types.find((t) => t.tag === ttag);

            this.raiseErrorIf(oopts === undefined, `Relaxed type resolution cannot infer type for ${tname}`);
            t = oopts.oftype;
        }

        if (tname === "List") {
            return $TypeInfo.createList(t);
        }
        else if (tname === "Stack") {
            return $TypeInfo.createStack(t);
        }
        else if (tname === "Queue") {
            return $TypeInfo.createQueue(t);
        }
        else {
            this.raiseErrorIf(tinfo !== "Set", `Unknown core type ${tname}`);

            return $TypeInfo.createSet(t);
        }
    }
}
BSQONParse.prototype.processCoreTypeW2Terms = function (tname, terms, expectedOpt) {
    if(tname === "Result::Ok") {
        return $TypeInfo.createOk(t1, t2);
    } 
    else if(tname === "Result::Error") {
        return $TypeInfo.createError(t1, t2);
    } 
    else if(tname === "Result") {
        return $TypeInfo.createResult(t1, t2);
    } 
    else {
        let ttag = $TypeInfo.TYPE_UNKNOWN;
        if (tname === "MapEntry") {
            ttag = $TypeInfo.TYPE_MAP_ENTRY;
        }
        else {
            ttag = $TypeInfo.TYPE_MAP;
        }

        let k = $TypeInfo.unresolvedType;
        let v = $TypeInfo.unresolvedType;
        if (terms.length === 2) {
            k = terms[0];
            v = terms[1];
        }
        else {
            this.raiseErrorIf(expectedOpt === undefined, `Relaxed type resolution required expected type information for ${tname}`);
            const oopts = expectedOpt.tag === ttag ? expectedOpt : expectedOpt.types.find((t) => t.tag === ttag);

            this.raiseErrorIf(oopts === undefined, `Relaxed type resolution cannot infer type for ${tname}`);
            k = oopts.ktype;
            v = oopts.vtype;
        }

        if (tname === "MapEntry") {
            return $TypeInfo.createMapEntry(k, v);
        }
        else {
            this.raiseErrorIf(tname !== "Map", `Unknown core type ${tname}`);

            return $TypeInfo.createMap(k, v);
        }
    }
}
BSQONParse.prototype.parseNominalType = function (expectedOpt) {
    let tnames = [this.expectTokenAndPop(TOKEN_TYPE).value];
    while(this.testToken(TOKEN_COLONCOLON)) {
        this.popToken();
        tnames.push(this.expectTokenAndPop(TOKEN_TYPE).value);
    }

    let rname = this.resolveType(tnames);
    if(typeof(rname) !== "string") {
        this.raiseErrorIf(expectedOpt !== undefined && expectedOpt.tag !== rname.tag, `Expected ${expectedOpt.ttag} type: but got ${rname.tag}`);
        return rname;
    }
    else {
        let rtype = undefined;

        let terms = [];
        if(this.testToken(TOKEN_LANGLE)) {
            this.popToken();
            while(terms.length === 0 || this.testToken(TOKEN_COMMA)) {
                if(this.testToken(TOKEN_COMMA)) {
                    this.popToken();
                }

                terms.push(this.parseType());
            }
        }

        if (_s_core_types.includes(rname)) {
            this.raiseErrorIf(terms.length !== 0, `Type ${rname} does not take type arguments`);

            rtype = this.processCoreType(rname);
        }
        else if (_s_core_types_with_one_template.includes(rname)) {
            this.raiseErrorIf(this.isFullMode() && terms.length !== 1, `Type ${rname} requires one type argument`);

            rtype = this.processCoreTypeW1Term(rname, terms, expectedOpt);
        }
        else if (_s_core_types_with_two_templates.includes(rname)) {
            this.raiseErrorIf(this.isFullMode() && terms.length !== 2, `Type ${rname} requires two type arguments`);

            rtype = this.processCoreTypeW2Terms(rname, terms, expectedOpt);
        }
        else {
            this.raiseErrorIf(terms.length !== 0, `Type ${rname} does not take type arguments`);

            rtype = $TypeInfo.createSimpleNominal(rname);
        }

        this.raiseErrorIf(expectedOpt !== undefined && expectedOpt !== rtype, `Expected type ${expectedOpt.ttag}: but got ${rtype.ttag}`);
        return rtype;
    }
}
BSQONParse.prototype.parseTupleType = function (expectedOpt) {
    this.raiseErrorIf(expectedOpt !== undefined && expectedOpt.tag !== $TypeInfo.TYPE_TUPLE, `Expected ${expectedOpt.ttag} type: but found tuple type`);

    let entries = [];
    this.popToken();
    while(entries.length === 0 || this.testToken(TOKEN_COMMA)) {
        if(this.testToken(TOKEN_COMMA)) {
            this.popToken();
        }

        const eptype = undefined;
        if(expectedOpt !== undefined && entries.length < expectedOpt.entries.length) {
            const ee = expectedOpt.entries[entries.length];
            eptype = ee[1];
        }

        entries.push(this.parseType(eptype));
    }

    $TypeInfo.createTuple(entries);
}
BSQONParse.prototype.parseRecordType = function (expectedOpt) {
    this.raiseErrorIf(expectedOpt !== undefined && expectedOpt.tag !== TYPE_RECORD, `Expected ${expectedOpt.ttag} type: but found record type`);

    let entries = {};
    this.popToken();
    while(entries.length === 0 || this.testToken(TOKEN_COMMA)) {
        if(this.testToken(TOKEN_COMMA)) {
            this.popToken();
        }

        const pname = this.expectTokenAndPop(TOKEN_PROPERTY).value;

        const eptype = undefined;
        if(expectedOpt !== undefined && expectedOpt.entries.find((ee) => ee[0] === pname) !== undefined) {
            const ee = expectedOpt.entries.find((ee) => ee[0] === pname);
            eptype = ee[1];
        }

        entries[pname] = this.parseType(eptype);
    }

    $TypeInfo.createRecord(entries);
}
BSQONParse.prototype.parseBaseType = function (expectedOpt) {
    let rtype = undefined;

    if(this.testToken(TOKEN_LBRACKET)) {
        rtype = this.parseTupleType(expectedOpt);
    }
    else if(this.testToken(TOKEN_LBRACE)) {
        rtype = this.parseRecordType(expectedOpt);
    }
    else if(this.testToken(TOKEN_NAME)) {
        rtype = this.parseNominalType(expectedOpt);
    }
    else {
        this.raiseErrorIf(!this.testToken(TOKEN_LPAREN) `Expected type inside "(...)": but got ${tt}`);
        this.popToken();
        rtype = this.parseType();
        this.raiseErrorIf(!this.testToken(TOKEN_RPAREN) `Expected type inside "(...)": but got ${tt}`);
        this.popToken();
    }

    this.raiseErrorIf(expectedOpt !== undefined && expectedOpt !== rtype, `Expected type ${expectedOpt.ttag}: but got ${rtype.ttag}`);
    return rtype;
}
BSQONParse.prototype.parseConceptSetType = function (expectedOpt) {
    let rtype = undefined;

    const lt = this.parseBaseType();
    if(!this.testToken(TOKEN_AMP)) {
        rtype = lt;
    }
    else {
        let opts = [lt];
        while(this.testToken(TOKEN_AMP)) {
            this.popToken();
            opts.push(this.parseConceptSetType());
        } 

        rtype = $TypeInfo.createConceptSet(opts);
    }

    this.raiseErrorIf(expectedOpt !== undefined && expectedOpt !== rtype, `Expected type ${expectedOpt.ttag}: but got ${rtype.ttag}`);
    return rtype;
}
BSQONParse.prototype.parseUnionType = function (expectedOpt) {
    let rtype = undefined;

    const lt = this.parseConceptSetType();
    if(!this.testToken(TOKEN_BAR)) {
        rtype = lt;
    }
    else {
        let opts = [lt];
        while(this.testToken(TOKEN_BAR)) {
            this.popToken();
            opts.push(this.parseUnionType());
        } 

        rtype = $TypeInfo.createUnion(opts);
    }

    this.raiseErrorIf(expectedOpt !== undefined && expectedOpt !== rtype, `Expected type ${expectedOpt.ttag}: but got ${rtype.ttag}`);
    return rtype;
}
BSQONParse.prototype.parseType = function (expectedOpt) {
    if(!this.isJSONMode()) {
       return this.parseType(expectedOpt);
    }
    else {
        this.raiseErrorIf(this.testToken(TOKEN_STRING), `Expected type: but got ${tt}`);
        this.unquoteStringForTypeParse();

        return this.parseType(expectedOpt);
    }
}
BSQONParse.prototype.parseSrc = function (oftype, breq) {
    this.expectTokenAndPop(TOKEN_SRC);

    this.raiseErrorIf(this.m_srcbind === undefined, "Invalid use of $SRC binding");
    this.raiseErrorIf(!$TypeInfo.checkSubtype(this.m_assembly, this.m_srcbind[1], oftype), `Reference ${ref} has type ${this.m_srcbind[1].ttag} which is not a subtype of ${oftype.ttag}`);
    const rr = oftype.ttag === this.m_srcbind[1].ttag ? this.m_srcbind[0] : new $Runtime.UnionValue(this.m_srcbind[1], this.m_srcbind[0]);

    return createBSQONParseResult(rr, this.m_srcbind[1], this.m_srcbind[2], breq);
}
BSQONParse.prototype.parseReference = function (oftype, breq) {
    const ref = this.expectTokenAndPop(TOKEN_REFERENCE).value;

    this.raiseErrorIf(!this.m_refs.has(ref), `Reference ${ref} not found`);
    const rinfo = this.m_refs.get(ref);

    this.raiseErrorIf(!$TypeInfo.checkSubtype(this.m_assembly, rinfo[1], oftype), `Reference ${ref} has type ${rinfo[1].ttag} which is not a subtype of ${oftype.ttag}`);
    const rr = oftype.ttag === rinfo[1].ttag ? rinfo[0] : new $Runtime.UnionValue(rinfo[1], rinfo[0]);
    
    return createBSQONParseResult(rr, rinfo[1], rinfo[2], breq);
}
BSQONParse.prototype.parseBaseExpression = function (oftype, breq) {
    if(this.testToken(TOKEN_SRC)) {
        return this.parseSrc(oftype, breq);
    }
    else if(this.testToken(TOKEN_REFERENCE)) {
        return this.parseReference(oftype, breq);
    }
    else {
        this.expectTokenAndPop(TOKEN_LPAREN);
        const re = this.parseExpression(oftype, breq);
        this.expectTokenAndPop(TOKEN_RPAREN);

        return re;
    }
}
BSQONParse.prototype.parsePostfixOp = function (oftype, breq) {
    const bexp = this.parseBaseExpression(oftype, true);

    let vv = bexp;
    while(this.testToken(TOKEN_DOT_NAME) || this.testToken(TOKEN_DOT_IDX) || this.testToken(TOKEN_LBRACKET)) {
        let aval = undefined;
        let ptype = undefined;

        if(this.testToken(TOKEN_DOT_NAME)) {
            const iname = this.popToken().value.slice(1);
            const vval = getBSQONParseValue(vv);

            if(getBSQONParseInfo(vv).ctype === $TypeInfo.TYPE_RECORD) {
                aval = $TypeInfo.isUnionValueRepr(vval) ? vval[iname] : vval.value[iname];
                ptype = getBSQONParseInfo(vv).ttree[iname];
            }
            else if(getBSQONParseInfo(vv).ctype === $TypeInfo.TYPE_SIMPLE_ENTITY) {
                aval = $TypeInfo.isUnionValueRepr(vval) ? vval[iname] : vval.value[iname];
                ptype = getBSQONParseInfo(vv).ttree[iname];
            }
            else if(getBSQONParseInfo(vv).ctype === $TypeInfo.TYPE_MAP_ENTRY) {
                this.raiseErrorIf(iname !== "key" && iname !== "value", `Expected 'key' or 'value' property access but got ${iname}`);

                if(iname === "key") {
                    $TypeInfo.isUnionValueRepr(vval) ? vval[0] : vval.value[0];
                    ptype = getBSQONParseInfo(vv).ttree[0];
                }
                else if(iname === "value") {
                    $TypeInfo.isUnionValueRepr(vval) ? vval[1] : vval.value[1];
                    ptype = getBSQONParseInfo(vv).ttree[1];
                }
            }
            else {
                this.raiseError(`Invalid use of '.' operator -- ${getBSQONParseInfo(vv).ctype.ttag} is not a record, nominal, or map entry type`);
            }
        }
        else if(this.testToken(TOKEN_DOT_IDX)) {
            this.raiseErrorIf(getBSQONParseInfo(vv).ctype.tag !== $TypeInfo.TYPE_TUPLE, `Invalid use of '[]' operator -- ${getBSQONParseInfo(vv).ctype.ttag} is not a tuple type`);

            const idx = Number.parseInt(this.expectTokenAndPop(TOKEN_DOT_IDX).slice(1));
            const tuprepr = $TypeInfo.isUnionValueRepr(vval) ? vval : vval.value;
            
            this.raiseErrorIf(idx >= tuprepr.length, `Invalid use of '[]' operator -- index ${idx} is out of bounds for tuple type ${getBSQONParseInfo(vv).ctype.ttag}`);
            aval = tuprepr[idx];
            ptype = getBSQONParseInfo(vv).ttree[idx];
        }
        else {
            if(getBSQONParseInfo(vv).ctype.tag === $TypeInfo.TYPE_LIST) {
                this.expectTokenAndPop(TOKEN_LBRACKET);
                const eexp = this.parseExpression(this.m_assembly.types.get("Nat"), false);
                this.expectTokenAndPop(TOKEN_RBRACKET);

                const lrepr = $TypeInfo.isUnionValueRepr(vval) ? vval : vval.value;
                aval = lrepr.get(eexp);
                ptype = getBSQONParseInfo(vv).ttree[eexp];
            }
            //OTHER TYPES HERE
            else {
                this.raiseErrorIf(getBSQONParseInfo(vv).ctype.tag !== $TypeInfo.TYPE_MAP, `Invalid use of '[]' operator -- ${getBSQONParseInfo(vv).ctype.ttag} is not a map type`);

                this.expectTokenAndPop(TOKEN_LBRACKET);
                const eexp = this.parseExpression(getBSQONParseInfo(vv).ctype.ktype, false);
                this.expectTokenAndPop(TOKEN_RBRACKET);
                
                const lrepr = $TypeInfo.isUnionValueRepr(vval) ? vval : vval.value;
                aval = lrepr.get(eexp);
                ptype = getBSQONParseInfo(vv).ttree.get(eexp);
            }
        }

        vv = createBSQONParseResult(aval, ptype.ctype, ptype.ttree, true);
    }
        
    this.raiseErrorIf(!$TypeInfo.checkSubtype(this.m_assembly, getBSQONParseInfo(vv).ctype, oftype), `Reference ${ref} has type ${getBSQONParseInfo(vv).ctype.ttag} which is not a subtype of ${oftype.ttag}`);
    const rr = oftype.ttag === getBSQONParseInfo(vv).ctype ? getBSQONParseValue(vv) : new $Runtime.UnionValue(getBSQONParseValue(vv), getBSQONParseInfo(vv).ctype); 
    
    return createBSQONParseResult(rr, ...getBSQONParseInfo(vv), breq);
}
BSQONParse.prototype.parseExpression = function (oftype, breq) {
    return this.parsePostfixOp(oftype, breq);
}
BSQONParse.prototype.parseNone = function (breq) {
    if(!this.isJSONMode()) {
        this.expectTokenAndPop(TOKEN_NONE);
    }
    else {
        this.expectTokenAndPop(TOKEN_NULL);
    }
    return createBSQONParseResult(null, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "None"), undefined, breq);
}
BSQONParse.prototype.parseNothing = function (breq) {
    if(!this.isJSONMode()) {
        this.expectTokenAndPop(TOKEN_NOTHING);
    }
    else {
        this.expectTokenAndPop(TOKEN_NULL);
    }
    return createBSQONParseResult(undefined, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "Nothing"), undefined, breq);
}
BSQONParse.prototype.parseBool = function (breq) {
    const tk = this.popToken();
    return createBSQONParseResult(tk.type === TOKEN_TRUE, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "Bool"), undefined, breq);
}
BSQONParse.prototype.parseNat = function (breq) {
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
    this.raiseErrorIf(bv > $Constants.FIXED_NUMBER_MAX, `Nat value is larger than max value -- ${tkval}`);

    return createBSQONParseResult(bv, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "Nat"), undefined, breq);
}
BSQONParse.prototype.parseInt = function (breq) {
    let tkval = undefined;
    if(!this.isJSONMode()) {
        tkval = this.expectTokenAndPop(TOKEN_INT).value.slice(0, -1);
    }
    else {
        tkval = this.expectTokenAndPop(TOKEN_INT).value;
    }

    const bv = Number.parseInt(tkval);
    this.raiseErrorIf(Number.isNaN(bv) || !Number.isFinite(bv), `Expected finite Int number but got -- ${tkval}`);
    this.raiseErrorIf(bv < $Constants.FIXED_NUMBER_MIN, `Int value is smaller than min value -- ${tkval}`);
    this.raiseErrorIf(bv > $Constants.FIXED_NUMBER_MAX, `Int value is larger than max value -- ${tkval}`);
    
    return createBSQONParseResult(bv, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "Int"), undefined, breq);
}
BSQONParse.prototype.parseBigNat = function (breq) {
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

    return createBSQONParseResult(BigInt(tkval), $TypeInfo.resolveTypeInAssembly(this.m_assembly, "BigNat"), undefined, breq);
}
BSQONParse.prototype.parseBigInt = function (breq) {
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

    return createBSQONParseResult(BigInt(tkval), $TypeInfo.resolveTypeInAssembly(this.m_assembly, "BigInt"), undefined, breq);
}
BSQONParse.prototype.parseRational = function (breq) {
    let tkval = undefined;
    if(!this.isJSONMode()) {
        tkval = this.expectTokenAndPop(TOKEN_RATIONAL).value.slice(0, -1);
    }
    else {
        tkval = this.expectTokenAndPop(TOKEN_STRING).value.slice(1, -1);
        this.raiseErrorIf(!_s_rationalCheckRe.test(tkval), `Expected float but got ${tkval}`);
    }

    return createBSQONParseResult(Fraction(tkval), $TypeInfo.resolveTypeInAssembly(this.m_assembly, "Rational"), undefined, breq);
}
BSQONParse.prototype.parseFloat = function (breq) {
    let tkval = undefined;
    if(!this.isJSONMode()) {
        tkval = this.expectTokenAndPop(TOKEN_FLOAT).value.slice(0, -1);
    }
    else {
        tkval = this.expectTokenAndPop(TOKEN_FLOAT).value;
        this.raiseErrorIf(!_s_floatCheckRe.test(tkval), `Expected float but got ${tkval}`);
    }

    return createBSQONParseResult(Number.parseFloat(tkval), $TypeInfo.resolveTypeInAssembly(this.m_assembly, "Float"), undefined, breq);
}
BSQONParse.prototype.parseDecimal = function (breq) {
    let tkval = undefined;
    if(!this.isJSONMode()) {
        tkval = this.expectTokenAndPop(TOKEN_DECIMAL).value.slice(0, -1);
    }
    else {
        tkval = this.expectTokenAndPop(TOKEN_FLOAT).value;
        this.raiseErrorIf(!_s_floatCheckRe.test(tkval), `Expected decimal but got ${tkval}`);
    }

    return createBSQONParseResult(Decimal(tkval), $TypeInfo.resolveTypeInAssembly(this.m_assembly, "Decimal"), undefined, breq);
}
BSQONParse.prototype.parseString = function () {
    return createBSQONParseResult(this.expectTokenAndPop(TOKEN_STRING).value, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "String"), undefined, breq);
}
BSQONParse.prototype.parseASCIIString = function (breq) {
    let tkval = undefined;
    if(!this.isJSONMode()) {
        tkval = this.expectTokenAndPop(TOKEN_ASCII_STRING).value.slice(6, -1);
    }
    else {
        tkval = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_asciiStringCheckRe.test(tkval), `Expected ASCII string but got ${ts}`);
    }

    return createBSQONParseResult(tkval, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "ASCIIString"), undefined, breq);
}
BSQONParse.prototype.parseByteBuffer = function (breq) {
    let tbval = undefined;
    if(!this.isJSONMode()) {
        tbval = this.expectTokenAndPop(TOKEN_BYTE_BUFFER).value.slice(3, -1);
    }
    else {
        tbval = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_bytebuffCheckRe.test(tbval), `Expected byte buffer but got ${tb}`);
    }

    return createBSQONParseResult(tbval, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "ByteBuffer"), undefined, breq);
}
BSQONParse.prototype.parseDateTime = function (breq) {
    let dd = undefined;
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_ISO_DATE_TIME).value;
        dd = generateDateTime(tk);
        this.raiseErrorIf(dd === undefined, `Expected date+time but got ${tk}`);
    }
    else {
        const tk = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_fullTimeCheckRE.test(tk), `Expected date+time but got ${tk}`);

        dd = generateDateTime(tk);
        this.raiseErrorIf(dd === undefined, `Expected date+time but got ${tk}`);
    }

    return createBSQONParseResult(dd, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "DateTime"), undefined, breq);
}
BSQONParse.prototype.parseUTCDateTime = function (breq) {
    let dd = undefined;
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_ISO_UTC_DATE_TIME).value;
        dd = generateDateTime(tk);
        this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected UTC date+time but got ${tk}`);
    }
    else {
        const tk = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_fullTimeUTCCheckRE.test(tk), `Expected UTC date+time but got ${tk}`);

        dd = generateDateTime(tk);
        this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected UTC date+time but got ${tk}`);
    }

    return createBSQONParseResult(dd, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "UTCDateTime"), undefined, breq);
}
BSQONParse.prototype.parsePlainDate = function (breq) {
    let dd = undefined;
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_ISO_DATE).value;
        dd = generateDate(tk);
        this.raiseErrorIf(dd === undefined, `Expected plain date but got ${tk}`);
    }
    else {
        const tk = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_dateOnlyCheckRE.test(tk), `Expected plain date but got ${tk}`);

        dd = generateDate(tk);
        this.raiseErrorIf(dd === undefined, `Expected plain date but got ${tk}`);
    }

    return createBSQONParseResult(dd, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "PlainDate"), undefined, breq);
}
BSQONParse.prototype.parsePlainTime = function (breq) {
    let dd = undefined;
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_ISO_TIME).value;
        dd = generateTime(tk);
        this.raiseErrorIf(dd === undefined, `Expected plain time but got ${tk}`);
    }
    else {
        const tk = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_timeOnlyCheckRE.test(tk), `Expected plain time but got ${tk}`);

        dd = generateTime(tk);
        this.raiseErrorIf(dd === undefined, `Expected plain time but got ${tk}`);
    }

    return createBSQONParseResult(dd, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "PlainTime"), undefined, breq);
}
BSQONParse.prototype.parseTickTime = function (breq) {
    let tt = undefined;
    if(!this.isJSONMode()) {
        tt = this.expectTokenAndPop(TOKEN_TICK_TIME).value.slice(0, -1);
    }
    else {
        tt = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_tickTimeCheckRE.test(tt), `Expected tick time but got ${tt}`);
    }

    return createBSQONParseResult(new BigInt(tt), $TypeInfo.resolveTypeInAssembly(this.m_assembly, "TickTime"), undefined, breq);
}
BSQONParse.prototype.parseLogicalTime = function (breq) {
    let tt = undefined;
    if(!this.isJSONMode()) {
        tt = this.expectTokenAndPop(TOKEN_LOGICAL_TIME).value.slice(0, -1);
    }
    else {
        const tt = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_logicalTimeCheckRE.test(tt), `Expected logical time but got ${tt}`);
    }

    return createBSQONParseResult(new BigInt(tt), $TypeInfo.resolveTypeInAssembly(this.m_assembly, "LogicalTime"), undefined, breq);
}
BSQONParse.prototype.parseISOTimeStamp = function (breq) {
    let dd = undefined;
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_ISO_TIMESTAMP).value;
        dd = generateDateTime(tk);
        this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected timestamp but got ${tk}`);
    }
    else {
        const tk = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_isoStampCheckRE.test(tk), `Expected timestamp but got ${tk}`);

        dd = generateDateTime(tk);
        this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected timestamp but got ${tk}`);
    }

    return createBSQONParseResult(dd, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "ISOTimeStamp"), undefined, breq);
}
BSQONParse.prototype.parseUUIDv4 = function (breq) {
    let uuid = undefined;
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_UUID).value;
        this.raiseErrorIf(!tk.startsWith("uuid4{"), `Expected UUIDv4 but got ${tk}`);

        uuid = tk.slice(6, -1);
    }
    else {
        uuid = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_uuidCheckRE.test(tk), `Expected UUIDv4 but got ${uuid}`);
    }

    return createBSQONParseResult(uuid, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "UUIDv4"), undefined, breq);
}
BSQONParse.prototype.parseUUIDv7 = function (breq) {
    let uuid = undefined;
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_UUID).value;
        this.raiseErrorIf(!tk.startsWith("uuid7{"), `Expected UUIDv7 but got ${tk}`);

        uuid = tk.slice(6, -1);
    }
    else {
        uuid = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_uuidCheckRE.test(tk), `Expected UUIDv7 but got ${uuid}`);
    }

    return createBSQONParseResult(uuid, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "UUIDv7"), undefined, breq);
}
BSQONParse.prototype.parseSHAContentHash = function (breq) {
    let sh = undefined;
    if(!this.isJSONMode()) {
        sh = this.expectTokenAndPop(TOKEN_SHA_HASH).value.slice(5, -1);
    }
    else {
        sh = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_shahashCheckRE.test(tk), `Expected SHA3 512 hash but got ${sh}`);
    }

    return createBSQONParseResult(sh, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "SHAContentHash"), undefined, breq);
}
BSQONParse.prototype.parseLatLongCoordinate = function (breq) {
    let llc = undefined;
    if (!this.isJSONMode()) {
        const ttype = this.expectTokenAndPop(TOKEN_TYPE).value;
        this.raiseErrorIf(ttype !== "LatLongCoordinate", `Expected LatLongCoordinate but got ${ttype}`);

        this.expectTokenAndPop(TOKEN_LBRACE);
        const lat = this.parseFloat();
        this.expectTokenAndPop(TOKEN_COMMA);
        const long = this.parseFloat();
        this.expectTokenAndPop(TOKEN_RBRACE);

        llc = [lat, long];
    }
    else {
        this.expectTokenAndPop(TOKEN_LBRACKET);
        const lat = this.parseFloat();
        this.expectTokenAndPop(TOKEN_COMMA);
        const long = this.parseFloat();
        this.expectTokenAndPop(TOKEN_RBRACKET);

        llc = [lat, long];
    }

    return createBSQONParseResult(llc, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "LatLongCoordinate"), undefined, breq);
}
BSQONParse.prototype.parseStringOf = function (ttype, breq) {
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_STRING).value;
        const vv = this.parseType

        return tk.slice(7, -1);
    }
    else {

    }
}
BSQONParse.prototype.parseASCIIStringOf = function (ttype, breq) {
    xxxx;
}


export {
    BSQONParse, BSQONParseError
}
