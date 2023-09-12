import {Decimal} from "npm:decimal.js@10.4.3";
import Fraction from "npm:fraction.js@4.2.0";

import { List as IList, Map as IMap } from "npm:immutable@4.3.0";

import * as $Constants from "./constants.ts";
import * as $TypeInfo from "./typeinfo.ts";
import * as $Runtime from "./runtime.ts";


class BSQONParseError extends Error {
    readonly msg: string;
    readonly pos: number;

    constructor(message: string, pos: number) {
        super(`Parse Error -- ${message}`);
        Object.setPrototypeOf(this, new.target.prototype);

        this.msg = message;
        this.pos = pos;
    }
}

enum TokenKind {
    TOKEN_NULL = "null",
    TOKEN_NONE = "none",
    TOKEN_NOTHING = "nothing",
    TOKEN_TYPE = "type",
    TOKEN_SOMETHING = "something",
    TOKEN_OK = "ok",
    TOKEN_ERR = "err",

    TOKEN_LBRACE = "{",
    TOKEN_RBRACE = "}",
    TOKEN_LBRACKET = "[",
    TOKEN_RBRACKET = "]",
    TOKEN_LPAREN = "(",
    TOKEN_RPAREN = ")",
    TOKEN_LANGLE = "<",
    TOKEN_RANGLE = ">",
    TOKEN_COLON = ":",
    TOKEN_COLON_COLON = "::",
    TOKEN_COMMA = ",",
    TOKEN_AMP = "&",
    TOKEN_BAR = "|",
    TOKEN_ENTRY = "=>",
    TOKEN_LDOTS = "...",
    TOKEN_EQUALS = "=",
    TOKEN_LET = "let",
    TOKEN_IN = "in",

    TOKEN_SRC = "$SRC",
    TOKEN_REFERENCE = "#REF",
    TOKEN_PROPERTY = "PROPERTY",
    TOKEN_DOT_NAME = "DOT_NAME",
    TOKEN_DOT_IDX = "DOT_IDX",

    TOKEN_TRUE = "true", 
    TOKEN_FALSE = "false",
    TOKEN_NAT = "NAT",
    TOKEN_INT = "INT",
    TOKEN_BIG_NAT = "BIG_NAT",
    TOKEN_BIG_INT = "BIG_INT",
    TOKEN_FLOAT = "FLOAT",
    TOKEN_DECIMAL = "DECIMAL",
    TOKEN_RATIONAL = "RATIONAL",
    TOKEN_STRING = "STRING",
    TOKEN_ASCII_STRING = "ASCII_STRING",
    TOKEN_BYTE_BUFFER = "BYTE_BUFFER",
    TOKEN_REGEX = "REGEX",
    TOKEN_ISO_DATE_TIME = "DATE_TIME",
    TOKEN_ISO_UTC_DATE_TIME = "DATE_TIME_UTC",
    TOKEN_ISO_DATE = "DATE",
    TOKEN_ISO_TIME = "TIME",
    TOKEN_TICK_TIME = "TICK_TIME",
    TOKEN_LOGICAL_TIME = "LOGICAL_TIME",
    TOKEN_ISO_TIMESTAMP = "ISO_TIMESTAMP",
    TOKEN_UUID = "UUID",
    TOKEN_SHA_HASH = "HASH",
    TOKEN_PATH_ITEM = "PATH"
}

function createToken(kind: string, value: string): {kind: string, value: string} {
    return {
        kind: kind,
        value: value
    };
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

//TODO: needs support for the [TYPE] part and impl
const _s_pathRe = /(path|fragment|glob)\[[a-zA-Z0-9_:]\]\{[^\}]*\}/uy;

const _s_intRe = /(0|-?[1-9][0-9]*)i/y;
const _s_natRe = /(0|[1-9][0-9]*)n/y;

const _s_floatRe = /([+-]?[0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?f/y;
const _s_decimalRe = /([+-]?[0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?d/y;

const _s_bigintRe = /(0|-?[1-9][0-9]*)I/y;
const _s_bignatRe = /(0|[1-9][0-9]*)N/y;
const _s_rationalRe = /((0|-?[1-9][0-9]*)|(0|-?[1-9][0-9]*)\/([1-9][0-9]*))R/y;

const _s_intNumberinoRe = /0|-?[1-9][0-9]*/y;
const _s_floatNumberinoRe = /([+-]?[0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?/y;

const _s_stringRe = /"[^"]*"/uy;
const _s_ascii_stringRe = /ascii\{"[^]*"\}/uy;

const _s_regexRe = /\/[^"\\\r\n]*(\\(.)[^"\\\r\n]*)*\//y;
const _s_regexCheckRe = /^\/[^"\\\r\n]*(\\(.)[^"\\\r\n]*)*\/$/y;

const _s_keywordRe = /([a-z]*)/y;
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
    TokenKind.TOKEN_LBRACE,
    TokenKind.TOKEN_RBRACE,
    TokenKind.TOKEN_LBRACKET,
    TokenKind.TOKEN_RBRACKET,
    TokenKind.TOKEN_LPAREN,
    TokenKind.TOKEN_RPAREN,
    TokenKind.TOKEN_LANGLE, 
    TokenKind.TOKEN_RANGLE,

    //length 3
    TokenKind.TOKEN_LDOTS,

    //length 2
    TokenKind.TOKEN_COLON_COLON,
    TokenKind.TOKEN_ENTRY,

    //length 1
    TokenKind.TOKEN_COLON,
    TokenKind.TOKEN_AMP,
    TokenKind.TOKEN_BAR,
    TokenKind.TOKEN_COMMA,
    TokenKind.TOKEN_EQUALS
];

const KWStrings = [
    TokenKind.TOKEN_NULL,
    TokenKind.TOKEN_NONE,
    TokenKind.TOKEN_TRUE,
    TokenKind.TOKEN_FALSE,
    
    TokenKind.TOKEN_NOTHING,
    TokenKind.TOKEN_SOMETHING,
    TokenKind.TOKEN_OK,
    TokenKind.TOKEN_ERR,
    
    TokenKind.TOKEN_LET,
    TokenKind.TOKEN_IN
];


const _s_core_types = [
    "None", "Bool", "Int", "Nat", "BigInt", "BigNat", "Rational", "Float", "Decimal", "String", "ASCIIString",
    "ByteBuffer", "DateTime", "UTCDateTime", "PlainDate", "PlainTime", "TickTime", "LogicalTime", "ISOTimeStamp", "UUIDv4", "UUIDv7", "SHAContentHash", 
    "LatLongCoordinate", "Regex", "Nothing"
];

const _s_dateTimeNamedExtractRE = /^(?<year>[0-9]{4})-(?<month>[0-9]{2})-(?<day>[0-9]{2})T(?<hour>[0-9]{2}):(?<minute>[0-9]{2}):(?<second>[0-9]{2})\.(?<millis>[0-9]{3})(?<timezone>\[[a-zA-Z/ _-]+\]|Z)$/;

function _extractDateTimeYear(m: RegExpMatchArray): number | undefined {
    const year = Number.parseInt(m.groups!.year);
    return (1900 <= year && year <= 2200) ? year : undefined; 
}

function _extractDateTimeMonth(m: RegExpMatchArray): number | undefined {
    const month = Number.parseInt(m.groups!.month);
    return (0 <= month && month <= 11) ? month : undefined;
}

function _extractDateTimeDay(m: RegExpMatchArray): number | undefined {
    const year = Number.parseInt(m.groups!.year);
    const month = Number.parseInt(m.groups!.month);
    const day = Number.parseInt(m.groups!.day);
    
    if(month !== 1) {
        const mday = (month === 3 || month === 5 || month === 8 || month === 10) ? 30 : 31;
        return day <= mday ? day : undefined;
    }
    else {
        const isleapyear = !(year === 1900 || year === 2100 || year === 2200) && (year % 4 === 0);
        const mday = isleapyear ? 29 : 28;
        return day <= mday ? day : undefined;
    }
}

function _extractDateTimeHour(m: RegExpMatchArray): number | undefined {
    const hour = Number.parseInt(m.groups!.hour);
    return (0 <= hour && hour <= 23) ? hour : undefined;
}

function _extractDateTimeMinute(m: RegExpMatchArray): number | undefined {
    const minute = Number.parseInt(m.groups!.minute);
    return (0 <= minute && minute <= 59) ? minute : undefined;
}

function _extractDateTimeSecond(m: RegExpMatchArray): number | undefined {
    const second = Number.parseInt(m.groups!.second);
    return (0 <= second && second <= 60) ? second : undefined;
}

function _extractDateTimeMillis(m: RegExpMatchArray): number | undefined {
    const millis = Number.parseInt(m.groups!.millis);
    return (0 <= millis && millis <= 999) ? millis : undefined;
}

function _extractDateTimeTZ(m: RegExpMatchArray): string {
    const tzinfo = m.groups!.timezone;
    if(tzinfo === "Z") {
        return "UTC";
    }
    else {
        return tzinfo.slice(1, -1);
    }
}

function isValidBSQDate(dstr: string): boolean {
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

function generateDate(dstr: string): $Runtime.BSQDate | undefined {
    dstr = dstr + "T00:00:00.000Z";
    if(!isValidBSQDate(dstr)) {
        return undefined;
    }

    const m = _s_dateTimeNamedExtractRE.exec(dstr) as RegExpMatchArray;
    const year = _extractDateTimeYear(m) as number;
    const month = _extractDateTimeMonth(m) as number;
    const day = _extractDateTimeDay(m) as number;

    return new $Runtime.BSQDate(year, month, day);
}

function generateTime(dstr: string): $Runtime.BSQTime | undefined {
    dstr = "2000-01-01" + "T" + dstr + "Z";
    if(!isValidBSQDate(dstr)) {
        return undefined;
    }

    const m = _s_dateTimeNamedExtractRE.exec(dstr) as RegExpMatchArray;
    const hour = _extractDateTimeHour(m) as number;
    const minute = _extractDateTimeMinute(m) as number;
    const second = _extractDateTimeSecond(m) as number;
    const millis = _extractDateTimeMillis(m) as number;

    return new $Runtime.BSQTime(hour, minute, second, millis);
}

function generateDateTime(dstr: string): $Runtime.BSQDateTime | undefined {
    if(!isValidBSQDate(dstr)) {
        return undefined;
    }

    const m = _s_dateTimeNamedExtractRE.exec(dstr) as RegExpMatchArray;
    const year = _extractDateTimeYear(m) as number;
    const month = _extractDateTimeMonth(m) as number;
    const day = _extractDateTimeDay(m) as number;
    const hour = _extractDateTimeHour(m) as number;
    const minute = _extractDateTimeMinute(m) as number;
    const second = _extractDateTimeSecond(m) as number;
    const millis = _extractDateTimeMillis(m) as number;
    const tz = _extractDateTimeTZ(m) as string;

    return new $Runtime.BSQDateTime(year, month, day, hour, minute, second, millis, tz);
}

class BSQONParseResultInfo {
    readonly value: any;
    readonly vtype: $TypeInfo.BSQType;
    readonly parsetree: any;

    constructor(val: any, vtype: $TypeInfo.BSQType, parsetree: any) {
        this.value = val;
        this.vtype = vtype;
        this.parsetree = parsetree;
    }

    static create(val: any, vtype: $TypeInfo.BSQType, parsetree: any, whistory: boolean): BSQONParseResultInfo | any {
        if(!whistory) {
            return val;
        }
        else {
            return new BSQONParseResultInfo(val, vtype, parsetree);
        }
    }

    static getParseValue(parseinfo: any, whistory: boolean): any {
        return !whistory ? parseinfo : parseinfo.value;
    }
    
    static getValueType(parseinfo: any, whistory: boolean): $TypeInfo.BSQType {
        return !whistory ? undefined : parseinfo.vtype;
    }
    
    static getHistory(parseinfo: any, whistory: boolean): any {
        return !whistory ? undefined : parseinfo.parsetree;
    }
}

type BSQONParseResult = BSQONParseResultInfo | any;

class BSQONParser {
    readonly m_parsemode: $Runtime.NotationMode;

    readonly m_defaultns: string;
    readonly m_importmap: Map<string, string>;
    readonly m_assembly: $TypeInfo.AssemblyInfo;

    readonly m_input: string;
    m_cpos: number;
    m_lastToken: {kind: string, value: string} | undefined;

    readonly m_stdentityChecks: {etype: $TypeInfo.BSQTypeKey, evalue: object}[];
    readonly m_typedeclChecks: {ttype: $TypeInfo.BSQTypeKey, tvalue: any}[];

    readonly m_srcbind: [any, $TypeInfo.BSQType, any] | undefined; //a [value, type, ttree] where type is always a concrete type
    readonly m_refs: Map<string, [any, $TypeInfo.BSQType, any]>; //maps from names to [value, type, ttree] where type is always a concrete type

    constructor(mode: $Runtime.NotationMode, defaultns: string, importmap: Map<string, string>, assembly: $TypeInfo.AssemblyInfo, str: string, srcbind: [any, $TypeInfo.BSQType, any] | undefined) {
        this.m_parsemode = mode;

        this.m_defaultns = defaultns;
        this.m_importmap = importmap;
        this.m_assembly = assembly;

        this.m_input = str;
        this.m_cpos = 0;
        this.m_lastToken = undefined;

        this.m_stdentityChecks = [];
        this.m_typedeclChecks = [];

        this.m_srcbind = srcbind;
        this.m_refs = new Map<string, [any, $TypeInfo.BSQType, any]>();
    }

    private lookupMustDefType(tname: $TypeInfo.BSQTypeKey): $TypeInfo.BSQType {
        const rtype = this.m_assembly.typerefs.get(tname);
        this.raiseErrorIf(rtype === undefined, `Type ${tname} is not defined in this assembly`);

        return rtype as $TypeInfo.BSQType;
    }

    private unescapeString(str: string): string {
        return $Runtime.bsqonUnescapeString(str);
    }

    private lexWS() {
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

    private lexComment() {
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

    private lexBytebuff() {
        _s_bytebuffRe.lastIndex = this.m_cpos;
        const m = _s_bytebuffRe.exec(this.m_input);
        if (m === null) {
            return false;
        }
        else {
            this.m_cpos += m[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_BYTE_BUFFER, m[0]);
            return true;
        }
    }

    private lexTimeInfo() {
        _s_fullTimeRE.lastIndex = this.m_cpos;
        const ftm = _s_fullTimeRE.exec(this.m_input);
        if(ftm !== null) {
            this.m_cpos += ftm[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_ISO_DATE_TIME, ftm[0]);
            return true;
        }
    
        _s_fullTimeUTCRE.lastIndex = this.m_cpos;
        const ftutc = _s_fullTimeUTCRE.exec(this.m_input);
        if(ftutc !== null) {
            this.m_cpos += ftutc[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_ISO_UTC_DATE_TIME, ftutc[0]);
            return true;
        }
    
        _s_dateOnlyRE.lastIndex = this.m_cpos;
        const dm = _s_dateOnlyRE.exec(this.m_input);
        if(dm !== null) {
            this.m_cpos += dm[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_ISO_DATE, dm[0]);
            return true;
        }
    
        _s_timeOnlyRE.lastIndex = this.m_cpos;
        const tm = _s_timeOnlyRE.exec(this.m_input);
        if(tm !== null) {
            this.m_cpos += tm[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_ISO_TIME, tm[0]);
            return true;
        }
    
        return false;
    }

    private lexLogicalTime() {
        _s_logicalTimeRE.lastIndex = this.m_cpos;
        const m = _s_logicalTimeRE.exec(this.m_input);
        if (m === null) {
            return false;
        }
        else {
            this.m_cpos += m[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_LOGICAL_TIME, m[0]);
            return true;
        }
    }

    private lexTickTime() {
        _s_tickTimeRE.lastIndex = this.m_cpos;
        const m = _s_tickTimeRE.exec(this.m_input);
        if (m === null) {
            return false;
        }
        else {
            this.m_cpos += m[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_TICK_TIME, m[0]);
            return true;
        }
    }

    private lexISOTimestamp() {
        _s_isostampRE.lastIndex = this.m_cpos;
        const m = _s_isostampRE.exec(this.m_input);
        if (m === null) {
            return false;
        }
        else {
            this.m_cpos += m[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_ISO_TIMESTAMP, m[0]);
            return true;
        }
    }

    private lexUUID() {
        _s_uuidRE.lastIndex = this.m_cpos;
        const m = _s_uuidRE.exec(this.m_input);
        if (m === null) {
            return false;
        }
        else {
            this.m_cpos += m[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_UUID, m[0]);
            return true;
        }
    }

    private lexSHACode() {
        _s_shahashRE.lastIndex = this.m_cpos;
        const m = _s_shahashRE.exec(this.m_input);
        if (m === null) {
            return false;
        }
        else {
            this.m_cpos += m[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_SHA_HASH, m[0]);
            return true;
        }
    }

    private lexPath() {
        _s_pathRe.lastIndex = this.m_cpos;
        const m = _s_pathRe.exec(this.m_input);
        if (m === null) {
            return false;
        }
        else {
            this.m_cpos += m[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_PATH_ITEM, m[0]);
            return true;
        }
    }

    private lexNumber() {
        if (this.m_parsemode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
            _s_intNumberinoRe.lastIndex = this.m_cpos;
            const inio = _s_intNumberinoRe.exec(this.m_input);
            if (inio !== null) {
                this.m_cpos += inio[0].length;
                this.m_lastToken = createToken(TokenKind.TOKEN_INT, inio[0]);
                return true;
            }
    
            _s_floatNumberinoRe.lastIndex = this.m_cpos;
            const fnio = _s_floatNumberinoRe.exec(this.m_input);
            if (fnio !== null) {
                this.m_cpos += fnio[0].length;
                this.m_lastToken = createToken(TokenKind.TOKEN_FLOAT, fnio[0]);
                return true;
            }
        }
        else {
            _s_rationalRe.lastIndex = this.m_cpos;
            const mr = _s_rationalRe.exec(this.m_input);
            if (mr !== null) {
                this.m_cpos += mr[0].length;
                this.m_lastToken = createToken(TokenKind.TOKEN_RATIONAL, mr[0]);
                return true;
            }
    
            _s_bignatRe.lastIndex = this.m_cpos;
            const mbn = _s_bignatRe.exec(this.m_input);
            if (mbn !== null) {
                this.m_cpos += mbn[0].length;
                this.m_lastToken = createToken(TokenKind.TOKEN_BIG_NAT, mbn[0]);
                return true;
            }
    
            _s_bigintRe.lastIndex = this.m_cpos;
            const mbi = _s_bigintRe.exec(this.m_input);
            if (mbi !== null) {
                this.m_cpos += mbi[0].length;
                this.m_lastToken = createToken(TokenKind.TOKEN_BIG_INT, mbi[0]);
                return true;
            }
    
            _s_decimalRe.lastIndex = this.m_cpos;
            const md = _s_decimalRe.exec(this.m_input);
            if (md !== null) {
                this.m_cpos += md[0].length;
                this.m_lastToken = createToken(TokenKind.TOKEN_DECIMAL, md[0]);
                return true;
            }
    
            _s_floatRe.lastIndex = this.m_cpos;
            const mf = _s_floatRe.exec(this.m_input);
            if (mf !== null) {
                this.m_cpos += mf[0].length;
                this.m_lastToken = createToken(TokenKind.TOKEN_FLOAT, mf[0]);
                return true;
            }
    
            _s_natRe.lastIndex = this.m_cpos;
            const mn = _s_natRe.exec(this.m_input);
            if (mn !== null) {
                this.m_cpos += mn[0].length;
                this.m_lastToken = createToken(TokenKind.TOKEN_NAT, mn[0]);
                return true;
            }
    
            _s_intRe.lastIndex = this.m_cpos;
            const mi = _s_intRe.exec(this.m_input);
            if (mi !== null) {
                this.m_cpos += mi[0].length;
                this.m_lastToken = createToken(TokenKind.TOKEN_INT, mi[0]);
                return true;
            }
        }
    
        return false;
    }

    private lexString() {
        _s_stringRe.lastIndex = this.m_cpos;
        const ms = _s_stringRe.exec(this.m_input);
        if (ms !== null) {
            this.m_cpos += ms[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_STRING, ms[0]);
            return true;
        }
    
        if (this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            _s_ascii_stringRe.lastIndex = this.m_cpos;
            const mas = _s_ascii_stringRe.exec(this.m_input);
            if (mas !== null) {
                this.m_cpos += mas[0].length;
                this.m_lastToken = createToken(TokenKind.TOKEN_ASCII_STRING, mas[0]);
                return true;
            }
        }
    
        return false;
    }

    private lexRegex() {
        _s_regexRe.lastIndex = this.m_cpos;
        const ms = _s_regexRe.exec(this.m_input);
        if (ms !== null) {
            this.m_cpos += ms[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_REGEX, ms[0]);
            return true;
        }
    
        return false;
    }

    private lexSymbol() {
        _s_symbolRe.lastIndex = this.m_cpos;
        const ms = _s_symbolRe.exec(this.m_input);
        if (ms !== null) {
            const sym = SymbolStrings.find((value) => ms[0].startsWith(value));
            if (sym !== undefined) {
                this.m_cpos += sym.length;
                this.m_lastToken = createToken(sym, sym);
                return true;
            }
        }

        _s_keywordRe.lastIndex = this.m_cpos;
        const mk = _s_keywordRe.exec(this.m_input);
        if (mk !== null) {
            const kw = KWStrings.find((value) => mk[0].startsWith(value));
            if (kw !== undefined) {
                this.m_cpos += kw.length;
                this.m_lastToken = createToken(kw, kw);
                return true;
            }
        }
    
        return false;
    }

    private lexName() {
        _s_nameSrcRe.lastIndex = this.m_cpos;
        const msrc = _s_nameSrcRe.exec(this.m_input);
        if(msrc !== null) {
            this.m_cpos += msrc[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_SRC, msrc[0]);
            return true;
        }
    
        _s_nameRefRe.lastIndex = this.m_cpos;
        const mref = _s_nameRefRe.exec(this.m_input);
        if(mref !== null) {
            this.m_cpos += mref[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_REFERENCE, mref[0]);
            return true;
        }
    
        _s_nameTypeRe.lastIndex = this.m_cpos;
        const mtype = _s_nameTypeRe.exec(this.m_input);
        if(mtype !== null) {
            this.m_cpos += mtype[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_TYPE, mtype[0]);
            return true;
        }
    
        _s_namePropertyRE.lastIndex = this.m_cpos;
        const pname = _s_namePropertyRE.exec(this.m_input);
        if(pname !== null) {
            this.m_cpos += pname[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_PROPERTY, pname[0]);
            return true;
        }
    
        return false;
    }

    private lexAccess() {
        _s_dotNameAccessRe.lastIndex = this.m_cpos;
        const dotname = _s_dotNameAccessRe.exec(this.m_input);
        if(dotname !== null) {
            this.m_cpos += dotname[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_DOT_NAME, dotname[0].slice(1));
            return true;
        }
    
        _s_dotIdxAccessRe.lastIndex = this.m_cpos;
        const dotidx = _s_dotIdxAccessRe.exec(this.m_input);
        if(dotidx !== null) {
            this.m_cpos += dotidx[0].length;
            this.m_lastToken = createToken(TokenKind.TOKEN_DOT_IDX, dotidx[0].slice(1));
            return true;
        }
    
        return false;
    }


    private peekToken(): {kind: string, value: string} | undefined {
        if (this.m_lastToken !== undefined) {
            return this.m_lastToken;
        }

        while (this.lexWS() || this.lexComment()) {
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

    private popToken(): {kind: string, value: string} | undefined {
        const tt = this.peekToken();
        
        this.m_lastToken = undefined;
        return tt;
    }

    private popTokenSafe(): {kind: string, value: string} {
        return this.popToken()!;
    }

    private testToken(tkind: string): boolean {
        return this.peekToken() !== undefined && this.peekToken()!.kind === tkind;
    }

    private testTokens(...tkinds: string[]): boolean {
        const opos = this.m_cpos;
        const olt = this.m_lastToken;

        for (let i = 0; i < tkinds.length; ++i) {
            if (this.testToken(tkinds[i])) {
                this.popToken();
            }
            else {
                this.m_cpos = opos;
                this.m_lastToken = olt;

                return false;
            }
        }

        this.m_cpos = opos;
        this.m_lastToken = olt;
        return true;
    }

    private testTokenWValue(tk: {kind: TokenKind, value: string}): boolean {
        return this.peekToken() !== undefined && this.peekToken()!.kind === tk.kind && this.peekToken()!.value === tk.value;
    }

    private testTokensWValue(...tks: {kind: TokenKind, value: string}[]): boolean {
        const opos = this.m_cpos;
        const olt = this.m_lastToken;

        for (let i = 0; i < tks.length; ++i) {
            if (!this.testTokenWValue(tks[i])) {
                this.m_cpos = opos;
                this.m_lastToken = olt;

                return false;
            }
        }

        this.m_cpos = opos;
        this.m_lastToken = olt;
        return true;
    }

    private raiseError(msg: string) {
        const mm = this.m_input.slice(0, this.m_cpos).match(/[\n]/g);
        throw new BSQONParseError(msg, (mm?.length ?? 0) + 1);
    }

    private raiseErrorIf(cond: boolean, msg: string) {
        if (cond) {
            this.raiseError(msg);
        }
    }

    private expectToken(tkind: string) {
        this.raiseErrorIf(!this.testToken(tkind), `Expected token ${tkind} but got ${this.peekToken()?.value ?? "[Unknown]"}`);
    }

    private expectTokenAndPop(tkind: string): {kind: string, value: string} {
        this.expectToken(tkind);
        return this.popToken() as {kind: string, value: string};
    }

    private testAndPop_TypedeclUnder(): boolean {
        if(this.m_cpos < this.m_input.length && this.m_input[this.m_cpos] !== "_", "Expected token _") {
            return false;
        }
        else {
            this.raiseErrorIf(this.m_cpos >= this.m_input.length || this.m_input[this.m_cpos] !== "_", "Expected token _");
            this.m_cpos += 1;
            this.m_lastToken = undefined;

            return true;
        }
    }

    private resolveTypeFromNameList(tt: string[], terms: $TypeInfo.BSQType[]): $TypeInfo.BSQType  {
        let scopedname = "[uninit]";

        if (this.m_assembly.namespaces.get("Core")!.typenames.includes(tt.join("::"))) {
            scopedname = tt.join("::");
        }
        else if (this.m_importmap.has(tt[0])) {
            scopedname = `${this.m_importmap.get(tt[0])}::${tt.slice(1).join("::")}`;
        }
        else {
            if (this.m_assembly.namespaces.has(tt[0])) {
                scopedname = tt.join("::");
            }
            else {
                scopedname = `${this.m_defaultns}::${tt.join("::")}`;
            }
        }

        if (terms.length !== 0) {
            scopedname = scopedname + `<${terms.map((t) => t.tkey).join(", ")}>`;
        }

        if (!this.m_assembly.aliasmap.has(scopedname)) {
            return this.m_assembly.typerefs.get(scopedname) as $TypeInfo.BSQType;
        }
        else {
            return this.m_assembly.aliasmap.get(scopedname) as $TypeInfo.BSQType;
        }
    }

    private processCoreType(tname: string): $TypeInfo.BSQType {
        const ttk = this.popToken()!.value;
        this.raiseErrorIf(!_s_core_types.includes(ttk), `Invalid core type ${ttk}`);

        return this.resolveTypeFromNameList([tname], []);
    }

    private parseTemplateTerm(): $TypeInfo.BSQType | undefined {
        if(!this.testToken(TokenKind.TOKEN_LANGLE)) {
            return undefined;
        }

        this.expectTokenAndPop(TokenKind.TOKEN_LANGLE);
        const ttype = this.parseType();
        this.expectTokenAndPop(TokenKind.TOKEN_RANGLE);

        return ttype;
    }

    private parseTemplateTermPair(): [$TypeInfo.BSQType, $TypeInfo.BSQType] | undefined {
        if(!this.testToken(TokenKind.TOKEN_LANGLE)) {
            return undefined;
        }

        this.expectTokenAndPop(TokenKind.TOKEN_LANGLE);
        const ttype1 = this.parseType();
        this.expectTokenAndPop(TokenKind.TOKEN_COMMA);
        const ttype2 = this.parseType();
        this.expectTokenAndPop(TokenKind.TOKEN_RANGLE);

        return [ttype1, ttype2];
    }

    private parseStringOfType(): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "StringOf", `Not a StringOf type`);

        const oftype = this.parseTemplateTerm();
        this.raiseErrorIf(oftype === undefined || !(oftype instanceof $TypeInfo.ValidatorREType), `Type StringOf requires a validator type argument`);

        return this.lookupMustDefType(`StringOf<${(oftype as $TypeInfo.ValidatorREType).tkey}>`);
    }

    private parseASCIIStringOfType(): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "ASCIIStringOf", `Not a ASCIIStringOf type`);

        const oftype = this.parseTemplateTerm();
        this.raiseErrorIf(oftype === undefined || !(oftype instanceof $TypeInfo.ValidatorREType), `Type ASCIIStringOf requires a validator type argument`);

        return this.lookupMustDefType(`ASCIIStringOf<${(oftype as $TypeInfo.ValidatorREType).tkey}>`);
    }

    private parseSomethingType(opt: $TypeInfo.SomethingType | $TypeInfo.OptionType | undefined): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Something", `Not a Something type`);

        return this.parseSomethingTypeComplete(opt);
    }

    private parseSomethingTypeComplete(opt: $TypeInfo.SomethingType | $TypeInfo.OptionType | undefined): $TypeInfo.BSQType {
        const oftype = this.parseTemplateTerm();
        if(oftype !== undefined) {
            const t = this.lookupMustDefType(`Something<${oftype.tkey}>`);
            this.raiseErrorIf(opt !== undefined && !this.m_assembly.checkConcreteSubtype(t, opt), `Type ${t.tkey} is not a subtype of expected type`);

            return t;
        }
        else {
            this.raiseErrorIf(opt === undefined, `Type Something requires one type argument *OR* can be used in a inferable context`);
            const t = this.lookupMustDefType(`Something<${opt!.oftype}>`);

            return t;
        }
    }

    private parseOptionType(): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Option", `Not a Option type`);

        const oftype = this.parseTemplateTerm();
        this.raiseErrorIf(oftype === undefined, `Type Option requires a type argument`);

        return this.lookupMustDefType(`Option<${(oftype as $TypeInfo.BSQType).tkey}>`);
    }

    private parsePathType(): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Path", `Not a Path type`);

        const oftype = this.parseTemplateTerm();
        this.raiseErrorIf(oftype === undefined || !(oftype instanceof $TypeInfo.ValidatorPthType), `Type Path requires a validator type argument`);

        return this.lookupMustDefType(`Path<${(oftype as $TypeInfo.ValidatorPthType).tkey}>`);
    }

    private parsePathFragmentType(): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "PathFragement", `Not a PathFragment type`);

        const oftype = this.parseTemplateTerm();
        this.raiseErrorIf(oftype === undefined || !(oftype instanceof $TypeInfo.ValidatorPthType), `Type PathFragement requires a validator type argument`);

        return this.lookupMustDefType(`PathFragment<${(oftype as $TypeInfo.ValidatorPthType).tkey}>`);
    }

    private parsePathGlobType(): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "PathGlob", `Not a PathGlob type`);

        const oftype = this.parseTemplateTerm();
        this.raiseErrorIf(oftype === undefined || !(oftype instanceof $TypeInfo.ValidatorPthType), `Type PathGlob requires a validator type argument`);

        return this.lookupMustDefType(`PathGlob<${(oftype as $TypeInfo.ValidatorPthType).tkey}>`);
    }

    private parseListType(opt: $TypeInfo.ListType | undefined): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "List", `Not a List type`);

        const oftype = this.parseTemplateTerm();
        if(oftype !== undefined) {
            const t = this.lookupMustDefType(`List<${oftype.tkey}>`);
            this.raiseErrorIf(opt !== undefined && !this.m_assembly.checkConcreteSubtype(t, opt), `Type ${t.tkey} is not a subtype of expected type`);

            return t;
        }
        else {
            this.raiseErrorIf(opt === undefined, `Type List requires one type argument *OR* can be used in a inferable context`);
            const t = this.lookupMustDefType(`List<${opt!.oftype}>`);

            return t;
        }
    }

    private parseStackType(opt: $TypeInfo.StackType | undefined): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Stack", `Not a Stack type`);

        const oftype = this.parseTemplateTerm();
        if(oftype !== undefined) {
            const t = this.lookupMustDefType(`Stack<${oftype.tkey}>`);
            this.raiseErrorIf(opt !== undefined && !this.m_assembly.checkConcreteSubtype(t, opt), `Type ${t.tkey} is not a subtype of expected type`);

            return t;
        }
        else {
            this.raiseErrorIf(opt === undefined, `Type Stack requires one type argument *OR* can be used in a inferable context`);
            const t = this.lookupMustDefType(`Stack<${opt!.oftype}>`);

            return t;
        }
    }

    private parseQueueType(opt: $TypeInfo.QueueType | undefined): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Queue", `Not a Queue type`);

        const oftype = this.parseTemplateTerm();
        if(oftype !== undefined) {
            const t = this.lookupMustDefType(`Queue<${oftype.tkey}>`);
            this.raiseErrorIf(opt !== undefined && !this.m_assembly.checkConcreteSubtype(t, opt), `Type ${t.tkey} is not a subtype of expected type`);

            return t;
        }
        else {
            this.raiseErrorIf(opt === undefined, `Type Queue requires one type argument *OR* can be used in a inferable context`);
            const t = this.lookupMustDefType(`Queue<${opt!.oftype}>`);

            return t;
        }
    }

    private parseSetType(opt: $TypeInfo.SetType | undefined): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Set", `Not a Set type`);

        const oftype = this.parseTemplateTerm();
        if(oftype !== undefined) {
            const t = this.lookupMustDefType(`Set<${oftype.tkey}>`);
            this.raiseErrorIf(opt !== undefined && !this.m_assembly.checkConcreteSubtype(t, opt), `Type ${t.tkey} is not a subtype of expected type`);

            return t;
        }
        else {
            this.raiseErrorIf(opt === undefined, `Type Set requires one type argument *OR* can be used in a inferable context`);
            const t = this.lookupMustDefType(`Set<${opt!.oftype}>`);

            return t;
        }
    }

    private parseMapEntryType(): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "MapEntry", `Not a MapEntry type`);

        const kvtype = this.parseTemplateTermPair();
        this.raiseErrorIf(kvtype === undefined, `Type MapEntry requires two type arguments`);

        return this.lookupMustDefType(`MapEntry<${kvtype![0].tkey}, ${kvtype![1].tkey}>`);
    }

    private parseMapType(opt: $TypeInfo.MapType | undefined): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Map", `Not a Map type`);

        const kvtype = this.parseTemplateTermPair();
        if(kvtype !== undefined) {
            const t = this.lookupMustDefType(`Map<${kvtype[0].tkey}, ${kvtype[1].tkey}>`);
            this.raiseErrorIf(opt !== undefined && !this.m_assembly.checkConcreteSubtype(t, opt), `Type ${t.tkey} is not a subtype of expected type`);

            return t;
        }
        else {
            this.raiseErrorIf(opt === undefined, `Type Map requires two type arguments *OR* can be used in a inferable context`);
            const t = this.lookupMustDefType(`Map<${opt!.ktype}, ${opt!.vtype}>`);

            return t;
        }
    }

    private parseOkType(opt: $TypeInfo.OkType | $TypeInfo.ResultType | undefined): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Result", `Not a Result::Ok type`);

        const tts = this.parseTemplateTermPair();
        const okn = this.popToken()!.value;
        this.raiseErrorIf(okn !== "Ok", `Not a Result::Ok type`);

        return this.parseOkTypeComplete(tts, opt);
    }

    private parseOkTypeComplete(tts: [$TypeInfo.BSQType, $TypeInfo.BSQType] | undefined, opt: $TypeInfo.OkType | $TypeInfo.ResultType | undefined): $TypeInfo.BSQType {
       if(tts !== undefined) {
            const t = this.lookupMustDefType(`Result<${tts[0].tkey}, ${tts[1].tkey}>::Ok`);
            this.raiseErrorIf(opt !== undefined && !this.m_assembly.checkConcreteSubtype(t, opt), `Type ${t.tkey} is not a subtype of expected type`);

            return t;
        }
        else {
            this.raiseErrorIf(opt === undefined, `Type Result::Ok requires two type arguments *OR* can be used in a inferable context`);
            const t = this.lookupMustDefType(`Result<${opt!.ttype}, ${opt!.etype}>::Ok`);

            return t;
        }
    }

    private parseErrType(opt: $TypeInfo.ErrorType | $TypeInfo.ResultType | undefined): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Result", `Not a Result::Err type`);

        const tts = this.parseTemplateTermPair();
        const okn = this.popToken()!.value;
        this.raiseErrorIf(okn !== "Err", `Not a Result::Err type`);

        return this.parseErrTypeComplete(tts, opt);
    }

    private parseErrTypeComplete(tts: [$TypeInfo.BSQType, $TypeInfo.BSQType] | undefined, opt: $TypeInfo.ErrorType | $TypeInfo.ResultType | undefined): $TypeInfo.BSQType {
        if(tts !== undefined) {
            const t = this.lookupMustDefType(`Result<${tts[0].tkey}, ${tts[1].tkey}>::Err`);
            this.raiseErrorIf(opt !== undefined && !this.m_assembly.checkConcreteSubtype(t, opt), `Type ${t.tkey} is not a subtype of expected type`);

            return t;
        }
        else {
            this.raiseErrorIf(opt === undefined, `Type Result::Err requires two type arguments *OR* can be used in a inferable context`);
            const t = this.lookupMustDefType(`Result<${opt!.ttype}, ${opt!.etype}>::Err`);

            return t;
        }
    }

    private parseResultTypeComplete(tts: [$TypeInfo.BSQType, $TypeInfo.BSQType]): $TypeInfo.BSQType {
        return this.lookupMustDefType(`Result<${tts[0].tkey}, ${tts[1].tkey}>`);
    }

    private isNominalTypePrefix(): boolean {
        const ntok = this.peekToken();
        return ntok !== undefined && ntok.kind === TokenKind.TOKEN_TYPE;
    }

    private parseNominalType(): $TypeInfo.BSQType {
        const ntok = this.peekToken();
        this.raiseErrorIf(ntok === undefined || ntok.kind !== TokenKind.TOKEN_TYPE, `Expected nominal type name but found ${ntok?.value ?? "EOF"}`);

        const tname = ntok!.value;
        if (_s_core_types.includes(tname)) {
            return this.processCoreType(tname);
        }
        else if (tname === "StringOf") {
            return this.parseStringOfType();
        }
        else if (tname === "ASCIIStringOf") {
            return this.parseASCIIStringOfType();
        }
        else if (tname === "Something") {
            return this.parseSomethingType(undefined);
        }
        else if (tname === "Option") {
            return this.parseOptionType();
        }
        else if (tname === "Path") {
            return this.parsePathType();
        }
        else if (tname === "PathFragment") {
            return this.parsePathFragmentType();
        }
        else if (tname === "PathGlob") {
            return this.parsePathGlobType();
        }
        else if (tname === "List") {
            return this.parseListType(undefined);
        }
        else if (tname === "Stack") {
            return this.parseStackType(undefined);
        }
        else if (tname === "Queue") {
            return this.parseQueueType(undefined);
        }
        else if (tname === "Set") {
            return this.parseSetType(undefined);
        }
        else if (tname === "MapEntry") {
            return this.parseMapEntryType();
        }
        else if (tname === "Set") {
            return this.parseMapType(undefined);
        }
        else if (tname === "Result") {
            this.popToken();
            const tts = this.parseTemplateTermPair();

            if (!this.testToken(TokenKind.TOKEN_COLON_COLON)) {
                this.raiseErrorIf(tts === undefined, `Type Result requires two type arguments`);
                return this.parseResultTypeComplete(tts!);
            }
            else {
                this.expectTokenAndPop(TokenKind.TOKEN_COLON_COLON);
                const tname = this.expectTokenAndPop(TokenKind.TOKEN_TYPE).value;
                this.raiseErrorIf(tname !== "Ok" && tname !== "Err", `Unknown type (expected Ok or Err)`);

                if(tname === "Ok") {
                    return this.parseOkTypeComplete(tts, undefined);
                }
                else {
                    return this.parseErrTypeComplete(tts, undefined);
                }
            }
        }
        else {
            this.popToken();
            let tnames = [tname];
            while (this.testTokens(TokenKind.TOKEN_COLON_COLON, TokenKind.TOKEN_TYPE)) {
                this.popToken();
                tnames.push(this.expectTokenAndPop(TokenKind.TOKEN_TYPE).value);
            }

            let terms: $TypeInfo.BSQType[] = [];
            if (this.testToken(TokenKind.TOKEN_LANGLE)) {
                this.popToken();

                while (terms.length === 0 || this.testToken(TokenKind.TOKEN_COMMA)) {
                    if (this.testToken(TokenKind.TOKEN_COMMA)) {
                        this.popToken();
                    }

                    terms.push(this.parseType());
                }
                this.expectTokenAndPop(TokenKind.TOKEN_RANGLE);
            }

            const lltype = this.resolveTypeFromNameList(tnames, terms);
            this.raiseErrorIf(lltype === undefined, `Could not resolve nominal type ${tnames.join("::")}`);

            return lltype;
        }
    }

    private parseTupleType(): $TypeInfo.BSQType {
        let entries: $TypeInfo.BSQType[] = [];
        this.popToken();
        if(this.testToken(TokenKind.TOKEN_RBRACKET)) {
            return this.lookupMustDefType("[]");
        }
        else {
            let first = true;
            while (first || this.testToken(TokenKind.TOKEN_COMMA)) {
                if(first) {
                    first = false;
                }
                else {
                    this.popToken();
                }
                
                entries.push(this.parseType());
            }
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

            return this.lookupMustDefType(`[${entries.map((ee) => ee.tkey).join(", ")}]`);
        }
    }

    private parseRecordType(): $TypeInfo.BSQType {
        let entries: {pname: string, rtype: $TypeInfo.BSQType}[] = [];
        this.popToken();
        if(this.testToken(TokenKind.TOKEN_RBRACE)) {
            return this.lookupMustDefType("{}");
        }
        else {
            let first = true;
            while (first || this.testToken(TokenKind.TOKEN_COMMA)) {
                if(first) {
                    first = false;
                }
                else {
                    this.popToken();
                }
                
                const pname = this.expectTokenAndPop(TokenKind.TOKEN_PROPERTY).value;
                const rtype = this.parseType();
                entries.push({ pname: pname, rtype: rtype });
            }
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

            const ees = entries.sort((a, b) => ((a.pname !== b.pname) ? (a.pname < b.pname ? -1 : 1) : 0)).map((ee) => `${ee.pname}: ${ee.rtype.tkey}`);
            return this.lookupMustDefType(`{${ees.join(", ")}}`);
        }
    }

    private parseBaseType(): $TypeInfo.BSQType {
        if (this.testToken(TokenKind.TOKEN_TYPE)) {
            return this.parseNominalType();
        }
        else if (this.testToken(TokenKind.TOKEN_LBRACKET)) {
            return this.parseTupleType();
        }
        else if (this.testToken(TokenKind.TOKEN_LBRACE)) {
            return this.parseRecordType();
        }
        else {
            this.raiseError(`Unexpected token when parsing type: ${this.peekToken()?.value ?? "EOF"}`);
            return $TypeInfo.UnresolvedType.singleton;
        }
    }

    private parseConceptSetType(): $TypeInfo.BSQType {
        const lt = this.parseBaseType();
        if (!this.testToken(TokenKind.TOKEN_AMP)) {
            return lt;
        }
        else {
            let opts = [lt];
            while (this.testToken(TokenKind.TOKEN_AMP)) {
                this.popToken();
                opts.push(this.parseConceptSetType());
            }

            return this.lookupMustDefType(opts.map((tt) => tt.tkey).sort((a, b) => ((a !== b) ? (a < b ? -1 : 1) : 0)).join("&"));
        }
    }

    private parseUnionType(): $TypeInfo.BSQType {
        const lt = this.parseConceptSetType();
        if (!this.testToken(TokenKind.TOKEN_BAR)) {
            return lt;
        }
        else {
            let opts = [lt];
            while (this.testToken(TokenKind.TOKEN_BAR)) {
                this.popToken();
                opts.push(this.parseUnionType());
            }

            return this.lookupMustDefType(opts.map((tt) => tt.tkey).sort((a, b) => ((a !== b) ? (a < b ? -1 : 1) : 0)).join(" | "));
        }
    }

    private parseType(): $TypeInfo.BSQType {
        if (this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return this.parseUnionType();
        }
        else {
            this.raiseErrorIf(this.testToken(TokenKind.TOKEN_STRING), `Expected type: but got ${this.peekToken()?.value ?? "EOF"}`);
            this.m_cpos++; //eat the "
            const tt = this.parseUnionType();
            this.m_cpos++; //eat the "

            return tt;
        }
    }

    private peekType(): $TypeInfo.BSQType {
        const opos = this.m_cpos;
        const olt = this.m_lastToken;

        const tt = this.parseType();

        this.m_lastToken = olt;
        this.m_cpos = opos;

        return tt;
    }

    private parseSrc(oftype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        this.expectTokenAndPop(TokenKind.TOKEN_SRC);

        this.raiseErrorIf(this.m_srcbind === undefined, "Invalid use of $SRC binding");
        this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(this.m_srcbind![1], oftype), `Reference $src has type ${this.m_srcbind![1].tkey} which is not a subtype of ${oftype.tkey}`);
        const rr = oftype.isconcretetype ? this.m_srcbind![0] : new $Runtime.UnionValue(this.m_srcbind![1].tkey, this.m_srcbind![0]);

        return BSQONParseResultInfo.create(rr, this.m_srcbind![1], this.m_srcbind![2], whistory);
    }

    private parseReference(oftype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        const ref = this.expectTokenAndPop(TokenKind.TOKEN_REFERENCE).value;

        this.raiseErrorIf(!this.m_refs.has(ref), `Reference ${ref} not found`);
        const rinfo = this.m_refs.get(ref);

        this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(rinfo![1], oftype), `Reference ${ref} has type ${rinfo![1].tkey} which is not a subtype of ${oftype.tkey}`);
        const rr = oftype.isconcretetype ? rinfo![0] : new $Runtime.UnionValue(rinfo![1].tkey, rinfo![0]);

        return BSQONParseResultInfo.create(rr, rinfo![1], rinfo![2], whistory);
    }

    private parseBaseExpression(oftype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        if (this.testToken(TokenKind.TOKEN_SRC)) {
            return this.parseSrc(oftype, whistory);
        }
        else if (this.testToken(TokenKind.TOKEN_REFERENCE)) {
            return this.parseReference(oftype, whistory);
        }
        else {
            this.expectTokenAndPop(TokenKind.TOKEN_LPAREN);
            const re = this.parseExpression(oftype, whistory);
            this.expectTokenAndPop(TokenKind.TOKEN_RPAREN);

            return re;
        }
    }

    private parsePostfixOp(oftype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        const bexp = this.parseBaseExpression(oftype, true);

        let vv = bexp;
        while (this.testToken(TokenKind.TOKEN_DOT_NAME) || this.testToken(TokenKind.TOKEN_DOT_IDX) || this.testToken(TokenKind.TOKEN_LBRACKET)) {
            let aval: any = undefined;
            let ptype: $TypeInfo.BSQType = $TypeInfo.UnresolvedType.singleton;
            let ptree: any = undefined;

            const vval = BSQONParseResultInfo.getParseValue(vv, true);
            const vtype = BSQONParseResultInfo.getValueType(vv, true)
            if (this.testToken(TokenKind.TOKEN_DOT_NAME)) {
                const iname = this.popTokenSafe().value.slice(1);

                if (vtype.tag === $TypeInfo.BSQTypeTag.TYPE_RECORD) {
                    aval = vtype.isconcretetype ? vval[iname] : vval.value[iname];
                    ptype = BSQONParseResultInfo.getHistory(vv, true)[iname][0];
                    ptree = BSQONParseResultInfo.getHistory(vv, true)[iname][1];
                }
                else if (vtype.tag === $TypeInfo.BSQTypeTag.TYPE_STD_ENTITY) {
                    aval = vtype.isconcretetype ? vval[iname] : vval.value[iname];
                    ptype = BSQONParseResultInfo.getHistory(vv, true)[iname][0];
                    ptree = BSQONParseResultInfo.getHistory(vv, true)[iname][1];
                }
                else if (vtype.tag === $TypeInfo.BSQTypeTag.TYPE_SOMETHING) {
                    this.raiseErrorIf(iname !== "value", `Expected 'value' property access but got ${iname}`);

                    aval = vtype.isconcretetype ? vval : vval.value;
                    ptype = BSQONParseResultInfo.getHistory(vv, true)[0];
                    ptree = BSQONParseResultInfo.getHistory(vv, true)[1];
                }
                else if (vtype.tag === $TypeInfo.BSQTypeTag.TYPE_MAP_ENTRY) {
                    this.raiseErrorIf(iname !== "key" && iname !== "value", `Expected 'key' or 'value' property access but got ${iname}`);

                    if (iname === "key") {
                        vtype.isconcretetype ? vval[0] : vval.value[0];
                        ptype = BSQONParseResultInfo.getHistory(vv, true).key[0];
                        ptree = BSQONParseResultInfo.getHistory(vv, true).key[1];
                    }
                    else if (iname === "value") {
                        vtype.isconcretetype ? vval[1] : vval.value[1];
                        ptype = BSQONParseResultInfo.getHistory(vv, true).value[0];
                        ptree = BSQONParseResultInfo.getHistory(vv, true).value[1];
                    }
                }
                else {
                    this.raiseError(`Invalid use of '.' operator -- ${vtype.tkey} is not a record, nominal, option/something, or map entry type`);
                }
            }
            else if (this.testToken(TokenKind.TOKEN_DOT_IDX)) {
                this.raiseErrorIf(vtype.tag !== $TypeInfo.BSQTypeTag.TYPE_TUPLE, `Invalid use of '[]' operator -- ${vtype.tkey} is not a tuple type`);

                const idx = Number.parseInt(this.expectTokenAndPop(TokenKind.TOKEN_DOT_IDX).value.slice(1));
                const tuprepr = vtype.isconcretetype ? vval : vval.value;

                this.raiseErrorIf(idx >= tuprepr.length, `Invalid use of '[]' operator -- index ${idx} is out of bounds for tuple type ${BSQONParseResultInfo.getValueType(vv, true).tkey}`);
                aval = tuprepr[idx];
                ptype = BSQONParseResultInfo.getHistory(vv, true)[idx][0];
                ptree = BSQONParseResultInfo.getHistory(vv, true)[idx][1];
            }
            else {
                if (vtype.tag === $TypeInfo.BSQTypeTag.TYPE_LIST) {
                    this.expectTokenAndPop(TokenKind.TOKEN_LBRACKET);
                    const eexp = this.parseExpression(this.m_assembly.typerefs.get("Nat") as $TypeInfo.BSQType, false);
                    this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

                    const lrepr = (vtype.isconcretetype ? vval : vval.value) as IList<any>;
                    aval = lrepr.get(eexp);
                    ptype = BSQONParseResultInfo.getHistory(vv, true).get(eexp)[0];
                    ptree = BSQONParseResultInfo.getHistory(vv, true).get(eexp)[1];
                }
                //OTHER TYPES HERE
                else {
                    this.raiseErrorIf(vtype.tag !== $TypeInfo.BSQTypeTag.TYPE_MAP, `Invalid use of '[]' operator -- ${vtype.tkey} is not a map type`);

                    this.expectTokenAndPop(TokenKind.TOKEN_LBRACKET);
                    const eexp = this.parseExpression(this.lookupMustDefType((BSQONParseResultInfo.getValueType(vv, true) as $TypeInfo.MapType).ktype), false);
                    this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

                    const lrepr = (vtype.isconcretetype ? vval : vval.value) as IMap<any, any>;
                    aval = lrepr.get(eexp);
                    ptype = BSQONParseResultInfo.getHistory(vv, true).get(eexp)[0];
                    ptree = BSQONParseResultInfo.getHistory(vv, true).get(eexp)[1];
                }
            }

            vv = BSQONParseResultInfo.create(aval, ptype, ptree, true);
        }

        this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(BSQONParseResultInfo.getValueType(vv, true), oftype), `Expression has type ${BSQONParseResultInfo.getValueType(vv, true).tkey} which is not a subtype of ${oftype.tkey}`);
        const rr = oftype.isconcretetype ? BSQONParseResultInfo.getParseValue(vv, true) : new $Runtime.UnionValue(BSQONParseResultInfo.getParseValue(vv, true), BSQONParseResultInfo.getValueType(vv, true));

        return BSQONParseResultInfo.create(rr, BSQONParseResultInfo.getParseValue(vv, true), BSQONParseResultInfo.getHistory(vv, true), whistory);
    }

    private parseExpression(oftype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        return this.parsePostfixOp(oftype, whistory);
    }

    private parseNone(whistory: boolean): BSQONParseResult {
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            this.expectTokenAndPop(TokenKind.TOKEN_NONE);
        }
        else {
            this.expectTokenAndPop(TokenKind.TOKEN_NULL);
        }
        return BSQONParseResultInfo.create(null, this.lookupMustDefType("None"), undefined, whistory);
    }

    private parseNothing(whistory: boolean): BSQONParseResult {
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            this.expectTokenAndPop(TokenKind.TOKEN_NOTHING);
        }
        else {
            this.expectTokenAndPop(TokenKind.TOKEN_NULL);
        }
        return BSQONParseResultInfo.create(undefined, this.lookupMustDefType("Nothing"), undefined, whistory);
    }

    private parseBool(whistory: boolean): BSQONParseResult {
        const tk = this.popToken();
        this.raiseErrorIf(tk === undefined || (tk.kind !== TokenKind.TOKEN_TRUE && tk.kind !== TokenKind.TOKEN_FALSE), `Expected boolean value but got -- ${tk?.value ?? "EOF"}`);

        return BSQONParseResultInfo.create(tk!.kind === TokenKind.TOKEN_TRUE, this.lookupMustDefType("Bool"), undefined, whistory);
    }
    
    private parseNat(whistory: boolean): BSQONParseResult {
        let tkval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_NAT).value.slice(0, -1);
        }
        else {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_INT).value;
        }
    
        const bv = Number.parseInt(tkval);
        this.raiseErrorIf(Number.isNaN(bv) || !Number.isFinite(bv), `Expected finite Nat number but got -- ${tkval}`);
        this.raiseErrorIf(bv < 0, `Nat value is negative -- ${tkval}`);
        this.raiseErrorIf(bv > $Constants.FIXED_NUMBER_MAX, `Nat value is larger than max value -- ${tkval}`);
    
        return BSQONParseResultInfo.create(bv, this.lookupMustDefType("Nat"), undefined, whistory);
    }

    private parseInt(whistory: boolean): BSQONParseResult {
        let tkval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_INT).value.slice(0, -1);
        }
        else {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_INT).value;
        }
    
        const bv = Number.parseInt(tkval);
        this.raiseErrorIf(Number.isNaN(bv) || !Number.isFinite(bv), `Expected finite Int number but got -- ${tkval}`);
        this.raiseErrorIf(bv < $Constants.FIXED_NUMBER_MIN, `Int value is smaller than min value -- ${tkval}`);
        this.raiseErrorIf(bv > $Constants.FIXED_NUMBER_MAX, `Int value is larger than max value -- ${tkval}`);
        
        return BSQONParseResultInfo.create(bv, this.lookupMustDefType("Int"), undefined, whistory);
    }

    private parseBigNat(whistory: boolean): BSQONParseResult {
        let tkval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_BIG_NAT).value.slice(0, -1);
        }
        else {
            const tk = this.popToken();
            this.raiseErrorIf(tk === undefined || (tk.kind !== TokenKind.TOKEN_INT && tk.kind !== TokenKind.TOKEN_STRING), `Expected BigNat but got ${tk?.value ?? "EOF"}`);
    
            if(tk!.kind === TokenKind.TOKEN_INT) {
                tkval = tk!.value;
            }
            else {
                tkval = tk!.value.slice(1, -1);
                this.raiseErrorIf(!_s_natCheckRe.test(tkval), `Expected BigInt: but got ${tkval}`);
            }
        }
    
        return BSQONParseResultInfo.create(BigInt(tkval), this.lookupMustDefType("BigNat"), undefined, whistory);
    }
    private parseBigInt(whistory: boolean): BSQONParseResult {
        let tkval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_BIG_INT).value.slice(0, -1);
        }
        else {
            const tk = this.popToken();
            this.raiseErrorIf(tk === undefined || (tk.kind !== TokenKind.TOKEN_INT && tk.kind !== TokenKind.TOKEN_STRING), `Expected BigInt but got ${tk?.value ?? "EOF"}`);
    
            if(tk!.kind === TokenKind.TOKEN_INT) {
                tkval = tk!.value;
            }
            else {
                tkval = tk!.value.slice(1, -1);
                this.raiseErrorIf(!_s_intCheckRe.test(tkval), `Expected BigInt: but got ${tkval}`);
            }
        }
    
        return BSQONParseResultInfo.create(BigInt(tkval), this.lookupMustDefType("BigInt"), undefined, whistory);
    }

    private parseRational(whistory: boolean): BSQONParseResult {
        let tkval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_RATIONAL).value.slice(0, -1);
        }
        else {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_rationalCheckRe.test(tkval), `Expected float but got ${tkval}`);
        }
    
        return BSQONParseResultInfo.create(new Fraction(tkval), this.lookupMustDefType("Rational"), undefined, whistory);
    }

    private parseFloat(whistory: boolean): BSQONParseResult {
        let tkval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_FLOAT).value.slice(0, -1);
        }
        else {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_FLOAT).value;
            this.raiseErrorIf(!_s_floatCheckRe.test(tkval), `Expected float but got ${tkval}`);
        }
    
        return BSQONParseResultInfo.create(Number.parseFloat(tkval), this.lookupMustDefType("Float"), undefined, whistory);
    }

    private parseDecimal(whistory: boolean): BSQONParseResult {
        let tkval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_DECIMAL).value.slice(0, -1);
        }
        else {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_FLOAT).value;
            this.raiseErrorIf(!_s_floatCheckRe.test(tkval), `Expected decimal but got ${tkval}`);
        }
    
        return BSQONParseResultInfo.create(new Decimal(tkval), this.lookupMustDefType("Decimal"), undefined, whistory);
    }

    private parseString(whistory: boolean): BSQONParseResult {
        const tstr = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
        const rstr = this.unescapeString(tstr);

        return BSQONParseResultInfo.create(rstr, this.lookupMustDefType("String"), undefined, whistory);
    }

    private parseASCIIString(whistory: boolean): BSQONParseResult {
        let tkval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_ASCII_STRING).value.slice(7, -2);
        }
        else {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_asciiStringCheckRe.test(tkval), `Expected ASCII string but got ${tkval}`);
        }
    
        const rstr = this.unescapeString(tkval);
        return BSQONParseResultInfo.create(rstr, this.lookupMustDefType("ASCIIString"), undefined, whistory);
    }

    private parseByteBuffer(whistory: boolean): BSQONParseResult {
        let tbval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tbval = this.expectTokenAndPop(TokenKind.TOKEN_BYTE_BUFFER).value.slice(3, -1);
        }
        else {
            tbval = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_bytebuffCheckRe.test(tbval), `Expected byte buffer but got ${tbval}`);
        }
    
        return BSQONParseResultInfo.create(tbval, this.lookupMustDefType("ByteBuffer"), undefined, whistory);
    }

    private parseDateTime(whistory: boolean): BSQONParseResult {
        let dd: $Runtime.BSQDateTime | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ISO_DATE_TIME).value;
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined, `Expected date+time but got ${tk}`);
        }
        else {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_fullTimeCheckRE.test(tk), `Expected date+time but got ${tk}`);
    
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined, `Expected date+time but got ${tk}`);
        }
    
        return BSQONParseResultInfo.create(dd, this.lookupMustDefType("DateTime"), undefined, whistory);
    }

    private parseUTCDateTime(whistory: boolean): BSQONParseResult {
        let dd: $Runtime.BSQDateTime | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ISO_UTC_DATE_TIME).value;
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected UTC date+time but got ${tk}`);
        }
        else {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_fullTimeUTCCheckRE.test(tk), `Expected UTC date+time but got ${tk}`);
    
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected UTC date+time but got ${tk}`);
        }
    
        return BSQONParseResultInfo.create(dd, this.lookupMustDefType("UTCDateTime"), undefined, whistory);
    }

    private parsePlainDate(whistory: boolean): BSQONParseResult {
        let dd: $Runtime.BSQDate | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ISO_DATE).value;
            dd = generateDate(tk);
            this.raiseErrorIf(dd === undefined, `Expected plain date but got ${tk}`);
        }
        else {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_dateOnlyCheckRE.test(tk), `Expected plain date but got ${tk}`);
    
            dd = generateDate(tk);
            this.raiseErrorIf(dd === undefined, `Expected plain date but got ${tk}`);
        }
    
        return BSQONParseResultInfo.create(dd, this.lookupMustDefType("PlainDate"), undefined, whistory);
    }

    private parsePlainTime(whistory: boolean): BSQONParseResult {
        let dd: $Runtime.BSQTime | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ISO_TIME).value;
            dd = generateTime(tk);
            this.raiseErrorIf(dd === undefined, `Expected plain time but got ${tk}`);
        }
        else {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_timeOnlyCheckRE.test(tk), `Expected plain time but got ${tk}`);
    
            dd = generateTime(tk);
            this.raiseErrorIf(dd === undefined, `Expected plain time but got ${tk}`);
        }
    
        return BSQONParseResultInfo.create(dd, this.lookupMustDefType("PlainTime"), undefined, whistory);
    }

    private parseTickTime(whistory: boolean): BSQONParseResult {
        let tt: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tt = this.expectTokenAndPop(TokenKind.TOKEN_TICK_TIME).value.slice(0, -1);
        }
        else {
            tt = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_tickTimeCheckRE.test(tt), `Expected tick time but got ${tt}`);
        }
    
        return BSQONParseResultInfo.create(BigInt(tt), this.lookupMustDefType("TickTime"), undefined, whistory);
    }

    private parseLogicalTime(whistory: boolean): BSQONParseResult {
        let tt: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tt = this.expectTokenAndPop(TokenKind.TOKEN_LOGICAL_TIME).value.slice(0, -1);
        }
        else {
            tt = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_logicalTimeCheckRE.test(tt), `Expected logical time but got ${tt}`);
        }
    
        return BSQONParseResultInfo.create(BigInt(tt), this.lookupMustDefType("LogicalTime"), undefined, whistory);
    }

    private parseISOTimeStamp(whistory: boolean): BSQONParseResult {
        let dd: $Runtime.BSQDateTime | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ISO_TIMESTAMP).value;
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected timestamp but got ${tk}`);
        }
        else {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_isoStampCheckRE.test(tk), `Expected timestamp but got ${tk}`);
    
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected timestamp but got ${tk}`);
        }
    
        return BSQONParseResultInfo.create(dd, this.lookupMustDefType("ISOTimeStamp"), undefined, whistory);
    }

    private parseUUIDv4(whistory: boolean): BSQONParseResult {
        let uuid: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_UUID).value;
            this.raiseErrorIf(!tk.startsWith("uuid4{"), `Expected UUIDv4 but got ${tk}`);
    
            uuid = tk.slice(6, -1);
        }
        else {
            uuid = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_uuidCheckRE.test(uuid), `Expected UUIDv4 but got ${uuid}`);
        }
    
        return BSQONParseResultInfo.create(uuid, this.lookupMustDefType("UUIDv4"), undefined, whistory);
    }

    private parseUUIDv7(whistory: boolean): BSQONParseResult {
        let uuid: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_UUID).value;
            this.raiseErrorIf(!tk.startsWith("uuid7{"), `Expected UUIDv7 but got ${tk}`);
    
            uuid = tk.slice(6, -1);
        }
        else {
            uuid = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_uuidCheckRE.test(uuid), `Expected UUIDv7 but got ${uuid}`);
        }
    
        return BSQONParseResultInfo.create(uuid, this.lookupMustDefType("UUIDv7"), undefined, whistory);
    }

    private parseSHAContentHash(whistory: boolean): BSQONParseResult {
        let sh: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            sh = this.expectTokenAndPop(TokenKind.TOKEN_SHA_HASH).value.slice(5, -1);
        }
        else {
            sh = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_shahashCheckRE.test(sh), `Expected SHA 512 hash but got ${sh}`);
        }
    
        return BSQONParseResultInfo.create(sh, this.lookupMustDefType("SHAContentHash"), undefined, whistory);
    }

    private parseRegex(whistory: boolean): BSQONParseResult {
        let re: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            re = this.expectTokenAndPop(TokenKind.TOKEN_REGEX).value;
        }
        else {
            re = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_regexCheckRe.test(re), `Expected a regex string but got ${re}`);
        }
    
        return BSQONParseResultInfo.create(re, this.lookupMustDefType("Regex"), undefined, whistory);
    }

    private parseLatLongCoordinate(whistory: boolean): BSQONParseResult {
        let llc: [number, number] | undefined = undefined;
        if (this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const ttype = this.expectTokenAndPop(TokenKind.TOKEN_TYPE).value;
            this.raiseErrorIf(ttype !== "LatLongCoordinate", `Expected LatLongCoordinate but got ${ttype}`);
    
            this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
            const lat = this.parseFloat(false);
            this.expectTokenAndPop(TokenKind.TOKEN_COMMA);
            const long = this.parseFloat(false);
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);
    
            llc = [lat, long];
        }
        else {
            this.expectTokenAndPop(TokenKind.TOKEN_LBRACKET);
            const lat = this.parseFloat(false);
            this.expectTokenAndPop(TokenKind.TOKEN_COMMA);
            const long = this.parseFloat(false);
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);
    
            llc = [lat, long];
        }

        this.raiseErrorIf(-90.0 <= llc[0] && llc[0] <= 90.0 && -180.0 < llc[1] && llc[1] <= 180.0, `LatLongCoordinate out of range: ${llc}`)
        return BSQONParseResultInfo.create(llc, this.lookupMustDefType("LatLongCoordinate"), undefined, whistory);
    }

    private parseStringOfWithType(whistory: boolean): [BSQONParseResult, $TypeInfo.BSQTypeKey] {
        const rawtk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
        const tk = this.unescapeString(rawtk);
        const st = this.parseNominalType() as $TypeInfo.ValidatorEntityType;

        const vre = this.m_assembly.revalidators.get(st.oftype);
        this.raiseErrorIf(vre === undefined || !$Runtime.acceptsString(vre.slice(1, -1), tk), `String literal does not satisfy the required format: ${st.oftype} (${vre})`);

        const stt = this.lookupMustDefType(`StringOf<${st.tkey}>`) as $TypeInfo.StringOfType;
        return [BSQONParseResultInfo.create(tk, stt, undefined, whistory), stt.tkey];
    }

    private parseStringOf(ttype: $TypeInfo.StringOfType, whistory: boolean): BSQONParseResult {
        let sval: string | undefined = undefined;
        if (this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);

            if(this.isNominalTypePrefix()) {
                const st = this.parseNominalType();
                this.raiseErrorIf(st.tkey !== ttype.oftype, `Expected ${ttype.oftype} but got StringOf<${st.tkey}>`);
            }

            sval = this.unescapeString(tk);
        }
        else {
            const rawtk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            sval = this.unescapeString(rawtk);
        }

        const vre = this.m_assembly.revalidators.get(ttype.oftype);
        this.raiseErrorIf(vre === undefined || !$Runtime.acceptsString(vre.slice(1, -1), sval), `String literal does not satisfy the required format: ${ttype.oftype} (${vre})`);

        return BSQONParseResultInfo.create(sval, ttype, undefined, whistory);
    }

    private parseASCIIStringOfWithType(whistory: boolean): [BSQONParseResult, $TypeInfo.BSQTypeKey] {
        const rawtk = this.expectTokenAndPop(TokenKind.TOKEN_ASCII_STRING).value.slice(7, -2);
        const tk = this.unescapeString(rawtk);
        const st = this.parseASCIIStringOfType() as $TypeInfo.ValidatorEntityType;

        const vre = this.m_assembly.revalidators.get(st.oftype);
        this.raiseErrorIf(vre === undefined || !$Runtime.acceptsString(vre.slice(1, -1), tk), `String literal does not satisfy the required format: ${st.oftype} (${vre})`);

        const stt = this.lookupMustDefType(`ASCIIStringOf<${st.tkey}>`) as $TypeInfo.ASCIIStringOfType;
        return [BSQONParseResultInfo.create(tk, stt, undefined, whistory), stt.tkey];
    }

    private parseASCIIStringOf(ttype: $TypeInfo.ASCIIStringOfType, whistory: boolean): BSQONParseResult {
        let sval: string | undefined = undefined;
        if (this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ASCII_STRING).value;

            if (this.isNominalTypePrefix()) {
                const st = this.parseASCIIStringOfType();
                this.raiseErrorIf(st.tkey !== ttype.oftype, `Expected ${ttype.tag} but got ASCIIStringOf<${st.tkey}>`);
            }

            const rawtk = tk.slice(7, -2);
            sval = this.unescapeString(rawtk);
        }
        else {
            const rawtk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            sval = this.unescapeString(rawtk);
        }

        const vre = this.m_assembly.revalidators.get(ttype.oftype);
        this.raiseErrorIf(vre === undefined || !$Runtime.acceptsString(vre.slice(1, -1), sval), `ASCIIString literal does not satisfy the required format: ${ttype.oftype} (${vre})`);

        return BSQONParseResultInfo.create(sval, ttype, undefined, whistory);
    }

    private parsePath(ttype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        this.raiseError("NOT IMPLEMENTED: PATH");
        /*
        let pth = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const ptk = this.expectTokenAndPop(TokenKind.TOKEN_PATH_ITEM).value;
        }
        else {
            const ptk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value;
        }
        */
    }

    private parsePathFragment(ttype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        this.raiseError("NOT IMPLEMENTED: PATH FRAGMENT");
    }

    private parsePathGlob(ttype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        this.raiseError("NOT IMPLEMENTED: PATH GLOB");
    }

    private parseSomething(ttype: $TypeInfo.SomethingType | $TypeInfo.OptionType | undefined, chktype: $TypeInfo.BSQType, whistory: boolean): [BSQONParseResult, $TypeInfo.BSQType] {
        let vv = undefined;
        let stype: $TypeInfo.BSQType = $TypeInfo.UnresolvedType.singleton;

        if (this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            if (this.testToken(TokenKind.TOKEN_SOMETHING)) {
                this.popToken();
                stype = this.parseSomethingTypeComplete(ttype);

                this.expectTokenAndPop(TokenKind.TOKEN_LPAREN);
                vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.SomethingType).oftype), whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_RPAREN);
            }
            else {
                const stype = this.parseSomethingType(ttype);
                this.raiseErrorIf(ttype === undefined || !this.m_assembly.checkConcreteSubtype(stype, ttype), `Expected ${ttype?.tkey ?? "Something"} but got ${stype.tkey}`);

                this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
                vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.SomethingType).oftype), whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);
            }
        }
        else {
            stype = ttype as $TypeInfo.SomethingType;
            vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.SomethingType).oftype), whistory);
        }

        this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(stype, chktype), `Expected ${chktype.tkey} but got ${stype.tkey}`);
        return [BSQONParseResultInfo.create(BSQONParseResultInfo.getParseValue(vv, whistory), stype, [BSQONParseResultInfo.getValueType(vv, whistory), BSQONParseResultInfo.getHistory(vv, whistory)], whistory), stype];
    }

    private parseOk(ttype: $TypeInfo.OkType | $TypeInfo.ResultType | undefined, chktype: $TypeInfo.BSQType, whistory: boolean): [BSQONParseResult, $TypeInfo.BSQType] {
        let vv = undefined;
        let stype: $TypeInfo.BSQType = $TypeInfo.UnresolvedType.singleton;

        if (this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            if (this.testToken(TokenKind.TOKEN_OK)) {
                this.popToken();
                stype = this.parseOkTypeComplete(undefined, ttype);

                this.expectTokenAndPop(TokenKind.TOKEN_LPAREN);
                vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.OkType).ttype), whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_RPAREN);
            }
            else {
                const stype = this.parseOkType(ttype);
                this.raiseErrorIf(ttype === undefined || !this.m_assembly.checkConcreteSubtype(stype, ttype), `Expected ${ttype?.tkey ?? "Ok"} but got ${stype.tkey}`);

                this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
                vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.OkType).ttype), whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);
            }
        }
        else {
            stype = ttype as $TypeInfo.OkType;
            vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.OkType).ttype), whistory);
        }

        this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(stype, chktype), `Expected ${chktype.tkey} but got ${stype.tkey}`);
        return [BSQONParseResultInfo.create(BSQONParseResultInfo.getParseValue(vv, whistory), stype, [BSQONParseResultInfo.getValueType(vv, whistory), BSQONParseResultInfo.getHistory(vv, whistory)], whistory), stype];
    }

    private parseErr(ttype: $TypeInfo.ErrorType | $TypeInfo.ResultType | undefined, chktype: $TypeInfo.BSQType, whistory: boolean): [BSQONParseResult, $TypeInfo.BSQType] {
        let vv = undefined;
        let stype: $TypeInfo.BSQType = $TypeInfo.UnresolvedType.singleton;

        if (this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            if (this.testToken(TokenKind.TOKEN_ERR)) {
                this.popToken();
                stype = this.parseErrTypeComplete(undefined, ttype);

                this.expectTokenAndPop(TokenKind.TOKEN_LPAREN);
                vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.OkType).etype), whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_RPAREN);
            }
            else {
                const stype = this.parseErrType(ttype);
                this.raiseErrorIf(ttype === undefined || !this.m_assembly.checkConcreteSubtype(stype, ttype), `Expected ${ttype?.tkey ?? "Err"} but got ${stype.tkey}`);

                this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
                vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.OkType).etype), whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);
            }
        }
        else {
            stype = ttype as $TypeInfo.ErrorType;
            vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.ErrorType).etype), whistory);
        }

        this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(stype, chktype), `Expected ${chktype.tkey} but got ${stype.tkey}`);
        return [BSQONParseResultInfo.create(BSQONParseResultInfo.getParseValue(vv, whistory), stype, [BSQONParseResultInfo.getValueType(vv, whistory), BSQONParseResultInfo.getHistory(vv, whistory)], whistory), stype];
    }

    private parseMapEntry(ttype: $TypeInfo.MapEntryType, whistory: boolean, inmapdecl: boolean): BSQONParseResult {
        const keytype = this.lookupMustDefType(ttype.ktype);
        const valtype = this.lookupMustDefType(ttype.vtype);

        if(this.m_parsemode === $Runtime.NotationMode.NOTATION_MODE_JSON || (inmapdecl && this.testToken(TokenKind.TOKEN_LBRACKET))) {
            this.expectTokenAndPop(TokenKind.TOKEN_LBRACKET);
            const k = this.parseValue(keytype, whistory);
            this.expectTokenAndPop(TokenKind.TOKEN_COMMA);
            const v = this.parseValue(valtype, whistory);
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

            return BSQONParseResultInfo.create([BSQONParseResultInfo.getParseValue(k, whistory), BSQONParseResultInfo.getParseValue(v, whistory)], ttype, [[BSQONParseResultInfo.getValueType(k, whistory), BSQONParseResultInfo.getHistory(k, whistory)], [BSQONParseResultInfo.getValueType(v, whistory), BSQONParseResultInfo.getHistory(v, whistory)]], whistory);
        }
        else {
            if(inmapdecl && !this.testToken(TokenKind.TOKEN_TYPE)) {
                const k = this.parseValue(keytype, whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_ENTRY);
                const v = this.parseValue(valtype, whistory);

                return BSQONParseResultInfo.create([BSQONParseResultInfo.getParseValue(k, whistory), BSQONParseResultInfo.getParseValue(v, whistory)], ttype, [[BSQONParseResultInfo.getValueType(k, whistory), BSQONParseResultInfo.getHistory(k, whistory)], [BSQONParseResultInfo.getValueType(v, whistory), BSQONParseResultInfo.getHistory(v, whistory)]], whistory);
            }
            else {
                const etype = this.parseType();
                this.raiseErrorIf(etype.tkey !== ttype.tkey, `Expected ${ttype.tkey} but got value of type ${etype.tkey}`);

                this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
                const k = this.parseValue(keytype, whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_COMMA);
                const v = this.parseValue(valtype, whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

                return BSQONParseResultInfo.create([BSQONParseResultInfo.getParseValue(k, whistory), BSQONParseResultInfo.getParseValue(v, whistory)], ttype, [[BSQONParseResultInfo.getValueType(k, whistory), BSQONParseResultInfo.getHistory(k, whistory)], [BSQONParseResultInfo.getValueType(v, whistory), BSQONParseResultInfo.getHistory(v, whistory)]], whistory);
            }
        }
    }

    private parseTuple(ttype: $TypeInfo.TupleType, whistory: boolean): BSQONParseResult {
        this.expectTokenAndPop(TokenKind.TOKEN_LBRACKET);

        if (this.testToken(TokenKind.TOKEN_RBRACKET)) {
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

            this.raiseErrorIf(ttype.entries.length !== 0, `Expected ${ttype.entries.length} values but got []`);
            return BSQONParseResultInfo.create([], ttype, [], whistory);
        }
        else {
            let tvals: any[] = [];
            let ptree: [$TypeInfo.BSQType, any][] = [];

            let first = true;
            while (first || this.testToken(TokenKind.TOKEN_COMMA)) {
                if(first) {
                    first = false;
                }
                else {
                    this.popToken();
                }
                
                const entry = this.parseValue(this.lookupMustDefType(ttype.entries[tvals.length]), whistory);

                tvals.push(BSQONParseResultInfo.getParseValue(entry, whistory));
                ptree.push([BSQONParseResultInfo.getValueType(entry, whistory), BSQONParseResultInfo.getHistory(entry, whistory)]);
            }
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

            this.raiseErrorIf(ttype.entries.length !== tvals.length, `Expected ${ttype.entries.length} values but got ${tvals.length}`);
            return BSQONParseResultInfo.create(tvals, ttype, ptree, whistory);
        }
    }

    private parseRecord(ttype: $TypeInfo.RecordType, whistory: boolean): BSQONParseResult {
        this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);

        if (this.testToken(TokenKind.TOKEN_RBRACE)) {
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

            this.raiseErrorIf(ttype.entries.length !== 0, `Expected ${Object.keys(ttype.entries).length} values but got {}`);
            return BSQONParseResultInfo.create({}, ttype, {}, whistory);
        }
        else {
            let tvals: {[k: string]: any} = {};
            let ptree: {[k: string]: [$TypeInfo.BSQType, any]} = {};
            let first = true;
            while (first || this.testToken(TokenKind.TOKEN_COMMA)) {
                if(first) {
                    first = false;
                }
                else {
                    this.popToken();
                }
                
                const pname = this.expectTokenAndPop(TokenKind.TOKEN_PROPERTY).value;
                this.expectTokenAndPop(this.m_parsemode === $Runtime.NotationMode.NOTATION_MODE_JSON ? TokenKind.TOKEN_COLON : TokenKind.TOKEN_EQUALS);

                const ptype = ttype.entries.find((ee) => ee.pname === pname);
                this.raiseErrorIf(ptype === undefined, `Unexpected property ${pname} in record`);

                const entry = this.parseValue(this.lookupMustDefType(ptype!.ptype), whistory);

                tvals[pname] = BSQONParseResultInfo.getParseValue(entry, whistory);
                ptree[pname] = [BSQONParseResultInfo.getValueType(entry, whistory), BSQONParseResultInfo.getHistory(entry, whistory)];
            }
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

            this.raiseErrorIf(ttype.entries.length !== Object.keys(tvals).length, `Expected ${Object.keys(ttype.entries).length} values but got ${Object.keys(tvals).length}`);
            this.raiseErrorIf(ttype.entries.some((entry) => !(entry.pname in tvals)), `Expected property ${Object.keys(ttype.entries).filter((pname) => !(pname in tvals)).join(", ")} but not provided`);

            return BSQONParseResultInfo.create(Object.freeze(tvals), ttype, ptree, whistory);
        }
    }

    private parseEnum(ttype: $TypeInfo.EnumType, whistory: boolean): BSQONParseResult {
        const etype = this.parseType();
        this.expectTokenAndPop(TokenKind.TOKEN_COLON_COLON);
        const ename = this.expectTokenAndPop(TokenKind.TOKEN_PROPERTY).value;

        this.raiseErrorIf(etype.tkey !== ttype.tkey, `Expected enum of type ${ttype.tkey} but got ${etype.tkey}::${ename}`);
        this.raiseErrorIf(!ttype.variants.includes(ename), `Enum ${ttype.tkey} does not contain value ${ename}`);

        return BSQONParseResultInfo.create(`${etype.tkey}::${ename}`, ttype, undefined, whistory);
    }
    
    private parseTypedecl(ttype: $TypeInfo.TypedeclType, whistory: boolean): BSQONParseResult {
        const vv = this.parseValue(this.lookupMustDefType(ttype.basetype), whistory);

        if (this.testAndPop_TypedeclUnder()) {
            const ntype = this.parseType();
            this.raiseErrorIf(ttype.tkey !== ntype.tkey, `Expected typedecl of type ${ttype.tkey} but got ${ntype.tkey}`);
        }

        if(ttype.hasvalidations) {
            this.m_typedeclChecks.push({ttype: ttype.tkey, tvalue: vv});
        }

        if(ttype.basetype.tkey === "String" || ttype.basetype.tkey === "ASCIIString") {
            if(ttype.optStringOfValidator !== undefined) {
                const vre = this.m_assembly.revalidators.get(ttype.optStringOfValidator);
                this.raiseErrorIf(vre === undefined || !$Runtime.acceptsString(vre.slice(1, -1), vv as string), `Typedecl of string literal does not satisfy the required format: ${ttype.optStringOfValidator} (${vre})`);
            }
        }
        if(ttype.basetype.tkey === "Path" || ttype.basetype.tkey === "PathFragment" || ttype.basetype.tkey === "PathGlob") {
            this.raiseError("Path types are not IMPLEMENTED in typedecls");
        }

        return BSQONParseResultInfo.create(BSQONParseResultInfo.getParseValue(vv, whistory), ttype, [BSQONParseResultInfo.getValueType(vv, whistory), BSQONParseResultInfo.getHistory(vv, whistory)], whistory);
    }

    private parseStdEntity(ttype: $TypeInfo.StdEntityType, whistory: boolean): BSQONParseResult {
        if(!this.testToken(TokenKind.TOKEN_LBRACE)) {
            const etype = this.parseType();
            this.raiseErrorIf(etype.tkey !== ttype.tkey, `Expected entity of type ${ttype.tkey} but got ${etype.tkey}`);
        }
        this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);

        let tvals: {[k: string]: any} = {};
        let ptree: {[k: string]: [$TypeInfo.BSQType, any]} = {};
        if (this.testToken(TokenKind.TOKEN_RBRACE)) {
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

            this.raiseErrorIf(ttype.fields.length !== 0, `Expected ${ttype.fields.length} values but got {}`);
            return BSQONParseResultInfo.create({}, ttype, {}, whistory);
        }
        else {
            if(this.m_parsemode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
                let first = true;
                while (first || this.testToken(TokenKind.TOKEN_COMMA)) {
                    if (first) {
                        first = false;
                    }
                    else {
                        this.popToken();
                    }

                    const ff = this.expectTokenAndPop(TokenKind.TOKEN_PROPERTY).value;
                    const ffe = ttype.fields.find((f) => f.fname === ff);
                    this.raiseErrorIf(ffe === undefined, `Field ${ff} does not exist on type ${ttype.tkey}`);
                    
                    this.expectTokenAndPop(TokenKind.TOKEN_COLON);
                    const vv = this.parseValue(this.lookupMustDefType(ffe!.ftype), whistory);

                    tvals[ffe!.fname] = BSQONParseResultInfo.getParseValue(vv, whistory);
                    ptree[ffe!.fname] = [BSQONParseResultInfo.getValueType(vv, whistory), BSQONParseResultInfo.getHistory(vv, whistory)];
                }
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

                if(ttype.hasvalidations) {
                    this.m_stdentityChecks.push({ etype: ttype.tkey, evalue: tvals });
                }

                this.raiseErrorIf(ttype.fields.length !== Object.keys(tvals).length, `Expected ${ttype.fields.length} values but got ${Object.keys(tvals).length}`);
                return BSQONParseResultInfo.create(Object.freeze(tvals), ttype, ptree, whistory);
            }
            else {
                let ii = 0;
                while (ii === 0 || this.testToken(TokenKind.TOKEN_COMMA)) {
                    if (ii !== 0) {
                        this.popToken();
                    }

                    if (ii >= ttype.fields.length) {
                        this.raiseError(`Expected ${ttype.fields.length} values but got ${ii}`);
                    }
                    const ff = ttype.fields[ii++];
                    const vv = this.parseValue(this.lookupMustDefType(ff.ftype), whistory);

                    tvals[ff.fname] = BSQONParseResultInfo.getParseValue(vv, whistory);
                    ptree[ff.fname] = [BSQONParseResultInfo.getValueType(vv, whistory), BSQONParseResultInfo.getHistory(vv, whistory)];
                }
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

                if(ttype.hasvalidations) {
                    this.m_stdentityChecks.push({ etype: ttype.tkey, evalue: tvals });
                }

                this.raiseErrorIf(ttype.fields.length !== Object.keys(tvals).length, `Expected ${ttype.fields.length} values but got ${Object.keys(tvals).length}`);
                return BSQONParseResultInfo.create(Object.freeze(tvals), ttype, ptree, whistory);
            }
        }
    }

    private parseList(ttype: $TypeInfo.ListType | undefined, chktype: $TypeInfo.BSQType, whistory: boolean): [BSQONParseResult, $TypeInfo.BSQType] {
        if(this.testToken(TokenKind.TOKEN_LBRACKET)) {
            this.raiseErrorIf(ttype === undefined, `Cannot use list [...] shorthand notation in ambigious context`);

            this.popToken();
            if(this.testToken(TokenKind.TOKEN_RBRACKET)) {
                this.popToken();

                return [BSQONParseResultInfo.create(IList<any>(), ttype as $TypeInfo.ListType, [], whistory), ttype as $TypeInfo.ListType];
            }
            else {
                let first = true;
                let vv: any[] = [];
                let ptree: [$TypeInfo.BSQType, any][] = [];
                while(first || this.testToken(TokenKind.TOKEN_COMMA)) {
                    if(first) {
                        first = false;
                    }
                    else {
                        this.popToken();
                    }

                    if(this.testToken(TokenKind.TOKEN_LDOTS)) {
                        const entry = this.parseValue(ttype as $TypeInfo.ListType, whistory);
                        vv.push(...(BSQONParseResultInfo.getParseValue(entry, whistory) as IList<any>));

                        if(whistory) {
                            ptree.push(...(BSQONParseResultInfo.getHistory(entry, whistory) as [$TypeInfo.BSQType, any][]));
                        }
                    }
                    else {
                        const entry = this.parseValue(this.lookupMustDefType((ttype as $TypeInfo.ListType).oftype), whistory);
                        vv.push(BSQONParseResultInfo.getParseValue(entry, whistory));
                        ptree.push([BSQONParseResultInfo.getValueType(entry, whistory), BSQONParseResultInfo.getHistory(entry, whistory)]);
                    }
                }
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

                return [BSQONParseResultInfo.create(IList<any>(vv), ttype as $TypeInfo.ListType, ptree, whistory), ttype as $TypeInfo.ListType];
            }
        }
        else {
            const ltype = this.parseListType(ttype);
            this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(ltype, chktype), `Expected a type ${chktype.tkey} but got ${ltype.tkey}`);

            this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
            if(this.testToken(TokenKind.TOKEN_RBRACE)) {
                this.popToken();

                return [BSQONParseResultInfo.create(IList<any>(), ltype as $TypeInfo.ListType, [], whistory), ltype];
            }
            else {
                let first = true;
                let vv: any[] = [];
                let ptree: [$TypeInfo.BSQType, any][] = [];
                while(first || this.testToken(TokenKind.TOKEN_COMMA)) {
                    if(first) {
                        first = false;
                    }
                    else {
                        this.popToken();
                    }

                    if(this.testToken(TokenKind.TOKEN_LDOTS)) {
                        const entry = this.parseValue(ltype, whistory);
                        vv.push(...(BSQONParseResultInfo.getParseValue(entry, whistory) as IList<any>));

                        if(whistory) {
                            ptree.push(...(BSQONParseResultInfo.getHistory(entry, whistory) as [$TypeInfo.BSQType, any][]));
                        }
                    }
                    else {
                        const entry = this.parseValue(this.lookupMustDefType((ltype as $TypeInfo.ListType).oftype), whistory);
                        vv.push(BSQONParseResultInfo.getParseValue(entry, whistory));
                        ptree.push([BSQONParseResultInfo.getValueType(entry, whistory), BSQONParseResultInfo.getHistory(entry, whistory)]);
                    }
                }
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

                return [BSQONParseResultInfo.create(IList<any>(vv), ltype, ptree, whistory), ltype];
            }
        }
    }

    private parseStack(ttype: $TypeInfo.StackType | undefined, chktype: $TypeInfo.BSQType, whistory: boolean): [BSQONParseResult, $TypeInfo.BSQType] {
        this.raiseError("Not implemented -- parseStack");
        return (undefined as any) as [BSQONParseResult, $TypeInfo.BSQType];
    }

    private parseQueue(ttype: $TypeInfo.QueueType | undefined, chktype: $TypeInfo.BSQType, whistory: boolean): [BSQONParseResult, $TypeInfo.BSQType] {
        this.raiseError("Not implemented -- parseQueue");
        return (undefined as any) as [BSQONParseResult, $TypeInfo.BSQType];
    }

    private parseSet(ttype: $TypeInfo.SetType | undefined, chktype: $TypeInfo.BSQType, whistory: boolean): [BSQONParseResult, $TypeInfo.BSQType] {
        this.raiseError("Not implemented -- parseSet");
        return (undefined as any) as [BSQONParseResult, $TypeInfo.BSQType];
    }

    private static genericKeyEq(k1: any, k2: any): boolean {
        if (k1 === k2) {
            return true;
        }
        else {
            const type1 = typeof k1;
            if(type1 !== "object") {
                return false;
            }
            else {
                if(k1 instanceof $Runtime.UnionValue) {
                    return k1.equals(k2);
                }
                else {
                    return k1.equalsBase(k2);
                }
            }
        }
    }

    private parseMap(ttype: $TypeInfo.MapType | undefined, chktype: $TypeInfo.BSQType, whistory: boolean): [BSQONParseResult, $TypeInfo.BSQType] {
        if(this.testToken(TokenKind.TOKEN_LBRACKET)) {
            this.raiseErrorIf(ttype === undefined, `Cannot use map {...} shorthand notation in ambigious context`);

            this.popToken();
            if(this.testToken(TokenKind.TOKEN_RBRACKET)) {
                this.popToken();

                return [BSQONParseResultInfo.create(IMap<any, any>(), ttype as $TypeInfo.MapType, [], whistory), ttype as $TypeInfo.MapType];
            }
            else {
                const metype = this.lookupMustDefType(`MapEntry<${(ttype as $TypeInfo.MapType).ktype}, ${(ttype as $TypeInfo.MapType).vtype}>`) as $TypeInfo.MapEntryType;

                let first = true;
                let vv: [any, any][] = [];
                let ptree: [$TypeInfo.BSQType, any][] = [];
                while(first || this.testToken(TokenKind.TOKEN_COMMA)) {
                    if(first) {
                        first = false;
                    }
                    else {
                        this.popToken();
                    }

                    if(this.testToken(TokenKind.TOKEN_LDOTS)) {
                        this.raiseError("... shorthand notation NOT IMPLEMENTED for maps yet");
                    }
                    else {
                        const entry = this.parseMapEntry(metype, whistory, true);

                        const kk = BSQONParseResultInfo.getParseValue(entry, whistory)[0];
                        this.raiseErrorIf(vv.some((v) => BSQONParser.genericKeyEq(kk, v[0])), `Duplicate key`);

                        vv.push(BSQONParseResultInfo.getParseValue(entry, whistory));
                        ptree.push([BSQONParseResultInfo.getValueType(entry, whistory), BSQONParseResultInfo.getHistory(entry, whistory)]);
                    }
                }
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

                return [BSQONParseResultInfo.create(IMap<any, any>(vv), ttype as $TypeInfo.MapType, ptree, whistory), ttype as $TypeInfo.MapType];
            }
        }
        else {
            const ltype = this.parseMapType(ttype);
            this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(ltype, chktype), `Expected a type ${chktype.tkey} but got ${ltype.tkey}`);

            this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
            if(this.testToken(TokenKind.TOKEN_RBRACE)) {
                this.popToken();

                return [BSQONParseResultInfo.create(IMap<any, any>(), ltype as $TypeInfo.MapType, [], whistory), ltype];
            }
            else {
                const metype = this.lookupMustDefType(`MapEntry<${(ltype as $TypeInfo.MapType).ktype}, ${(ltype as $TypeInfo.MapType).vtype}>`) as $TypeInfo.MapEntryType;

                let first = true;
                let vv: [any, any][] = [];
                let ptree: [$TypeInfo.BSQType, any][] = [];
                while(first || this.testToken(TokenKind.TOKEN_COMMA)) {
                    if(first) {
                        first = false;
                    }
                    else {
                        this.popToken();
                    }

                    if(this.testToken(TokenKind.TOKEN_LDOTS)) {
                        this.raiseError("... shorthand notation NOT IMPLEMENTED for maps yet");
                    }
                    else {
                        const entry = this.parseMapEntry(metype, whistory, true);

                        const kk = BSQONParseResultInfo.getParseValue(entry, whistory)[0];
                        this.raiseErrorIf(vv.some((v) => BSQONParser.genericKeyEq(kk, v[0])), `Duplicate key`);

                        vv.push(BSQONParseResultInfo.getParseValue(entry, whistory));
                        ptree.push([BSQONParseResultInfo.getValueType(entry, whistory), BSQONParseResultInfo.getHistory(entry, whistory)]);
                    }
                }
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

                return [BSQONParseResultInfo.create(IMap<any, any>(vv), ltype as $TypeInfo.MapType, ptree, whistory), ltype];
            }
        }
    }

    private parseValuePrimitive(ttype: $TypeInfo.PrimitiveType, whistory: boolean): BSQONParseResult {
        if(ttype.tkey === "None") {
            return this.parseNone(whistory);
        }
        else if(ttype.tkey === "Nothing") {
            return this.parseNothing(whistory);
        }
        else if(ttype.tkey === "Bool") {
            return this.parseBool(whistory);
        }
        else if(ttype.tkey === "Int") {
            return this.parseInt(whistory);
        }
        else if(ttype.tkey === "Nat") {
            return this.parseNat(whistory);
        }
        else if(ttype.tkey === "BigInt") {
            return this.parseBigInt(whistory);
        }
        else if(ttype.tkey === "BigNat") {
            return this.parseBigNat(whistory);
        }
        else if(ttype.tkey === "Rational") {
            return this.parseRational(whistory);
        }
        else if(ttype.tkey === "Float") {
            return this.parseFloat(whistory);
        }
        else if(ttype.tkey === "Decimal") {
            return this.parseDecimal(whistory);
        }
        else if(ttype.tkey === "String") {
            return this.parseString(whistory);
        }
        else if(ttype.tkey === "ASCIIString") {
            return this.parseASCIIString(whistory);
        }
        else if(ttype.tkey === "ByteBuffer") {
            return this.parseByteBuffer(whistory);
        }
        else if(ttype.tkey === "DateTime") {
            return this.parseDateTime(whistory);
        }
        else if(ttype.tkey === "UTCDateTime") {
            return this.parseUTCDateTime(whistory);
        }
        else if(ttype.tkey === "PlainDate") {
            return this.parsePlainDate(whistory);
        }
        else if(ttype.tkey === "PlainTime") {
            return this.parsePlainTime(whistory);
        }
        else if(ttype.tkey === "TickTime") {
            return this.parseTickTime(whistory);
        }
        else if(ttype.tkey === "LogicalTime") {
            return this.parseLogicalTime(whistory);
        }
        else if(ttype.tkey === "ISOTimeStamp") {
            return this.parseISOTimeStamp(whistory);
        }
        else if(ttype.tkey === "UUIDv4") {
            return this.parseUUIDv4(whistory);
        }
        else if(ttype.tkey === "UUIDv7") {
            return this.parseUUIDv7(whistory);
        }
        else if(ttype.tkey === "SHAContentHash") {
            return this.parseSHAContentHash(whistory);
        } 
        else if(ttype.tkey === "LatLongCoordinate") {
            return this.parseLatLongCoordinate(whistory);
        }
        else if(ttype.tkey === "Regex") {
            return this.parseRegex(whistory);
        }
        else {
            this.raiseError(`Unknown primitive type ${ttype.tkey}`);
        }
    }

    private parseValueDirect(ttype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        if(ttype instanceof $TypeInfo.TupleType) {
            return this.parseTuple(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.RecordType) {
            return this.parseRecord(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.StdEntityType) {
            return this.parseStdEntity(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.EnumType) {
            return this.parseEnum(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.TypedeclType) {
            return this.parseTypedecl(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.StringOfType) {
            return this.parseStringOf(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.ASCIIStringOfType) {
            return this.parseASCIIStringOf(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.SomethingType) {
            return this.parseSomething(ttype, ttype, whistory)[0];
        }
        else if(ttype instanceof $TypeInfo.OkType) {
            return this.parseOk(ttype, ttype, whistory)[0];
        }
        else if(ttype instanceof $TypeInfo.ErrorType) {
            return this.parseErr(ttype, ttype, whistory)[0];
        }
        else if(ttype instanceof $TypeInfo.PathType) {
            return this.parsePath(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.PathFragmentType) {
            return this.parsePathFragment(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.PathGlobType) {
            return this.parsePathGlob(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.ListType) {
            return this.parseList(ttype, ttype, whistory)[0];
        }
        else if(ttype instanceof $TypeInfo.StackType) {
            return this.parseStack(ttype, ttype, whistory)[0];
        }
        else if(ttype instanceof $TypeInfo.QueueType) {
            return this.parseQueue(ttype, ttype, whistory)[0];
        }
        else if(ttype instanceof $TypeInfo.SetType) {
            return this.parseSet(ttype, ttype, whistory)[0];
        }
        else if(ttype instanceof $TypeInfo.MapEntryType) {
            return this.parseMapEntry(ttype, whistory, false);
        }
        else if(ttype instanceof $TypeInfo.MapType) {
            return this.parseMap(ttype, ttype, whistory)[0];
        }
        else {
            this.raiseError(`Unknown type ${ttype.tkey}`);
        }
    }

    private parseValueConcept(ttype: $TypeInfo.ConceptType | $TypeInfo.ConceptSetType, whistory: boolean): BSQONParseResult {
        if (this.m_parsemode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
            this.expectTokenAndPop(TokenKind.TOKEN_LBRACKET);
            const tt = this.parseType();
            this.expectTokenAndPop(TokenKind.TOKEN_COMMA);
            const vv = this.parseValue(tt, whistory);
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

            this.raiseErrorIf(!tt.isconcretetype, `Expected concrete type but got ${tt.tkey}`);
            this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(tt, ttype), `Expected type ${ttype.tkey} but got ${tt.tkey}`);
            return BSQONParseResultInfo.create(new $Runtime.UnionValue(tt.tkey, BSQONParseResultInfo.getParseValue(vv, whistory)), tt, BSQONParseResultInfo.getHistory(vv, whistory), whistory);
        }
        else {
            let rv: BSQONParseResult = undefined;
            let rt: $TypeInfo.BSQType = $TypeInfo.UnresolvedType.singleton;
            
            if (ttype instanceof $TypeInfo.OptionType) {
                if (this.testToken(TokenKind.TOKEN_NOTHING)) {
                    rv = this.parseNothing(whistory);
                    rt = this.lookupMustDefType("Nothing");
                }
                else {
                    [rv, rt] = this.parseSomething(ttype, ttype, whistory);
                }
            }
            else if (ttype instanceof $TypeInfo.ResultType) {
                if (this.testToken(TokenKind.TOKEN_OK) || this.testTokensWValue({kind: TokenKind.TOKEN_TYPE, value: "Result"}, {kind: TokenKind.TOKEN_COLON_COLON, value: "::"}, {kind: TokenKind.TOKEN_TYPE, value: "Ok"})) {
                    [rv, rt] = this.parseOk(ttype, ttype, whistory);
                }
                else if (this.testToken(TokenKind.TOKEN_ERR) || this.testTokensWValue({kind: TokenKind.TOKEN_TYPE, value: "Result"}, {kind: TokenKind.TOKEN_COLON_COLON, value: "::"}, {kind: TokenKind.TOKEN_TYPE, value: "Err"})) {
                    [rv, rt] = this.parseErr(ttype, ttype, whistory);
                }
                else {
                    const rtype = this.parseNominalType();
                    this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(rtype, ttype), `Expected result of type ${ttype.tkey} but got ${rtype.tkey}`);

                    if (rtype instanceof $TypeInfo.OkType) {
                        this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
                        const vv = this.parseValue(this.lookupMustDefType(rtype.ttype), whistory);
                        this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

                        rv = BSQONParseResultInfo.create(BSQONParseResultInfo.getParseValue(vv, whistory), rtype, [BSQONParseResultInfo.getValueType(vv, whistory), BSQONParseResultInfo.getHistory(vv, whistory)], whistory);
                        rt = rtype;
                    }
                    else {
                        this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
                        const vv = this.parseValue(this.lookupMustDefType((rtype as $TypeInfo.ErrorType).etype), whistory);
                        this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

                        rv = BSQONParseResultInfo.create(BSQONParseResultInfo.getParseValue(vv, whistory), rtype, [BSQONParseResultInfo.getValueType(vv, whistory), BSQONParseResultInfo.getHistory(vv, whistory)], whistory);
                        rt = rtype;
                    }
                }
            }
            else if (ttype instanceof $TypeInfo.StdConceptType) {
                const tt = this.parseNominalType();
                this.raiseErrorIf(!(tt instanceof $TypeInfo.StdEntityType), `Expected std entity type but got ${tt.tkey}`);
                this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(tt, ttype), `Expected std entity of type ${ttype.tkey} but got ${tt.tkey}`);

                rv = this.parseStdEntity(tt as $TypeInfo.StdEntityType, whistory);
                rt = tt;
            }
            else if (ttype instanceof $TypeInfo.ConceptSetType) {
                const tt = this.parseNominalType();
                this.raiseErrorIf(!(tt instanceof $TypeInfo.StdEntityType), `Expected std entity type but got ${tt.tkey}`);
                this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(tt, ttype), `Expected std entity of type ${ttype.tkey} but got ${tt.tkey}`);

                rv = this.parseStdEntity(tt as $TypeInfo.StdEntityType, whistory);
                rt = tt;
            }
            else {
                this.raiseError(`Unknown concept type ${ttype.tkey}`);
            }

            return BSQONParseResultInfo.create(new $Runtime.UnionValue(rt.tkey, BSQONParseResultInfo.getParseValue(rv, whistory)), rt, BSQONParseResultInfo.getHistory(rv, whistory), whistory);
        }
    }

    private resolveRelaxedTypeMatch(oftags: $TypeInfo.BSQTypeTag[], opts: $TypeInfo.UnionType): $TypeInfo.BSQType | undefined {
        let tt: $TypeInfo.BSQType | undefined = undefined;
        if (opts.types.length === 1) {
            tt = this.lookupMustDefType(opts.types[0]);
        }
        else if(opts.types.length === 2 && opts.types.includes("None")) {
            tt = this.lookupMustDefType(opts.types[0] === "None" ? opts.types[1] : opts.types[0]);
        }   
        else {
            ; //do nothing
        }

        return (tt !== undefined && oftags.includes(tt.tag)) ? tt : undefined;
    }

    private isNoneableParse(ttype: $TypeInfo.UnionType): boolean {
        return ttype.types.length === 2 && ttype.types.includes("None");
    }

    private getNoneableRealType(ttype: $TypeInfo.UnionType): $TypeInfo.BSQType {
        return this.lookupMustDefType(ttype.types[0] === "None" ? ttype.types[1] : ttype.types[0]);
    }

    private parseValueSimple(ttype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        if (ttype instanceof $TypeInfo.PrimitiveType) {
            return this.parseValuePrimitive(ttype, whistory);
        }
        else if ((ttype instanceof $TypeInfo.ConceptType) || (ttype instanceof $TypeInfo.ConceptSetType)) {
            return this.parseValueConcept(ttype, whistory);
        }
        else {
            return this.parseValueDirect(ttype, whistory);
        }
    }

    private parseValueUnion(ttype: $TypeInfo.UnionType, whistory: boolean): BSQONParseResult {
        //everyone has a none special format option
        if(this.testToken(TokenKind.TOKEN_NONE)) {
            const nonep = this.parseNone(whistory);
            return BSQONParseResultInfo.create(new $Runtime.UnionValue("None", BSQONParseResultInfo.getParseValue(nonep, whistory)), this.lookupMustDefType("None"), BSQONParseResultInfo.getHistory(nonep, whistory), whistory);
        }

        //Check for special nonable form as well "T | none"
        if(this.isNoneableParse(ttype)) {
            //from previous check we know that the type is not none
            const vtt = this.parseValueSimple(this.getNoneableRealType(ttype), whistory);
            return BSQONParseResultInfo.create(new $Runtime.UnionValue(this.getNoneableRealType(ttype).tkey, BSQONParseResultInfo.getParseValue(vtt, whistory)), this.getNoneableRealType(ttype), BSQONParseResultInfo.getHistory(vtt, whistory), whistory);
        }

        if (this.m_parsemode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
            this.expectTokenAndPop(TokenKind.TOKEN_LBRACKET);
            const tt = this.parseType();
            this.expectTokenAndPop(TokenKind.TOKEN_COMMA);
            const vv = this.parseValue(tt, whistory);
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

            this.raiseErrorIf(!tt.isconcretetype, `Expected concrete type but got ${tt.tkey}`);
            this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(tt, ttype), `Expected type ${ttype.tkey} but got ${tt.tkey}`);
            return BSQONParseResultInfo.create(new $Runtime.UnionValue(tt.tkey, BSQONParseResultInfo.getParseValue(vv, whistory)), tt, BSQONParseResultInfo.getHistory(vv, whistory), whistory);
        }
        else {
            //it isn't none so now we start looking at prefixes
            const tk = this.peekToken()?.kind ?? "EOF";

            let rv: BSQONParseResult = undefined;
            let rt: $TypeInfo.BSQType = $TypeInfo.UnresolvedType.singleton;

            if(tk === TokenKind.TOKEN_NOTHING) {
                rv = this.parseNothing(whistory);
                rt = this.lookupMustDefType("Nothing");
            }
            else if(tk === TokenKind.TOKEN_SOMETHING) {
                const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_SOMETHING, $TypeInfo.BSQTypeTag.TYPE_OPTION], ttype);
                [rv, rt] = this.parseSomething(oftt as ($TypeInfo.SomethingType | $TypeInfo.OptionType | undefined), ttype, whistory);
            }
            else if(tk === TokenKind.TOKEN_OK) {
                const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_OK, $TypeInfo.BSQTypeTag.TYPE_RESULT], ttype);
                [rv, rt] = this.parseOk(oftt as ($TypeInfo.OkType | $TypeInfo.ResultType | undefined), ttype, whistory);
            }
            else if(tk === TokenKind.TOKEN_ERR) {
                const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_ERROR, $TypeInfo.BSQTypeTag.TYPE_RESULT], ttype);
                [rv, rt] = this.parseErr(oftt as ($TypeInfo.ErrorType | $TypeInfo.ResultType | undefined), ttype, whistory);
            }
            else if(tk === TokenKind.TOKEN_TYPE) {
                const ptt = this.peekToken()!.value;
                if(ptt === "Something") {
                    const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_SOMETHING, $TypeInfo.BSQTypeTag.TYPE_OPTION], ttype);
                    [rv, rt] = this.parseSomething(oftt as ($TypeInfo.SomethingType | $TypeInfo.OptionType | undefined), ttype, whistory);
                }
                else if(ptt === "Result") {
                    if(this.testTokensWValue({kind: TokenKind.TOKEN_TYPE, value: "Result"}, {kind: TokenKind.TOKEN_COLON_COLON, value: "::"}, {kind: TokenKind.TOKEN_TYPE, value: "Ok"})) {
                        const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_OK, $TypeInfo.BSQTypeTag.TYPE_RESULT], ttype);
                        [rv, rt] = this.parseOk(oftt as ($TypeInfo.OkType | $TypeInfo.ResultType | undefined), ttype, whistory);
                    }
                    else if(this.testTokensWValue({kind: TokenKind.TOKEN_TYPE, value: "Result"}, {kind: TokenKind.TOKEN_COLON_COLON, value: "::"}, {kind: TokenKind.TOKEN_TYPE, value: "Err"})) {
                        const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_ERROR, $TypeInfo.BSQTypeTag.TYPE_RESULT], ttype);
                        [rv, rt] = this.parseErr(oftt as ($TypeInfo.ErrorType | $TypeInfo.ResultType | undefined), ttype, whistory);
                    }
                    else {
                        rt = this.peekType();
                        if(rt instanceof $TypeInfo.OkType) {
                            rv = this.parseOk(rt, ttype, whistory)[0];
                        }
                        else {
                            rv = this.parseErr(rt as $TypeInfo.ErrorType, ttype, whistory)[0];
                        }
                    }
                }
                else if(ptt === "List") {
                    const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_LIST], ttype);
                    [rv, rt] = this.parseList(oftt as ($TypeInfo.ListType | undefined), ttype, whistory);
                }
                else if(ptt === "Stack") {
                    const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_STACK], ttype);
                    [rv, rt] = this.parseStack(oftt as ($TypeInfo.StackType | undefined), ttype, whistory);
                }
                else if(ptt === "Queue") {
                    const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_QUEUE], ttype);
                    [rv, rt] = this.parseQueue(oftt as ($TypeInfo.QueueType | undefined), ttype, whistory);
                }
                else if(ptt === "Set") {
                    const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_SET], ttype);
                    [rv, rt] = this.parseSet(oftt as ($TypeInfo.SetType | undefined), ttype, whistory);
                }
                else if(ptt === "Map") {
                    const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_MAP], ttype);
                    [rv, rt] = this.parseMap(oftt as ($TypeInfo.MapType | undefined), ttype, whistory);
                }
                else {
                    const tt = this.peekType();
                    this.raiseErrorIf(!tt.isconcretetype, `Expected concrete type but got ${tt.tkey}`);

                    rv = this.parseValue(tt, whistory);
                    rt = tt;
                }
            }
            else if(tk === TokenKind.TOKEN_LPAREN) {
                this.popToken();
                const tt = this.parseType();
                this.expectTokenAndPop(TokenKind.TOKEN_RPAREN);

                rv = this.parseValue(tt, whistory);
                rt = tt;
            }
            //Now are some (probably) common prefix/mistakes that we can warn about
            else if(tk === TokenKind.TOKEN_LBRACE) {
                this.raiseError(`Unexpected token ${tk} -- in ambigous position records need to be prefixed with a (type) and entities need a full constructor`);
            }
            else if(tk === TokenKind.TOKEN_LBRACKET) {
                this.raiseError(`Unexpected token ${tk} -- in ambigous position tuples/lists/etc. need to be prefixed with a (type)`);
            }
            else {
                let tt: string = "[UnresolvedType]";

                if(this.testToken(TokenKind.TOKEN_TRUE) || this.testToken(TokenKind.TOKEN_FALSE)) {
                    rv = this.parseBool(whistory);
                    tt = "Bool";
                }
                else if(this.testToken(TokenKind.TOKEN_NAT)) {
                    rv = this.parseNat(whistory);
                    tt = "Nat";
                }
                else if(this.testToken(TokenKind.TOKEN_INT)) {
                    rv = this.parseInt(whistory);
                    tt = "Int";
                }
                else if(this.testToken(TokenKind.TOKEN_BIG_NAT)) {
                    rv = this.parseBigNat(whistory);
                    tt = "BigNat";
                }
                else if(this.testToken(TokenKind.TOKEN_BIG_INT)) {
                    rv = this.parseBigInt(whistory);
                    tt = "BigInt";
                }
                else if(this.testToken(TokenKind.TOKEN_FLOAT)) {
                    rv = this.parseFloat(whistory);
                    tt = "Float";
                }
                else if(this.testToken(TokenKind.TOKEN_DECIMAL)) {
                    rv = this.parseDecimal(whistory);
                    tt = "Decimal";
                }
                else if(this.testToken(TokenKind.TOKEN_RATIONAL)) {
                    rv = this.parseRational(whistory);
                    tt = "Rational";
                }
                else if(this.testTokens(TokenKind.TOKEN_STRING, TokenKind.TOKEN_TYPE)) {
                    [rv, tt] = this.parseStringOfWithType(whistory);
                }
                else if(this.testTokens(TokenKind.TOKEN_ASCII_STRING, TokenKind.TOKEN_TYPE)) {
                    [rv, tt] = this.parseASCIIStringOfWithType(whistory);
                }
                else if(this.testToken(TokenKind.TOKEN_STRING)) {
                    rv = this.parseString(whistory);
                    tt = "String";
                }
                else if(this.testToken(TokenKind.TOKEN_ASCII_STRING)) {
                    rv = this.parseASCIIString(whistory);
                    tt = "ASCIIString";
                }
                else if(this.testToken(TokenKind.TOKEN_BYTE_BUFFER)) {
                    rv = this.parseByteBuffer(whistory);
                    tt = "ByteBuffer";
                }
                else if(this.testToken(TokenKind.TOKEN_REGEX)) {
                    rv = this.parseRegex(whistory);
                    tt = "Regex";
                }
                else if(this.testToken(TokenKind.TOKEN_ISO_DATE_TIME)) {
                    rv = this.parseDateTime(whistory);
                    tt = "DateTime";
                }
                else if(this.testToken(TokenKind.TOKEN_ISO_UTC_DATE_TIME)) {
                    rv = this.parseUTCDateTime(whistory);
                    tt = "UTCDateTime";
                }
                else if(this.testToken(TokenKind.TOKEN_ISO_DATE)) {
                    rv = this.parsePlainDate(whistory);
                    tt = "Date";
                }
                else if(this.testToken(TokenKind.TOKEN_ISO_TIME)) {
                    rv = this.parsePlainTime(whistory);
                    tt = "Time";
                }
                else if(this.testToken(TokenKind.TOKEN_TICK_TIME)) {
                    rv = this.parseTickTime(whistory);
                    tt = "TickTime";
                }
                else if(this.testToken(TokenKind.TOKEN_LOGICAL_TIME)) {
                    rv = this.parseLogicalTime(whistory);
                    tt = "LogicalTime";
                }
                else if(this.testToken(TokenKind.TOKEN_ISO_TIMESTAMP)) {
                    rv = this.parseISOTimeStamp(whistory);
                    tt = "Timestamp";
                }
                else if(this.testToken(TokenKind.TOKEN_UUID)) {
                    if(this.peekToken()!.value.startsWith("uuid4{")) {
                        rv = this.parseUUIDv4(whistory);
                        tt = "UUIDv4";
                    }
                    else {
                        rv = this.parseUUIDv7(whistory);
                        tt = "UUIDv7";
                    }
                }
                else if(this.testToken(TokenKind.TOKEN_SHA_HASH)) {
                    rv = this.parseSHAContentHash(whistory);
                    tt = "SHAHash";
                }
                else if(this.testToken(TokenKind.TOKEN_PATH_ITEM)) {
                    this.raiseError("PATH ITEMS ARE NOT IMPLEMENTED YET!!!");
                }
                else {
                    this.raiseError(`Expected a primitive value but got ${tk}`);
                }

                if(this.testAndPop_TypedeclUnder()) {
                    const tdtype = this.parseType();
                    this.raiseErrorIf(!(tdtype instanceof $TypeInfo.TypedeclType), `Expected a typedecl type but got ${tdtype.tkey}`);
                    this.raiseErrorIf((tdtype as $TypeInfo.TypedeclType).basetype !== tt, `Typedecl has a basetype of ${tdtype.tkey} but got ${tt}`);

                    tt = tdtype.tkey;

                    if((tdtype as $TypeInfo.TypedeclType).optStringOfValidator !== undefined) {
                        const vre = this.m_assembly.revalidators.get((tdtype as $TypeInfo.TypedeclType).optStringOfValidator!);
                        this.raiseErrorIf(vre === undefined || !$Runtime.acceptsString(vre.slice(1, -1), tt), `Typedecl string literal does not satisfy the required format: ${(tdtype as $TypeInfo.TypedeclType).optStringOfValidator!} (${vre})`);
                    }

                    if((tdtype as $TypeInfo.TypedeclType).optPathOfValidator !== undefined) {
                        this.raiseError("PATH ITEMS ARE NOT IMPLEMENTED YET!!!");
                    }

                    if((tdtype as $TypeInfo.TypedeclType).hasvalidations) {
                        this.m_typedeclChecks.push({ttype: tt, tvalue: rv});
                    }
                }

                rt = this.lookupMustDefType(tt);
            }

            this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(rt, ttype), `Value is not of type ${ttype.tkey} -- got ${rt.tkey}`);   
            return BSQONParseResultInfo.create(new $Runtime.UnionValue(rt.tkey, BSQONParseResultInfo.getParseValue(rv, whistory)), rt, BSQONParseResultInfo.getHistory(rv, whistory), whistory);
        }
    }

    private parseValue(ttype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        if(this.testTokens(TokenKind.TOKEN_LPAREN, TokenKind.TOKEN_LET)) {
            this.popToken();
            this.popToken();

            const vname = this.expectTokenAndPop(TokenKind.TOKEN_PROPERTY).value;
            this.expectTokenAndPop(TokenKind.TOKEN_COLON);
            const vtype = this.parseType();
            this.expectTokenAndPop(TokenKind.TOKEN_EQUALS);
            const vvalue = this.parseValue(vtype, true);
            
            this.raiseErrorIf(this.m_refs.has(vname), `Duplicate let binding ${vname}`);
            this.m_refs.set(vname, [BSQONParseResultInfo.getParseValue(vvalue, true), BSQONParseResultInfo.getValueType(vvalue, true), BSQONParseResultInfo.getHistory(vvalue, true)]);

            this.expectTokenAndPop(TokenKind.TOKEN_IN);

            const vv = this.parseExpression(ttype, whistory);

            this.expectTokenAndPop(TokenKind.TOKEN_RPAREN);

            this.m_refs.delete(vname);
            return vv;
        }
        else if(this.testTokens(TokenKind.TOKEN_SRC) || this.testTokens(TokenKind.TOKEN_REFERENCE)) {
            return this.parseExpression(ttype, whistory);
        }
        else {
            if (ttype instanceof $TypeInfo.UnionType) {
                return this.parseValueUnion(ttype, whistory);
            }
            else {
                return this.parseValueSimple(ttype, whistory);
            }
        }
    }

    static parse(input: string, ttype: $TypeInfo.BSQTypeKey, defaultns: string, importmap: Map<string, string>, assembly: $TypeInfo.AssemblyInfo, mode: $Runtime.NotationMode, srcbind: [any, $TypeInfo.BSQType, any] | undefined): {result: any, entityChecks: {etype: $TypeInfo.BSQTypeKey, evalue: object}[], typedeclChecks: {ttype: $TypeInfo.BSQTypeKey, tvalue: any}[]} {
        const parser = new BSQONParser(mode, defaultns, importmap, assembly, input, srcbind);
        const result = parser.parseValue(parser.lookupMustDefType(ttype), false);

        return {result: result, entityChecks: parser.m_stdentityChecks, typedeclChecks: parser.m_typedeclChecks};
    }

    static parseValueStd(input: string, ttype: $TypeInfo.BSQTypeKey, defaultns: string, assembly: $TypeInfo.AssemblyInfo): any {
        const parser = new BSQONParser($Runtime.NotationMode.NOTATION_MODE_BSQON, defaultns, new Map<string, string>(), assembly, input, undefined);

        const rr = parser.parseValue(parser.lookupMustDefType(ttype), false);
        return rr;
    }

    static parseInputsStd(input: string, ttypes: $TypeInfo.BSQTypeKey[], defaultns: string, assembly: $TypeInfo.AssemblyInfo): {result: any[], entityChecks: {etype: $TypeInfo.BSQTypeKey, evalue: object}[], typedeclChecks: {ttype: $TypeInfo.BSQTypeKey, tvalue: any}[]} {
        const parser = new BSQONParser($Runtime.NotationMode.NOTATION_MODE_BSQON, defaultns, new Map<string, string>(), assembly, input, undefined);

        let result: any[] = [];
        for(let i = 0; i < ttypes.length; ++i) {
            const rr = parser.parseValue(parser.lookupMustDefType(ttypes[i]), false);
            result.push(rr);
        }

        return {result: result, entityChecks: parser.m_stdentityChecks, typedeclChecks: parser.m_typedeclChecks};
    }
}

export {
    BSQONParser, BSQONParseError
}
