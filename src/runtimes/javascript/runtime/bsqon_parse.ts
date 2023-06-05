import {Decimal} from "decimal.js";
import Fraction from "fraction.js";

import * as $Constants from "./constants";
import * as $TypeInfo from "./typeinfo";
import * as $Runtime from "./runtime";


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
    TOKEN_UNDER = "_",
    TOKEN_SOMETHING = "something",
    TOKEN_OK = "ok",
    TOKEN_ERR = "err",

    TOKEN_LBRACE = "{",
    TOKEN_RBRACE = "}",
    TOKEN_LBRACKET = "[",
    TOKEN_RBRACKET = "]",
    TOKEN_LPAREN = "(",
    TOKEN_RPAREN = ")",
    TOKEN_RLET = "{|",
    TOKEN_LLET = "|}",
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

const _s_stringRe = /"[^"\\\r\n]*(\\(.|\r?\n)[^"\\\r\n]*)*"/uy;
const _s_ascii_stringRe = /ascii\{"[^"\\\r\n]*(\\(.|\r?\n)[^"\\\r\n]*)*"\}/uy;

const _s_regexRe = /\/[^"\\\r\n]*(\\(.)[^"\\\r\n]*)*\//y;
const _s_regexCheckRe = /^\/[^"\\\r\n]*(\\(.)[^"\\\r\n]*)*\/$/y;

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
    TokenKind.TOKEN_NULL,
    TokenKind.TOKEN_NONE,
    TokenKind.TOKEN_NOTHING,
    TokenKind.TOKEN_TYPE,
    TokenKind.TOKEN_UNDER,
    TokenKind.TOKEN_SOMETHING,
    TokenKind.TOKEN_OK,
    TokenKind.TOKEN_ERR,

    TokenKind.TOKEN_LBRACE,
    TokenKind.TOKEN_RBRACE,
    TokenKind.TOKEN_LBRACKET,
    TokenKind.TOKEN_RBRACKET,
    TokenKind.TOKEN_LPAREN,
    TokenKind.TOKEN_RPAREN,
    TokenKind.TOKEN_LANGLE, 
    TokenKind.TOKEN_RANGLE,
    TokenKind.TOKEN_RLET,
    TokenKind.TOKEN_LLET,

    TokenKind.TOKEN_COLON,
    TokenKind.TOKEN_COLON_COLON,
    TokenKind.TOKEN_AMP,
    TokenKind.TOKEN_BAR,
    TokenKind.TOKEN_ENTRY,
    TokenKind.TOKEN_LDOTS,
    TokenKind.TOKEN_COMMA,
    TokenKind.TOKEN_EQUALS,
    TokenKind.TOKEN_LET,
    TokenKind.TOKEN_IN
];

enum NotationMode {
    NOTATION_MODE_DEFAULT = "BSQ_OBJ_NOTATION_DEFAULT",
    NOTATION_MODE_JSON = "BSQ_OBJ_NOTATION_JSON",
    NOTATION_MODE_FULL = "BSQ_OBJ_NOTATION_FULL"
}

const _s_core_types = [
    "None", "Bool", "Int", "Nat", "BigInt", "BigNat", "Rational", "Float", "Decimal", "String", "ASCIIString",
    "ByteBuffer", "DateTime", "UTCDateTime", "PlainDate", "PlainTime", "TickTime", "LogicalTime", "ISOTimeStamp", "UUIDv4", "UUIDv7", "SHAContentHash", 
    "LatLongCoordinate", "Regex", "Nothing"
];

const _s_core_types_with_one_template = [
    "StringOf", "ASCIIStringOf", "Something", "Option", "Path", "PathFragment", "PathGlob", "List", "Stack", "Queue", "Set"
]

const _s_core_types_with_map = [
    "MapEntry", "Map"
]

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

class BSQONParseResult {
    readonly value: any;
    readonly vtype: $TypeInfo.BSQType;
    readonly parsetree: any;

    constructor(val: any, vtype: $TypeInfo.BSQType, parsetree: any) {
        this.value = val;
        this.vtype = vtype;
        this.parsetree = parsetree;
    }

    static create(val: any, vtype: $TypeInfo.BSQType, parsetree: any, whistory: boolean): BSQONParseResult | any {
        if(!whistory) {
            return val;
        }
        else {
            return new BSQONParseResult(val, vtype, parsetree);
        }
    }

    static getParseValue(parseinfo: any, whistory: boolean): any {
        return !whistory ? parseinfo : parseinfo.value;
    }
    
    static getValueType(parseinfo: any, whistory: boolean): $TypeInfo.BSQType {
        return !whistory ? undefined : parseinfo[1].vtype;
    }
    
    static getHistory(parseinfo: any, whistory: boolean): any {
        return !whistory ? undefined : parseinfo[1].parsetree;
    }
}

class BSQONParse {
    readonly m_parsemode: NotationMode;
   
    readonly m_defaultns: string;
    readonly m_importmap: Map<string, string>;
    readonly m_assembly: $TypeInfo.AssemblyInfo;

    readonly m_input: string;
    m_cpos: number;
    m_lastToken: {kind: string, value: string} | undefined;

    readonly m_stdentityChecks: $TypeInfo.BSQTypeKey[];
    readonly m_typedeclChecks: $TypeInfo.BSQTypeKey[];

    readonly m_srcbind: [any, $TypeInfo.BSQType, any] | undefined; //a [value, type, ttree] where type is always a concrete type
    readonly m_refs: Map<string, [any, $TypeInfo.BSQType, any]>; //maps from names to [value, type, ttree] where type is always a concrete type

    constructor(mode: NotationMode, defaultns: string, importmap: Map<string, string>, assembly: $TypeInfo.AssemblyInfo, str: string, srcbind: [any, $TypeInfo.BSQType, any] | undefined) {
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
        if (this.m_parsemode === NotationMode.NOTATION_MODE_JSON) {
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
    
        if (this.m_parsemode !== NotationMode.NOTATION_MODE_JSON) {
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

    private testToken(tkind: string): boolean {
        return this.peekToken() !== undefined && this.peekToken()!.kind === tkind;
    }

    private testTokens(...tkinds: string[]): boolean {
        const opos = this.m_cpos;
        for (let i = 0; i < tkinds.length; ++i) {
            if (!this.testToken(tkinds[i])) {
                this.m_cpos = opos;
                return false;
            }
        }

        this.m_cpos = opos;
        return true;
    }

    private testTypePrefixTokens(...tkinds: string[]): boolean {
        if (!this.testToken(TokenKind.TOKEN_TYPE)) {
            return false;
        }

        const opos = this.m_cpos;
        while (this.testTokens(TokenKind.TOKEN_COLON_COLON, TokenKind.TOKEN_TYPE)) {
            this.popToken();
            this.expectTokenAndPop(TokenKind.TOKEN_TYPE);
        }

        for (let i = 0; i < tkinds.length; ++i) {
            if (!this.testToken(tkinds[i])) {
                this.m_cpos = opos;
                return false;
            }
        }

        this.m_cpos = opos;
        return true;
    }

    private raiseError(msg: string) {
        throw new BSQONParseError(msg, this.m_cpos);
    }

    private raiseErrorIf(cond: boolean, msg: string) {
        if (cond) {
            this.raiseError(msg);
        }
    }

    private expectToken(tkind: string) {
        this.raiseErrorIf(!this.testToken(tkind), `Expected token ${tkind} but got ${this.peekToken()}`);
    }

    private expectTokenAndPop(tkind: string): {kind: string, value: string} {
        this.expectToken(tkind);
        return this.popToken() as {kind: string, value: string};
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
            scopedname = `${this.m_defaultns}::${tt.join("::")}`;
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
        return this.resolveTypeFromNameList([tname], []);
    }

    private resolveRelaxedTypeMatch(oftags: $TypeInfo.BSQTypeTag[], opts: $TypeInfo.BSQType[]): $TypeInfo.BSQType {
        this.raiseErrorIf(this.m_parsemode === NotationMode.NOTATION_MODE_FULL, `Cannot use relaxed types in this (strict) BSQON context`);

        if (opts.length === 1) {
            this.raiseErrorIf(!oftags.includes(opts[0].tag), `Could not resolve relaxed type ${opts[0].tkey}, is not matchable`);

            return opts[0];
        }
        else {
            const popts = opts.filter((tt) => oftags.includes((this.m_assembly.typerefs.get(tt.tkey) as $TypeInfo.BSQType).tag));
            this.raiseErrorIf(popts.length === 0, `Could not resolve relaxed type from (${opts.map((tt) => tt.tkey).join(", ")}), no candidates found`);
            this.raiseErrorIf(popts.length > 1, `Could not resolve relaxed type from (${opts.map((tt) => tt.tkey).join(", ")}), multiple candidates found`);

            return popts[0];
        }
    }

    private resolveRelaxedTemplateMatch(opts: $TypeInfo.BSQType[]): $TypeInfo.BSQType {
        this.raiseErrorIf(this.m_parsemode === NotationMode.NOTATION_MODE_FULL, `Cannot use relaxed types in this (strict) BSQON context`);

        if (opts.length === 1) {
            return opts[0];
        }
        else {
            const popts = opts.filter((tt) => tt.getTerms().length !== 0);
            this.raiseErrorIf(popts.length === 0, `Could not resolve relaxed type from (${opts.map((tt) => tt.tkey).join(", ")}), no candidates found`);
            this.raiseErrorIf(popts.length > 1, `Could not resolve relaxed type from (${opts.map((tt) => tt.tkey).join(", ")}), multiple candidates found`);

            return popts[0];
        }
    }

    private processCoreTypeW1Term(tname: string, terms: $TypeInfo.BSQType[], opts: $TypeInfo.BSQType[]): $TypeInfo.BSQType {
        if (tname === "StringOf") {
            this.raiseErrorIf(terms.length !== 1, `Type ${tname} requires one type argument`);
            return this.lookupMustDefType(`StringOf<${terms[0].tkey}>`);
        }
        else if (tname === "ASCIIStringOf") {
            this.raiseErrorIf(terms.length !== 1, `Type ${tname} requires one type argument`);
            return this.lookupMustDefType(`ASCIIStringOf<${terms[0].tkey}>`);
        }
        else if (tname === "Something") {
            let t: $TypeInfo.BSQType = $TypeInfo.UnresolvedType.singleton;
            if (terms.length === 1) {
                t = terms[0];
            }
            else {
                t = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_SOMETHING, $TypeInfo.BSQTypeTag.TYPE_OPTION], opts);
            }

            return this.lookupMustDefType(`Something<${t.tkey}>`);
        }
        else if (tname === "Option") {
            let t: $TypeInfo.BSQType = $TypeInfo.UnresolvedType.singleton;
            if (terms.length === 1) {
                t = terms[0];
            }
            else {
                t = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_OPTION], opts);
            }

            return this.lookupMustDefType(`Option<${t.tkey}>`);
        }
        else if (tname === "Path") {
            this.raiseErrorIf(terms.length !== 1, `Type ${tname} requires one type argument`);
            return this.lookupMustDefType(`Path<${terms[0].tkey}>`);
        }
        else if (tname === "PathFragment") {
            this.raiseErrorIf(terms.length !== 1, `Type ${tname} requires one type argument`);
            return this.lookupMustDefType(`PathFragment<${terms[0].tkey}>`);
        }
        else if (tname === "PathGlob") {
            this.raiseErrorIf(terms.length !== 1, `Type ${tname} requires one type argument`);
            return this.lookupMustDefType(`PathGlob<${terms[0].tkey}>`);
        }
        else {
            let ttag = $TypeInfo.BSQTypeTag.TYPE_UNRESOLVED;
            if (tname === "List") {
                ttag = $TypeInfo.BSQTypeTag.TYPE_LIST;
            }
            else if (tname === "Stack") {
                ttag = $TypeInfo.BSQTypeTag.TYPE_STACK;
            }
            else if (tname === "Queue") {
                ttag = $TypeInfo.BSQTypeTag.TYPE_QUEUE;
            }
            else {
                ttag = $TypeInfo.BSQTypeTag.TYPE_SET;
            }

            let t: $TypeInfo.BSQType = $TypeInfo.UnresolvedType.singleton;
            if (terms.length === 1) {
                t = terms[0];
            }
            else {
                t = this.resolveRelaxedTypeMatch([ttag], opts);
            }

            if (tname === "List") {
                return this.lookupMustDefType(`List<${t.tkey}>`);
            }
            else if (tname === "Stack") {
                return this.lookupMustDefType(`Stack<${t.tkey}>`);
            }
            else if (tname === "Queue") {
                return this.lookupMustDefType(`Queue<${t.tkey}>`);
            }
            else {
                this.raiseErrorIf(tname !== "Set", `Unknown core type ${tname}`);

                return this.lookupMustDefType(`Set<${t.tkey}>`);
            }
        }
    }

    private processCoreTypeW2Terms(tname: string, terms: $TypeInfo.BSQType[], opts: $TypeInfo.BSQType[]): $TypeInfo.BSQType {
        if (tname === "Result::Ok") {
            this.raiseErrorIf(terms.length !== 2, `Type ${tname} requires two type arguments`);
            return this.lookupMustDefType(`Result<${terms[0].tkey}, ${terms[1].tkey}>::Ok`);
        }
        else if (tname === "Result::Error") {
            this.raiseErrorIf(terms.length !== 2, `Type ${tname} requires two type arguments`);
            return this.lookupMustDefType(`Result<${terms[0].tkey}, ${terms[1].tkey}>::Err`);
        }
        else if (tname === "Result") {
            this.raiseErrorIf(terms.length !== 2, `Type ${tname} requires two type arguments`);
            return this.lookupMustDefType(`Result<${terms[0].tkey}, ${terms[1].tkey}>`);
        }
        else {
            let ttag = $TypeInfo.BSQTypeTag.TYPE_UNRESOLVED;
            if (tname === "MapEntry") {
                ttag = $TypeInfo.BSQTypeTag.TYPE_MAP_ENTRY;
            }
            else {
                ttag = $TypeInfo.BSQTypeTag.TYPE_MAP;
            }

            if (terms.length === 2) {
                if (tname === "MapEntry") {
                    return this.lookupMustDefType(`MapEntry<${terms[0].tkey, terms[1].tkey}>`);
                }
                else {
                    this.raiseErrorIf(tname !== "Map", `Unknown core type ${tname}`);

                    return this.lookupMustDefType(`Map<${terms[0].tkey, terms[1].tkey}>`);
                }
            }
            else {
                const t = this.resolveRelaxedTypeMatch([ttag], opts);

                if (tname === "MapEntry") {
                    const tme = t as $TypeInfo.MapEntryType;
                    return this.lookupMustDefType(`MapEntry<${tme.ktype, tme.vtype}>`);
                }
                else {
                    this.raiseErrorIf(tname !== "Map", `Unknown core type ${tname}`);

                    const tm = t as $TypeInfo.MapType;
                    return this.lookupMustDefType(`Map<${tm.ktype, tm.vtype}>`);
                }
            }
        }
    }

    private parseNominalType(opts: $TypeInfo.BSQType[]): $TypeInfo.BSQType {
        let tnames = [this.expectTokenAndPop(TokenKind.TOKEN_TYPE).value];
        while (this.testTokens(TokenKind.TOKEN_COLON_COLON, TokenKind.TOKEN_TYPE)) {
            this.popToken();
            tnames.push(this.expectTokenAndPop(TokenKind.TOKEN_TYPE).value);
        }

        let terms = [];
        if (this.testToken(TokenKind.TOKEN_LANGLE)) {
            const eterms = this.resolveRelaxedTemplateMatch(opts).getTerms();
            this.popToken();

            while (terms.length === 0 || this.testToken(TokenKind.TOKEN_COMMA)) {
                if (this.testToken(TokenKind.TOKEN_COMMA)) {
                    this.popToken();
                }

                this.raiseErrorIf(terms.length >= eterms.length, `Expected a type with ${eterms.length} (${opts.map((tt) => tt.tkey).join(", ")}) but got ${terms.length + 1} terms`)
                terms.push(this.parseType(this.lookupMustDefType(eterms[terms.length])));
            }
        }

        if (_s_core_types.includes(tnames[0])) {
            this.raiseErrorIf(terms.length !== 0, `Type ${tnames[0]} does not take type arguments`);

            return this.processCoreType(tnames[0]);
        }
        else if (_s_core_types_with_one_template.includes(tnames[0])) {
            return this.processCoreTypeW1Term(tnames[0], terms, opts);
        }
        else if (_s_core_types_with_map.includes(tnames[0])) {
            return this.processCoreTypeW2Terms(tnames[0], terms, opts);
        }
        else if (tnames[0] === "Result") {
            if (!this.testToken(TokenKind.TOKEN_COLON_COLON)) {
                return this.processCoreTypeW2Terms(tnames[0], terms, opts);
            }
            else {
                this.expectTokenAndPop(TokenKind.TOKEN_COLON_COLON);
                const tname = this.expectTokenAndPop(TokenKind.TOKEN_TYPE).value;
                return this.processCoreTypeW2Terms("Result::" + tname, terms, opts);
            }
        }
        else {
            return this.resolveTypeFromNameList(tnames, terms);
        }
    }

    private parseTupleType(opts: $TypeInfo.BSQType[]): $TypeInfo.BSQType {
        const expected = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_TUPLE], opts) as $TypeInfo.TupleType;

        let entries: $TypeInfo.BSQType[] = [];
        this.popToken();
        while (entries.length === 0 || this.testToken(TokenKind.TOKEN_COMMA)) {
            if (this.testToken(TokenKind.TOKEN_COMMA)) {
                this.popToken();
            }

            this.raiseErrorIf(entries.length >= expected.entries.length, `Expected a tuple of length ${expected.entries.length}`);
            
            const ee = this.lookupMustDefType(expected.entries[entries.length]);
            entries.push(this.parseType(ee));
        }
        this.raiseErrorIf(entries.length !== expected.entries.length, `Expected a tuple of length ${expected.entries.length}`);

        return this.lookupMustDefType(`[${entries.map((ee) => ee.tkey).join(", ")}]`);
    }

    private parseRecordType(opts: $TypeInfo.BSQType[]): $TypeInfo.BSQType {
        const expected = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_RECORD], opts) as $TypeInfo.RecordType;

        let entries: {pname: string, rtype: $TypeInfo.BSQType}[] = [];
        this.popToken();
        while (entries.length === 0 || this.testToken(TokenKind.TOKEN_COMMA)) {
            if (this.testToken(TokenKind.TOKEN_COMMA)) {
                this.popToken();
            }

            const pname = this.expectTokenAndPop(TokenKind.TOKEN_PROPERTY).value;

            this.raiseErrorIf(entries.length >= expected.entries.length, `Expected a record with ${expected.entries.length} properties`);
            
            const ee = this.lookupMustDefType(expected.entries[entries.length].rtype);
            const rtype = this.parseType(ee);

            entries.push({pname: pname, rtype: this.parseType(rtype)});
        }
        this.raiseErrorIf(entries.length !== expected.entries.length, `Expected a record with ${expected.entries.length} properties`);

        const ees = entries.sort((a, b) => a.pname.localeCompare(b.pname)).map((ee) => `${ee.pname}: ${ee.rtype.tkey}`);
        return this.lookupMustDefType(`{${ees.join(", ")}}`);
    }

    private parseBaseType(opts: $TypeInfo.BSQType[]): $TypeInfo.BSQType {
        if (this.testToken(TokenKind.TOKEN_TYPE)) {
            return this.parseNominalType(opts);
        }
        else if (this.testToken(TokenKind.TOKEN_LBRACKET)) {
            return this.parseTupleType(opts);
        }
        else if (this.testToken(TokenKind.TOKEN_LBRACE)) {
            return this.parseRecordType(opts);
        }
        else {
            this.raiseError(`Unexpected token when parsing type: ${this.peekToken()?.value || "EOF"}`);
            return $TypeInfo.UnresolvedType.singleton;
        }
    }

    private parseConceptSetType(opts: $TypeInfo.BSQType[]): $TypeInfo.BSQType {
        const lt = this.parseBaseType(opts);
        if (!this.testToken(TokenKind.TOKEN_AMP)) {
            return lt;
        }
        else {
            let opts = [lt];
            while (this.testToken(TokenKind.TOKEN_AMP)) {
                this.popToken();
                opts.push(this.parseConceptSetType(opts));
            }

            return this.lookupMustDefType(opts.map((tt) => tt.tkey).sort((a, b) => a.localeCompare(b)).join("&"));
        }
    }

    private parseUnionType(expected: $TypeInfo.BSQType) {
        const opts = (expected.tag === $TypeInfo.BSQTypeTag.TYPE_UNION) ? (expected as $TypeInfo.UnionType).types.map((tt) => this.lookupMustDefType(tt)) : [expected];
        
        const lt = this.parseConceptSetType(opts);
        if (!this.testToken(TokenKind.TOKEN_BAR)) {
            return lt;
        }
        else {
            let opts = [lt];
            while (this.testToken(TokenKind.TOKEN_BAR)) {
                this.popToken();
                opts.push(this.parseUnionType(expected));
            }

            return this.lookupMustDefType(opts.map((tt) => tt.tkey).sort((a, b) => a.localeCompare(b)).join(" | "));
        }
    }

    private parseType(expected: $TypeInfo.BSQType): $TypeInfo.BSQType {
        if (this.m_parsemode !== NotationMode.NOTATION_MODE_JSON) {
            return this.parseUnionType(expected);
        }
        else {
            this.raiseErrorIf(this.testToken(TokenKind.TOKEN_STRING), `Expected type: but got ${this.peekToken()?.value || "EOF"}`);
            this.unquoteStringForTypeParse();

            return this.parseUnionType(expected);
        }
    }

    private parseSrc(oftype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        this.expectTokenAndPop(TokenKind.TOKEN_SRC);

        this.raiseErrorIf(this.m_srcbind === undefined, "Invalid use of $SRC binding");
        this.raiseErrorIf(!$TypeInfo.checkSubtype(this.m_assembly, this.m_srcbind[1], oftype), `Reference ${ref} has type ${this.m_srcbind[1].ttag} which is not a subtype of ${oftype.ttag}`);
        const rr = oftype.ttag === this.m_srcbind[1].ttag ? this.m_srcbind[0] : new $Runtime.UnionValue(this.m_srcbind[1], this.m_srcbind[0]);

        return BSQONParseResult.create(rr, this.m_srcbind[1], this.m_srcbind[2], breq);
    }
    private parseReference(oftype, breq) {
        const ref = this.expectTokenAndPop(TOKEN_REFERENCE).value;

        this.raiseErrorIf(!this.m_refs.has(ref), `Reference ${ref} not found`);
        const rinfo = this.m_refs.get(ref);

        this.raiseErrorIf(!$TypeInfo.checkSubtype(this.m_assembly, rinfo[1], oftype), `Reference ${ref} has type ${rinfo[1].ttag} which is not a subtype of ${oftype.ttag}`);
        const rr = oftype.ttag === rinfo[1].ttag ? rinfo[0] : new $Runtime.UnionValue(rinfo[1], rinfo[0]);

        return createBSQONParseResult(rr, rinfo[1], rinfo[2], breq);
    }
    private parseBaseExpression(oftype, breq) {
        if (this.testToken(TOKEN_SRC)) {
            return this.parseSrc(oftype, breq);
        }
        else if (this.testToken(TOKEN_REFERENCE)) {
            return this.parseReference(oftype, breq);
        }
        else {
            this.expectTokenAndPop(TOKEN_LPAREN);
            const re = this.parseExpression(oftype, breq);
            this.expectTokenAndPop(TOKEN_RPAREN);

            return re;
        }
    }
    private parsePostfixOp(oftype, breq) {
        const bexp = this.parseBaseExpression(oftype, true);

        let vv = bexp;
        while (this.testToken(TOKEN_DOT_NAME) || this.testToken(TOKEN_DOT_IDX) || this.testToken(TOKEN_LBRACKET)) {
            let aval = undefined;
            let ptype = undefined;

            if (this.testToken(TOKEN_DOT_NAME)) {
                const iname = this.popToken().value.slice(1);
                const vval = getBSQONParseValue(vv);

                if (getBSQONParseInfo(vv).ctype === $TypeInfo.TYPE_RECORD) {
                    aval = $TypeInfo.isUnionValueRepr(vval) ? vval[iname] : vval.value[iname];
                    ptype = getBSQONParseInfo(vv).ttree[iname];
                }
                else if (getBSQONParseInfo(vv).ctype === $TypeInfo.TYPE_SIMPLE_ENTITY) {
                    aval = $TypeInfo.isUnionValueRepr(vval) ? vval[iname] : vval.value[iname];
                    ptype = getBSQONParseInfo(vv).ttree[iname];
                }
                else if (getBSQONParseInfo(vv).ctype === $TypeInfo.TYPE_SOMETHING) {
                    this.raiseErrorIf(iname !== "value", `Expected 'value' property access but got ${iname}`);

                    aval = $TypeInfo.isUnionValueRepr(vval) ? vval : vval.value;
                    ptype = getBSQONParseInfo(vv).ttree[0];
                }
                else if (getBSQONParseInfo(vv).ctype === $TypeInfo.TYPE_MAP_ENTRY) {
                    this.raiseErrorIf(iname !== "key" && iname !== "value", `Expected 'key' or 'value' property access but got ${iname}`);

                    if (iname === "key") {
                        $TypeInfo.isUnionValueRepr(vval) ? vval[0] : vval.value[0];
                        ptype = getBSQONParseInfo(vv).ttree[0];
                    }
                    else if (iname === "value") {
                        $TypeInfo.isUnionValueRepr(vval) ? vval[1] : vval.value[1];
                        ptype = getBSQONParseInfo(vv).ttree[1];
                    }
                }
                else {
                    this.raiseError(`Invalid use of '.' operator -- ${getBSQONParseInfo(vv).ctype.ttag} is not a record, nominal, option/something, or map entry type`);
                }
            }
            else if (this.testToken(TOKEN_DOT_IDX)) {
                this.raiseErrorIf(getBSQONParseInfo(vv).ctype.tag !== $TypeInfo.TYPE_TUPLE, `Invalid use of '[]' operator -- ${getBSQONParseInfo(vv).ctype.ttag} is not a tuple type`);

                const idx = Number.parseInt(this.expectTokenAndPop(TOKEN_DOT_IDX).slice(1));
                const tuprepr = $TypeInfo.isUnionValueRepr(vval) ? vval : vval.value;

                this.raiseErrorIf(idx >= tuprepr.length, `Invalid use of '[]' operator -- index ${idx} is out of bounds for tuple type ${getBSQONParseInfo(vv).ctype.ttag}`);
                aval = tuprepr[idx];
                ptype = getBSQONParseInfo(vv).ttree[idx];
            }
            else {
                if (getBSQONParseInfo(vv).ctype.tag === $TypeInfo.TYPE_LIST) {
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

        return createBSQONParseResult(rr, getBSQONParseInfoCType(vv), getBSQONParseInfoTTree(vv), breq);
    }
    private parseExpression(oftype, breq) {
        return this.parsePostfixOp(oftype, breq);
    }
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
        this.raiseErrorIf(!_s_shahashCheckRE.test(tk), `Expected SHA 512 hash but got ${sh}`);
    }

    return createBSQONParseResult(sh, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "SHAContentHash"), undefined, breq);
}
BSQONParse.prototype.parseRegex = function (breq) {
    let re = undefined;
    if(!this.isJSONMode()) {
        re = this.expectTokenAndPop(TOKEN_REGEX).value;
    }
    else {
        re = this.expectTokenAndPop(TOKEN_STRING).value;
        this.raiseErrorIf(!_s_regexCheckRe.test(re), `Expected a regex string but got ${re}`);
    }

    return createBSQONParseResult(re, $TypeInfo.resolveTypeInAssembly(this.m_assembly, "Regex"), undefined, breq);
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
    let sval = undefined;
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_STRING).value;
        const st = this.parseType(ttype.oftype);
        this.raiseErrorIf(st.ttag !== ttype.oftype.ttag, `Expected ${ttype.tag} but got StringOf<${st.ttag}>`);
        
        sval = tk;
    }
    else {
        sval = this.expectTokenAndPop(TOKEN_STRING).value;
    }

    const vre = this.m_assembly.revalidators.get(ttype.oftype.ttag);
    this.raiseErrorIf(!$Runtime.acceptsString(vre[1], sval), `String literal does not satisfy the required format: ${ttype.oftype.ttag} (${vre[0]})`);

    return createBSQONParseResult(sval, ttype, undefined, breq);
}
BSQONParse.prototype.parseASCIIStringOf = function (ttype, breq) {
    let sval = undefined;
    if(!this.isJSONMode()) {
        const tk = this.expectTokenAndPop(TOKEN_ASCII_STRING).value;
        const st = this.parseType(ttype.oftype);
        this.raiseErrorIf(st.ttag !== ttype.oftype.ttag, `Expected ${ttype.tag} but got ASCIIStringOf<${st.ttag}>`);
        
        sval = tk.slice(6, -1);
    }
    else {
        sval = this.expectTokenAndPop(TOKEN_STRING).value;
    }

    const vre = this.m_assembly.revalidators.get(ttype.oftype.ttag);
    this.raiseErrorIf(!$Runtime.acceptsString(vre[1], sval), `String literal does not satisfy the required format: ${ttype.oftype.ttag} (${vre[0]})`);

    return createBSQONParseResult(sval, ttype, undefined, breq);
}
BSQONParse.prototype.parsePath = function (ttype, breq) {
    this.raiseError("NOT IMPLEMENTED: PATH");
    /*
    let pth = undefined;
    if(!this.isJSONMode()) {
        const ptk = this.expectTokenAndPop(TOKEN_PATH_ITEM).value;
    }
    else {
        const ptk = this.expectTokenAndPop(TOKEN_STRING).value;
    }
    */
}
BSQONParse.prototype.parsePathFragment = function (ttype, breq) {
    this.raiseError("NOT IMPLEMENTED: PATH FRAGMENT");
}
BSQONParse.prototype.parsePathGlob = function (ttype, breq) {
    this.raiseError("NOT IMPLEMENTED: PATH GLOB");
}
BSQONParse.prototype.parseSomething = function (ttype, breq) {
    let vv = undefined;
    if(!this.isJSONMode()) {
        if(this.isFullMode()) {
            const stype = this.parseType(ttype);

            this.expectTokenAndPop(TOKEN_LBRACE);
            vv = this.parseValue(stype.oftype, breq);
            this.expectTokenAndPop(TOKEN_RBRACE);
        }
        else {
            if(this.testToken(TOKEN_SOMETHING)) {    
                this.expectTokenAndPop(TOKEN_LPAREN);
                vv = this.parseValue(ttype.oftype, breq);
                this.expectTokenAndPop(TOKEN_RPAREN);
            }
            else {
                const stype = this.parseType(ttype);
    
                this.expectTokenAndPop(TOKEN_LBRACE);
                vv = this.parseValue(stype.oftype, breq);
                this.expectTokenAndPop(TOKEN_RBRACE);
            }
        }
    }
    else {
        vv = this.parseValue(ttype.oftype, breq);
    }

    return createBSQONParseResult(getBSQONParseValue(vv), ttype, [getBSQONParseInfoTTree(vv)], breq);
}
BSQONParse.prototype.parseOption = function (ttype, breq) {
    if(!this.isJSONMode()) {
        let vv = undefined;
        let sstype = $TypeInfo.unresolvedType;
        if(this.testToken(TOKEN_NOTHING)) {
            sstype = $TypeInfo.resolveTypeInAssembly(this.m_assembly, "Nothing");
            vv = this.parseNothing(sstype, breq);
        }
        else {
            sstype = $TypeInfo.resolveTypeInAssembly(this.m_assembly, `Something<${ttype.oftype}>`);
            vv = this.parseSomething(sstype, breq);
        }

        return createBSQONParseResult(new $Runtime.UnionValue(sstype, getBSQONParseValue(vv)), sstype, getBSQONParseInfoTTree(vv), breq);
    }
    else {
        this.expectTokenAndPop(TOKEN_LBRACKET);
        const sstype = this.parseType(ttype);

        this.raiseErrorIf(!$Runtime.isTypeUniquelyResolvable(sstype), `Type ${sstype.ttag} is not unique type for parsing`);
        this.raiseErrorIf(stype.ttag !== "Nothing" && stype.ttag !== `Something<${ttype.oftype}>`, `Type ${sstype.ttag} is not a valid subtype of Option<T>`);

        const vv = this.parseValue(sstype, breq);
        this.expectTokenAndPop(TOKEN_RBRACKET);

        return createBSQONParseResult(new $Runtime.UnionValue(sstype, getBSQONParseValue(vv)), sstype, getBSQONParseInfoTTree(vv), breq);
    }
}
BSQONParse.prototype.parseOk = function (ttype, breq) {
    let vv = undefined;
    if(!this.isJSONMode()) {
        if(this.isFullMode()) {
            const stype = this.parseType(ttype);

            this.expectTokenAndPop(TOKEN_LBRACE);
            vv = this.parseValue(stype.ttype, breq);
            this.expectTokenAndPop(TOKEN_RBRACE);
        }
        else {
            if(this.testToken(TOKEN_OK)) {    
                this.expectTokenAndPop(TOKEN_LPAREN);
                vv = this.parseValue(ttype.ttype, breq);
                this.expectTokenAndPop(TOKEN_RPAREN);
            }
            else {
                const stype = this.parseType(tt);
                
                this.expectTokenAndPop(TOKEN_LBRACE);
                vv = this.parseValue(stype.ttype, breq);
                this.expectTokenAndPop(TOKEN_RBRACE);
            }
        }
    }
    else {
        vv = this.parseValue(ttype.oftype, breq);
    }

    return createBSQONParseResult(getBSQONParseValue(vv), ttype, [getBSQONParseInfoTTree(vv)], breq);
}
BSQONParse.prototype.parseErr = function (ttype, breq) {
    let vv = undefined;
    if(!this.isJSONMode()) {
        if(this.isFullMode()) {
            const stype = this.parseType(ttype);
            
            this.expectTokenAndPop(TOKEN_LBRACE);
            vv = this.parseValue(stype.etype, breq);
            this.expectTokenAndPop(TOKEN_RBRACE);
        }
        else {
            if(this.testToken(TOKEN_ERR)) {    
                this.expectTokenAndPop(TOKEN_LPAREN);
                vv = this.parseValue(ttype.etype, breq);
                this.expectTokenAndPop(TOKEN_RPAREN);
            }
            else {
                const stype = this.parseType(ttype);
               
                this.expectTokenAndPop(TOKEN_LBRACE);
                vv = this.parseValue(stype.etype, breq);
                this.expectTokenAndPop(TOKEN_RBRACE);
            }
        }
    }
    else {
        vv = this.parseValue(ttype.oftype, breq);
    }

    return createBSQONParseResult(getBSQONParseValue(vv), ttype, [getBSQONParseInfoTTree(vv)], breq);
}
BSQONParse.prototype.parseResult = function (ttype, breq) {
    if(!this.isJSONMode()) {
        let vv = undefined;
        let sstype = $TypeInfo.unresolvedType;
        let ptree = undefined;
        if(this.testToken(TOKEN_OK)) {
            sstype = $TypeInfo.resolveTypeInAssembly(this.m_assembly, `Result<${ttype.ttype}, ${ttype.etype}>::Ok`);
            vv = this.parseOk(breq);
            ptree = getBSQONParseInfoTTree(vv);
        }
        else if(this.testToken(TOKEN_ERR)) {
            sstype = $TypeInfo.resolveTypeInAssembly(this.m_assembly, `Result<${ttype.ttype}, ${ttype.etype}>::Err`);
            vv = this.parseErr(breq);
            ptree = getBSQONParseInfoTTree(vv);
        }
        else {
            sstype = this.parseType(ttype);
            this.raiseErrorIf(!$Runtime.isTypeUniquelyResolvable(sstype), `Type ${sstype.ttag} is not unique type for parsing`);
            this.raiseErrorIf(stype.ttag !== `Result<${ttype.ttype}, ${ttype.etype}>::Ok` && stype.ttag !== `Result<${ttype.ttype}, ${ttype.etype}>::Err`, `Type ${sstype.ttag} is not a valid subtype of Result<T, E>`);

            this.expectTokenAndPop(TOKEN_LBRACE);
            vv = this.parseValue(sstype, breq);
            ptree = [getBSQONParseInfoTTree(vv)];
            this.expectTokenAndPop(TOKEN_RBRACE);
        }

        return createBSQONParseResult(new $Runtime.UnionValue(sstype, getBSQONParseValue(vv)), sstype, ptree, breq);
    }
    else {
        this.expectTokenAndPop(TOKEN_LBRACKET);
        const sstype = this.parseType(ttype);

        this.raiseErrorIf(!$Runtime.isTypeUniquelyResolvable(sstype), `Type ${sstype.ttag} is not unique type for parsing`);
        this.raiseErrorIf(stype.ttag !== `Result<${ttype.ttype}, ${ttype.etype}>::Ok` && stype.ttag !== `Result<${ttype.ttype}, ${ttype.etype}>::Err`, `Type ${sstype.ttag} is not a valid subtype of Result<T, E>`);

        const vv = this.parseValue(sstype, breq);
        this.expectTokenAndPop(TOKEN_RBRACKET);

        return createBSQONParseResult(new $Runtime.UnionValue(sstype, getBSQONParseValue(vv)), sstype, getBSQONParseInfoTTree(vv), breq);
    }
}
BSQONParse.prototype.parseMapEntry = function (ttype, breq) {
    if(!this.isJSONMode()) {
        const etype = this.parseType(ttype);
        this.raiseErrorIf(etype.ttag !== ttype.ttag, `Expected ${ttype.ttag} but got value of type ${etype.ttag}`);
 
        this.expectTokenAndPop(TOKEN_LBRACE);
        const k = this.parseValue(ttype.ktype, breq);
        this.expectTokenAndPop(TOKEN_COMMA);
        const v = this.parseValue(ttype.vtype, breq);
        this.expectTokenAndPop(TOKEN_RBRACE);

        return createBSQONParseResult([getBSQONParseValue(k), getBSQONParseValue(v)], ttype, [getBSQONParseInfoTTree(k), getBSQONParseInfoTTree(v)], breq);
    }
    else {
        this.expectTokenAndPop(TOKEN_LBRACKET);
        const k = this.parseValue(ttype.ktype, breq);
        this.expectTokenAndPop(TOKEN_COMMA);
        const v = this.parseValue(ttype.vtype, breq);
        this.expectTokenAndPop(TOKEN_RBRACKET);

        return createBSQONParseResult([getBSQONParseValue(k), getBSQONParseValue(v)], ttype, [getBSQONParseInfoTTree(k), getBSQONParseInfoTTree(v)], breq);
    }
}

BSQONParse.prototype.parseTuple = function (ttype, breq) {
    this.expectTokenAndPop(TOKEN_LBRACKET);

    let tvals = [];
    let ptree = [];
    if (this.testToken(TOKEN_RBRACKET)) {
        this.expectTokenAndPop(TOKEN_RBRACKET);

        this.raiseErrorIf(ttype.entries.length !== 0, `Expected ${ttype.entries.length} values but got []`);
        return createBSQONParseResult([], ttype, [], breq);
    }
    else {
        while (tvals.length === 0 || this.testToken(TOKEN_COMMA)) {
            if(this.testToken(TOKEN_COMMA)) {
                this.expectTokenAndPop(TOKEN_COMMA);
            }
            const entry = this.parseValue(ttype.entries[tvals.length], breq);

            tvals.push(getBSQONParseValue(entry));
            ptree.push(getBSQONParseInfoTTree(entry));
        }
        this.expectTokenAndPop(TOKEN_RBRACKET);
        
        this.raiseErrorIf(ttype.entries.length !== tvals.length, `Expected ${ttype.entries.length} values but got ${tvals.length}`);
        return createBSQONParseResult(tvals, ttype, ptree, breq);
    }
}
BSQONParse.prototype.parseRecord = function (ttype, breq) {
    this.expectTokenAndPop(TOKEN_LBRACE);

    let tvals = {};
    let ptree = {};
    if (this.testToken(TOKEN_RBRACE)) {
        this.expectTokenAndPop(TOKEN_RBRACE);

        this.raiseErrorIf(Object.keys(ttype.entries).length !== 0, `Expected ${Object.keys(ttype.entries).length} values but got {}`);
        return createBSQONParseResult({}, ttype, {}, breq);
    }
    else {
        while (tvals.length === 0 || this.testToken(TOKEN_COMMA)) {
            if(this.testToken(TOKEN_COMMA)) {
                this.expectTokenAndPop(TOKEN_COMMA);
            }
            const pname = this.expectTokenAndPop(TOKEN_PROPERTY).value;
            this.expectTokenAndPop(TOKEN_COLON);
            const entry = this.parseValue(ttype.entries[pname], breq);

            tvals[pname] = getBSQONParseValue(entry);
            ptree[pname] = getBSQONParseInfoTTree(entry);
        }
        this.expectTokenAndPop(TOKEN_RBRACE);

        this.raiseErrorIf(Object.keys(ttype.entries).length !== Object.keys(tvals).length, `Expected ${Object.keys(ttype.entries).length} values but got ${Object.keys(tvals).length}`);
        this.raiseErrorIf(Object.keys(ttype.entries).some((pname) => !(pname in tvals)), `Expected property ${Object.keys(ttype.entries).filter((pname) => !(pname in tvals)).join(", ")} but not provided`);
        return createBSQONParseResult(tvals, ttype, ptree, breq);
    }
}
BSQONParse.prototype.parseEnum = function (ttype, breq) {
    this.raiseErrorIf(!this.m_assembly.has(ttype.ttag), `Enum ${ttype.ttag} is not defined`);

    const etype = this.parseNominalType(ttype);
    this.expectTokenAndPop(TOKEN_COLON_COLON);
    const ename = this.expectTokenAndPop(TOKEN_PROPERTY).value;
    this.raiseErrorIf(!this.m_assembly.enumdecls.has(ttype.ttag).contains(ename), `Enum ${ttype.ttag} does not contain value ${ename}`);

    return createBSQONParseResult(`${etype.ttag}::${ename}`, ttype, undefined, breq);
}
BSQONParse.prototype.parseTypedecl = function (ttype, breq) {
    this.raiseErrorIf(!this.m_assembly.typedecls.has(ttype.ttag), `Typedecl ${ttype.ttag} is not defined`);

    const vv = this.parseValue(ttype.basetype, breq);
    this.expectTokenAndPop(TOKEN_UNDER);
    this.parseNominalType(ttype);

    this.m_typedeclChecks.push({decltype: ttype, value: getBSQONParseValue(vv)});

    return createBSQONParseResult(getBSQONParseValue(vv), ttype, [getBSQONParseInfoTTree(vv)], breq);
}
BSQONParse.prototype.parseStdEntity = function (ttype, breq) {
    this.raiseErrorIf(!this.m_assembly.simpledecls.has(ttype.ttag), `Entity ${ttype.ttag} is not defined`);

    const etype = this.parseNominalType(ttype);
    this.expectTokenAndPop(TOKEN_LBRACE);

    let tvals = {};
    let ptree = {};
    if(this.testToken(TOKEN_RBRACE)) {
        this.expectTokenAndPop(TOKEN_RBRACE);
        
        this.raiseErrorIf(Object.keys(ttype.entries).length !== 0, `Expected ${Object.keys(ttype.entries).length} values but got {}`);
        return createBSQONParseResult({}, ttype, {}, breq);
    }
    else {
        const edecl = this.m_assembly.simpledecls.get(ttype.ttag);
        const fnames = Object.keys(edecl.fields);

        while (tvals.length === 0 || this.testToken(TOKEN_COMMA)) {
            if(this.testToken(TOKEN_COMMA)) {
                this.expectTokenAndPop(TOKEN_COMMA);
            }
            const fname = fnames[tvals.length];
            const entry = this.parseValue(edecl.fields[fname], breq);

            tvals[fname] = getBSQONParseValue(entry);
            ptree[fname] = getBSQONParseInfoTTree(entry);
        }
        this.expectTokenAndPop(TOKEN_RBRACE);

        this.raiseErrorIf(Object.keys(ttype.entries).length !== Object.keys(tvals).length, `Expected ${Object.keys(ttype.entries).length} values but got ${Object.keys(tvals).length}`);
        this.raiseErrorIf(Object.keys(ttype.entries).some((pname) => !(pname in tvals)), `Expected field ${Object.keys(ttype.entries).filter((pname) => !(pname in tvals)).join(", ")} but not provided`);
        return createBSQONParseResult(tvals, ttype, ptree, breq);
    }
}
BSQONParse.prototype.parseList = function (ttype, breq) {
}
BSQONParse.prototype.parseStack = function (ttype, breq) {
}
BSQONParse.prototype.parseQueue = function (ttype, breq) {
}
BSQONParse.prototype.parseSet = function (ttype, breq) {
}
BSQONParse.prototype.parseMap = function (ttype, breq) {
}


BSQONParse.prototype.parseConcept = function (ttype, breq) {
}
BSQONParse.prototype.parseConceptSet = function (ttype, breq) {
}
BSQONParse.prototype.parseUnion = function (ttype, breq) {
}

BSQONParse.prototype.parseValue = function (ttype, breq) {
}

function BSQONEmit(mode) {
    this.m_emitmode = mode ?? NOTATION_MODE_DEFAULT;
}
BSQONEmit.prototype.isDefaultMode = function () {
    return this.m_emitmode === NOTATION_MODE_DEFAULT;
}
BSQONEmit.prototype.isJSONMode = function () {
    return this.m_emitmode === NOTATION_MODE_JSON;
}
BSQONEmit.prototype.isFullMode = function () {
    return this.m_emitmode === NOTATION_MODE_FULL;
}
BSQONEmit.prototype.emitNone = function() {

}

export {
    NotationMode,
    BSQONParse, BSQONParseError,
    BSQONEmit
}
