type BSQTypeKey = string;

import { JS, NFA, Words } from "npm:refa@0.10.0";
import {Decimal} from "npm:decimal.js@10.4.3";
import Fraction from "npm:fraction.js@4.2.0";

import { List as IList, Map as IMap } from "npm:immutable@4.3.0";

enum NotationMode {
    NOTATION_MODE_BSQON = "BSQ_OBJ_NOTATION_DEFAULT",
    NOTATION_MODE_JSON = "BSQ_OBJ_NOTATION_JSON"
}

function bsqonEscapeString(str: string): string {
    let ret = "";
    for (let i = 0; i < str.length; i++) {
        if (str[i] === "%") {
            ret += "%$;";
        }
        else if(str[i] === "\"") {
            ret += "%;";
        }
        else if(str[i] === "`") {
            ret += "%backtick;";
        }
        else {
            ret += str[i];
        }
    }

    return ret;
}

function bsqonUnescapeString(str: string): string {
    let ret = "";
    for (let i = 0; i < str.length; i++) {
        if (str[i] === "%") {
            i++;
            const epos = str.indexOf(";", i);

            if (str[i] === "%") {
                ret += "%";
            }
            else if (str[i] === "n") {
                ret += "\n";
            }
            else if (str[i] === "r") {
                ret += "\r";
            }
            else if (str[i] === "t") {
                ret += "\t";
            }
            else if (str[i] === "b") {
                ret += "`";
            }
            else if (str[i] === ";") {
                ret += "\"";
            }
            else {
                const hex = str.substring(i, epos);
                ret += String.fromCharCode(parseInt(hex, 16));
            }

            i = epos;
        }
        else {
            ret += str[i];
        }
    }

    return ret;
}

enum BSQErrorKind {
    Runtime,
    UserAssert
}

class BSQError extends Error {
    readonly ekind: BSQErrorKind;
    readonly msg: string;

    constructor(ekind: BSQErrorKind, message: string) {
        super(`Error -- ${message}`);
        Object.setPrototypeOf(this, new.target.prototype);

        this.ekind = ekind;
        this.msg = message;
    }
}

function raiseRuntimeError(msg: string) {
    throw new BSQError(BSQErrorKind.Runtime, msg);
}

function raiseRuntimeErrorIf(cond: boolean, msg: string) {
    if(cond) {
        throw new BSQError(BSQErrorKind.Runtime, msg);
    }
}

function raiseUserAssert(msg: string) {
    throw new BSQError(BSQErrorKind.UserAssert, msg);
}

function raiseUserAssertIf(cond: boolean, msg: string) {
    if(cond) {
        throw new BSQError(BSQErrorKind.UserAssert, msg);
    }
}

function acceptsString(re: string, str: string): boolean {
    const jsre = RegExp(re);

    const { expression, maxCharacter } = JS.Parser.fromLiteral(jsre).parse();
    const nfa = NFA.fromRegex(expression, { maxCharacter });

    return nfa.test(Words.fromStringToUnicode(str));
}

function safeMath<T>(val: T, lb: T, ub: T): T {
    raiseRuntimeErrorIf(val < lb || ub < val, `bounded arithmetic op overflowed`);
    return val;
}

function safeMathUnderflow<T>(val: T, zero: T): T {
    raiseRuntimeErrorIf(val < zero, `arithmetic op underflow`);
    return val;
}

function safeMathDiv<T>(op: (x: T, y: T) => T, chk: (x: T) => boolean, v1: T, v2: T): T {
    raiseRuntimeErrorIf(chk(v2), `division by 0`);
    return op(v1, v2);
}

function hashvals(...vals: number[]): number {
    let h = 0;
    const len = vals.length;
    for(let i = 0; i < len; ++i) {
        return h ^ (vals[i] << 11);
    }

    return h;
}

function hashstr(str: string): number {
    let h = 0;
    const len = str.length;
    for(let i = 0; i < len; ++i) {
        return h ^ (str.charCodeAt(i) << 11);
    }

    return h;
}

function lesslexo(vals1: number[], vals2: number[]): number {
    if(vals1.length !== vals2.length) {
        return vals1.length < vals2.length ? -1 : 1;
    }
    else {
        const len = vals1.length;
        for (let i = 0; i < len; ++i) {
            if(vals1[i] !== vals2[i]) {
                return vals1[i] < vals2[i] ? -1 : 1;
            }
        }

        return 0; //same
    }
}

class BSQDateTime {
    readonly year: number;
    readonly month: number;
    readonly day: number;
    readonly hour: number;
    readonly minute: number;
    readonly second: number;
    readonly millisecond: number;
    readonly tz: string;

    constructor(year: number, month: number, day: number, hour: number, minute: number, second: number, millisecond: number, tz: string) {
        this.year = year;
        this.month = month;
        this.day = day;
        this.hour = hour;
        this.minute = minute;
        this.second = second;
        this.millisecond = millisecond;
        this.tz = tz;
    }

    equalsBase(other: BSQDateTime): boolean {
        return this.year === other.year && this.month === other.month && this.day === other.day && this.hour === other.hour && this.minute === other.minute && this.second === other.second && this.millisecond === other.millisecond && this.tz === other.tz;
    }

    hashcodeBase(): number {
        return hashvals(this.year, this.month, this.day, this.hour, this.minute, this.second, this.millisecond, this.tz.length);
    }

    lessBase(other: BSQDateTime): boolean {
        const llo = lesslexo([this.year, this.month, this.day, this.hour, this.minute, this.second, this.millisecond], [other.year, other.month, other.day, other.hour, other.minute, other.second, other.millisecond]);
        return llo !== 0 ? llo < 0 : this.tz < other.tz;
    }

    hashcode(): number {
        return this.hashcodeBase();
    }

    equals(other: any): boolean {
        return this.equalsBase(other);
    }
}

class BSQDate{
    readonly year: number;
    readonly month: number;
    readonly day: number;

    constructor(year: number, month: number, day: number) {
        this.year = year;
        this.month = month;
        this.day = day;
    }

    equalsBase(other: BSQDate): boolean {
        return this.year === other.year && this.month === other.month && this.day === other.day;
    }

    hashcodeBase(): number {
        return hashvals(this.year, this.month, this.day);
    }

    lessBase(other: BSQDate): boolean {
        return lesslexo([this.year, this.month, this.day], [other.year, other.month, other.day]) < 0;
    }

    hashcode(): number {
        return this.hashcodeBase();
    }

    equals(other: any): boolean {
        return this.equalsBase(other);
    }
}

class BSQTime {
    readonly hour: number;
    readonly minute: number;
    readonly second: number;
    readonly millisecond: number;

    constructor(hour: number, minute: number, second: number, millisecond: number) {
        this.hour = hour;
        this.minute = minute;
        this.second = second;
        this.millisecond = millisecond;
    }

    equalsBase(other: BSQTime): boolean {
        return this.hour === other.hour && this.minute === other.minute && this.second === other.second && this.millisecond === other.millisecond;
    }

    hashcodeBase(): number {
        return hashvals(this.hour, this.minute, this.second, this.millisecond);
    }

    lessBase(other: BSQTime): boolean {
        return lesslexo([this.hour, this.minute, this.second, this.millisecond], [other.hour, other.minute, other.second, other.millisecond]) < 0;
    }

    hashcode(): number {
        return this.hashcodeBase();
    }

    equals(other: any): boolean {
        return this.equalsBase(other);
    }
}

class UnionValue {
    readonly tkey: BSQTypeKey;
    readonly value: any;

    constructor(tkey: BSQTypeKey, value: any) {
        this.tkey = tkey;
        this.value = value;
    }

    hashCode(): number {
        return hashvals(hashstr(this.tkey), hashcodeBase(this.value));
    }

    equals(other: any): boolean {
        return this.tkey === other.tkey && keyEqualsBase(this.value, other.value);
    }
}

//None -> null
//Nothing -> undefined
//Bool -> boolean
//Int -> number
//Nat -> number
//BigInt -> bigint
//BigNat -> bigint
//Rational -> Fraction
//Float -> number
//Decimal -> Decimal
//String -> string
//AsciiString -> string
//ByteBuffer -> Buffer
//DateTime -> BSQDateTime
//UTCDateTime -> BSQDateTime
//PlainDate -> BSQDate
//PlainTime -> BSQTime
//TickTime -> bigint
//LogicalTime -> bigint
//ISOTimeStamp -> BSQTime
//UUIDv4 -> string
//UUIDv7 -> string
//SHAContentHash -> string
//Regex -> string

//StringOf -> string
//AsciiStringOf -> string
//Something<T> -> T
//Option<T> -> UnionValue(T)
//Ok<T> -> T
//Err<E> -> E
//Result<T, E> -> UnionValue(T | E)

//List<T> -> IList<T>
//Stack<T> -> IStack<T>
//Queue<T> -> IQueue<T>
//Set<T> -> ISet<T>
//MapEntry<K, V> -> [K, V]
//Map<K, V> -> IMap<K, V>

function keyEqualsBase(v1: any, v2: any): boolean {
    if (v1 === v2) {
        return true;
    }
    else {
        const type1 = typeof v1;
        if(type1 !== "object") {
            return false;
        }
        else {
            return v1.equalsBase(v2);
        }
    }
}

function hashcodeBase(v: any): number {
    if(v === null) {
        return 0;
    }
    else if(v === true) {
        return 1;
    }
    else if(v === false) {
        return 2;
    }
    else {
        const ttype = typeof v;
        if(ttype === "number") {
            return hashvals(v, 23);
        }
        else if(ttype === "bigint") {
            return hashvals(Number(v), 29);
        }
        else if(ttype === "string") {
            return hashvals(hashstr(v), 79);
        }
        else {
            return hashvals(v.hashcodeBase(), 111);
        }
    }
}

function keyLessBase(v1: any, v2: any): boolean {
    if (v1 === v2) {
        return false;
    }
    else {
        if(v1 === true) {
            return false;
        }
        else if(v1 === false) {
            return v2 === true;
        }
        else {
            const type1 = typeof v1;
            if(type1 !== "object") {
                return v1 < v2;
            }
            else {
                return v1.lessBase(v2);
            }
        }
    }
}

function keyEqualStrict(lval: any, rval: any): boolean {
    return keyEqualsBase(lval, rval);
}

function keyEqualMixed(uval: any, gval: UnionValue, oftype: BSQTypeKey): boolean {
    if(gval.tkey !== oftype) {
        return false;
    }

    return keyEqualsBase(uval, gval.value);
}

function keyEqualUnion(lval: UnionValue, rval: UnionValue): boolean {
    if(lval.tkey !== rval.tkey) {
        return false;
    }

    return keyEqualsBase(lval.value, rval.value);
}

function keyLessStrict(lval: any, rval: any): boolean {
    return keyLessBase(lval, rval);
}

function keyLessUnion(lval: any, rval: any): boolean {
    if(lval.tkey !== rval.tkey) {
        return lval.tkey < rval.tkey;
    }

    return keyLessBase(lval.value, rval.value);
}

class BSQEnvironment {
    readonly parent: BSQEnvironment;
    readonly args: Map<string, any>;
    
    constructor(env: BSQEnvironment, ...args: [string, any][]) {
        this.parent = env;
        this.args = new Map<string, any>();

        for (let i = 0; i < args.length; ++i) {
            this.args.set(args[i][0], args[i][1]);
        }
    }

    pushEmpty() {
        return new BSQEnvironment(this);
    }

    pop() {
        return this.parent;
    }

    has(key: string): boolean {
        if (this.args.has(key)) {
            const vv = this.args.get(key);
            return vv !== undefined;
        }

        return this.parent !== undefined && this.parent.has(key);
    }

    get(key: string, oftype: BSQTypeKey): any {
        if (this.args.has(key)) {
            const vv = this.args.get(key);
            raiseRuntimeErrorIf(vv === undefined, `key ${key} was not found in environment`);

            raiseRuntimeErrorIf(vv.tkey === oftype, `expected value of type ${oftype} but got ${vv.tkey}`);
            return vv.value;
        }

        raiseRuntimeErrorIf(this.parent === undefined, `key ${key} was not found in environment`);
        return this.get(key, oftype);
    }

    getOrNoneUV(key: string, oftype: BSQTypeKey): UnionValue {
        if (this.args.has(key)) {
            const vv = this.args.get(key);
            if (vv === undefined) {
                return new UnionValue("None", undefined);
            }

            raiseRuntimeErrorIf(vv.tkey === oftype, `expected value of type ${oftype} but got ${vv.tkey}`);
            return new UnionValue(vv.tkey, vv.value);
        }

        if (this.parent === undefined) {
            return new UnionValue("None", undefined);
        }
        else {
            return this.parent.getOrNoneUV(key, oftype);
        }
    }

    getOrNoneDV(key: string, oftype: BSQTypeKey): any {
        if (this.args.has(key)) {
            const vv = this.args.get(key);
            if (vv === undefined) {
                return undefined;
            }

            raiseRuntimeErrorIf(vv.tkey === oftype, `expected value of type ${oftype} but got ${vv.tkey}`);
            return vv.value;
        }

        if (this.parent === undefined) {
            return undefined;
        }
        else {
            return this.parent.getOrNoneDV(key, oftype);
        }
    }

    set(key: string, val: any, oftype: BSQTypeKey) {
        this.args.set(key, { tkey: oftype, value: val });
    }

    clear(key: string): any {
        raiseRuntimeErrorIf(!this.has(key), `key ${key} not defined in environment`);
        this.args.set(key, undefined);
    }
}

class NumericOps {
}

class StringOps {
}

class DateOps {
}

class ListOps {
    static create(...args: any[]): IList<any> {
        return IList(args);
    }
}

class MapOps {
    static create(...args: [any, any][]): IMap<any, any> {
        const minit = IMap<any, any>();
        const mres = minit.withMutations(map => {
            for (let i = 0; i < args.length; ++i) {
                if (map.has(args[i][0])) {
                    raiseRuntimeError("Duplicate keys in Map construction");
                }

                map = map.set(args[i][0], args[i][1]);
            }
        });

        return mres;
    }
}

const loglevels = ["fatal", "error", "warn", "info", "debug"];
let loglevel = "info";
let logprefix: {fmt: string, args: any[], smsg: string}[] = [];

function setloglevel(level: "fatal" | "error" | "warn" | "info" | "debug") {
    loglevel = level;
}

function checkloglevel(level: "fatal" | "error" | "warn" | "info" | "debug") {
    return loglevels.indexOf(level) <= loglevels.indexOf(loglevel);
}

function log(level: "fatal" | "error" | "warn" | "info" | "debug", tag: string, fmt: string, ...args: any[]) {
    const msg = fmt + " -- " + args.map((arg) => JSON.stringify(arg)).join(" ");
    if(logprefix.length === 0) {
        console.log(JSON.stringify(
            {
                tag: tag,
                msg: msg
            }
        ));
    }
    else {
        console.log(JSON.stringify(
            {
                tag: tag,
                prefix: logprefix.map((pp) => pp.smsg),
                msg: msg
            }
        ));
    }

    if(level === "fatal") {
        raiseUserAssert("log at fatal level -- " + msg);
    }
}

function pushlogprefix(fmt: string, ...args: any[]) {
    const smsg = fmt + " -- " + args.map((arg) => JSON.stringify(arg)).join(" ");
    logprefix.push({fmt: fmt, args: args, smsg: smsg});
}

function poplogprefix() {
    logprefix.pop();
}

const vtablemap = new Map();

const invmap = new Map();
const lambdas = new Map();
const validators = new Map();

const $ASM: {[k: string]: any} = {};

function setScratchValue(scratch: any[], sidx: number, value: any): number {
    scratch[sidx] = value;
    return 0;
}

export {
    Decimal, Fraction, IList, IMap,

    NotationMode, bsqonEscapeString, bsqonUnescapeString,
    BSQError, raiseRuntimeError, raiseRuntimeErrorIf, raiseUserAssert, raiseUserAssertIf,
    BSQDateTime, BSQDate, BSQTime,
    keyEqualsBase, hashcodeBase, keyLessBase, 
    UnionValue,
    acceptsString,
    safeMath, safeMathDiv, safeMathUnderflow, 
    keyEqualStrict, keyEqualMixed, keyEqualUnion, keyLessStrict, keyLessUnion,

    BSQEnvironment,
    NumericOps, StringOps, DateOps, ListOps, MapOps,

    $ASM,
    vtablemap, invmap, lambdas, validators, setScratchValue,
    setloglevel, checkloglevel, log, pushlogprefix, poplogprefix
};
