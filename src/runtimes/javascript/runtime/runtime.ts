import { BSQTypeKey } from "./typeinfo";

import { JS, NFA, Words } from "refa";
import {Decimal} from "decimal.js";
import Fraction from "fraction.js";

import { List as IList, Map as IMap } from "immutable";

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
//LatLongCoordinate -> [lat, long]
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

export {
    BSQError, raiseRuntimeError, raiseRuntimeErrorIf, raiseUserAssert, raiseUserAssertIf,

    BSQDateTime, BSQDate, BSQTime,
    keyEqualsBase, hashcodeBase, keyLessBase, 
    UnionValue,
    acceptsString,
    safeMath, safeMathDiv, safeMathUnderflow, 
    keyEqualStrict, keyEqualMixed, keyEqualUnion, keyLessStrict, keyLessUnion
};
