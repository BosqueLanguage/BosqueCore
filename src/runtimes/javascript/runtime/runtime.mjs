"use strict";

import { JS, NFA, Words } from "refa";
import {Decimal} from "decimal.js";
import Fraction from "fraction.js";

import { List as IList, Map as IMap } from "immutable";

function Unwind(kind, msg) {
    this.kind = kind;
    this.msg = msg;
}

function raiseRuntimeError(msg) {
    throw new Unwind("error", msg);
}

function raiseRuntimeErrorIf(cond, msg) {
    if(cond) {
        throw new Unwind("error", msg);
    }
}

function raiseUserAssert(msg) {
    throw new Unwind("assert", msg);
}

function raiseUserAssertIf(cond, msg) {
    if(cond) {
        throw new Unwind("assert", msg);
    }
}

function safeMath(val, lb, ub) {
    raiseRuntimeErrorIf(val < lb || ub < val, `bounded arithmetic op overflowed`);
    return val;
}

function safeMathUnderflow(val, zero) {
    raiseRuntimeErrorIf(val < zero, `arithmetic op underflow`);
    return val;
}

function safeMathDiv(op, chk, v1, v2) {
    raiseRuntimeErrorIf(chk(v2), `division by 0`);
    return op(v1, v2);
}

function hashvals(...vals) {
    let h = 0;
    const len = vals.length;
    for(let i = 0; i < len; ++i) {
        return h ^ (vals[i] << 11);
    }

    return h;
}

function hashstr(str) {
    let h = 0;
    const len = str.length;
    for(let i = 0; i < len; ++i) {
        return h ^ (str[i] << 11);
    }

    return h;
}

function lesslexo(vals1, vals2) {
    if(vals1.length !== vals2.length) {
        return vals1.length < vals2.length;
    }
    else {
        const len = vals1.length;
        for (let i = 0; i < len; ++i) {
            if(vals1[i] !== vals2[i]) {
                return vals1[i] < vals2[i];
            }
        }

        return false; //same
    }
}

function BSQDateTime(year, month, day, hour, minute, second, millisecond, tz) {
    this.year = year;
    this.month = month;
    this.day = day;
    this.hour = hour;
    this.minute = minute;
    this.second = second;
    this.millisecond = millisecond;
    this.tz = tz;
}
BSQDateTime.create = function(year, month, day, hour, minute, second, millisecond, tz) {
    return Object.freeze(new BSQDateTime(year, month, day, hour, minute, second, millisecond, tz));
}
BSQDateTime.prototype.equalsBase = function (other) {
    return this.year === other.year && this.month === other.month && this.day === other.day && this.hour === other.hour && this.minute === other.minute && this.second === other.second && this.millisecond === other.millisecond && this.tz === other.tz;
}
BSQDateTime.prototype.hashcodeBase = function () {
    return hashvals(this.year, this.month, this.day, this.hour, this.minute, this.second, this.millisecond, this.tz.length);
}
BSQDateTime.prototype.lessBase = function (other) {
    return lesslexo([this.year, this.month, this.day, this.hour, this.minute, this.second, this.millisecond, this.tz], [other.year, other.month, other.day, other.hour, other.minute, other.second, other.millisecond, other.tz]);
}

function BSQDate(year, month, day) {
    this.year = year;
    this.month = month;
    this.day = day;
}
BSQDate.create = function(year, month, day) {
    return Object.freeze(new BSQDate(year, month, day));
}
BSQDate.prototype.equalsBase = function (other) {
    return this.year === other.year && this.month === other.month && this.day === other.day;
}
BSQDate.prototype.hashcodeBase = function () {
    return hashvals(this.year, this.month, this.day);
}
BSQDate.prototype.lessBase = function (other) {
    return lesslexo([this.year, this.month, this.day], [other.year, other.month, other.day]);
}

function BSQTime(hour, minute, second, millisecond) {
    this.hour = hour;
    this.minute = minute;
    this.second = second;
    this.millisecond = millisecond;
}
BSQTime.create = function(year, month, day, hour, minute, second, millisecond, tz) {
    return Object.freeze(new BSQTime(hour, minute, second, millisecond, tz));
}
BSQTime.prototype.equalsBase = function (other) {
    return this.hour === other.hour && this.minute === other.minute && this.second === other.second && this.millisecond === other.millisecond;
}
BSQTime.prototype.hashcodeBase = function () {
    return hashvals(this.hour, this.minute, this.second, this.millisecond);
}
BSQTime.prototype.lessBase = function (other) {
    return lesslexo([this.hour, this.minute, this.second, this.millisecond], [other.hour, other.minute, other.second, other.millisecond]);
}

function BSQLatLongCoordinate(lat, long) {
    this.lat = lat;
    this.long = long;
}
BSQLatLongCoordinate.create = function(lat, long) {
    return Object.freeze(new BSQLatLongCoordinate(lat, long));
}

function BSQMapEntry(k, v) {
    this.k = k;
    this.v = v;
}
BSQMapEntry.create = function(k, v) {
    return Object.freeze(new BSQMapEntry(k, v));
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
//LatLongCoordinate -> BSQLatLongCoordinate
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
//MapEntry<K, V> -> BSQMapEntry
//Map<K, V> -> IMap<K, V>


function keyEqualsBase(v1, v2) {
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

function hashcodeBase(v) {
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
            return hashvals(BigInt.asUintN(31, v), 29);
        }
        else if(ttype === "string") {
            return hashvals(hashstr(v), 79);
        }
        else {
            return hashvals(v.hashcodeBase(), 111);
        }
    }
}

function keyLessBase(v1, v2) {
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

function UnionValue(tkey, value) {
    this.tkey = tkey;
    this.value = value;
}
UnionValue.prototype.hashCode = function () {
    return hashvals(hashstr(this.tkey), this.value);
}
UnionValue.prototype.equals = function (other) {
    return this.tkey === other.tkey && keyEqualsBase(this.value, other.value);
}
UnionValue.prototype.less = function (other) {
    if(this.tkey !== other.tkey) {
        return this.tkey < other.tkey;
    }
    else {
        keyEqualsBase(this.value, other.value);
    }
}
UnionValue.create = function(tkey, value) {
    return Object.freeze(new UnionValue(tkey, value));
}

export {
    BSQDateTime, BSQDate, BSQTime, BSQLatLongCoordinate, BSQMapEntry,
    keyEqualsBase, hashcodeBase, keyLessBase, 
    UnionValue,
    keyEqualsBase, keyLessBase,
    Unwind, raiseRuntimeError, raiseRuntimeErrorIf, raiseUserAssert, raiseUserAssertIf,
    safeMath, safeMathDiv, safeMathUnderflow
};
