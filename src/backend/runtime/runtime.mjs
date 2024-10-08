"use strict;"

import { accepts } from "@bosque/jsbrex";

/**
 * @constant
 * @type {string[]}
 **/
let _$softfails = [];

/**
 * @constant
 * @type {bigint}
 **/
const MIN_SAFE_INT = -9223372036854775807n;

/**
 * @constant
 * @type {bigint}
 **/
const MAX_SAFE_INT = 9223372036854775807n;

/**
 * @constant
 * @type {bigint}
 **/
const MAX_SAFE_NAT = 9223372036854775807n;

/**
 * @constant
 * @type {Symbol}
 **/
const $Unwind_NumericRange = Symbol("NumericRangeFailed");

/**
 * @constant
 * @type {Symbol}
 **/
const $Unwind_DivZero = Symbol("DivZeroFailed");

/**
 * @constant
 * @type {Symbol}
 **/
const $Unwind_BadRegex = Symbol("BadRegexFailed");

/**
 * @constant
 * @type {Symbol}
 **/
const $Unwind_Assert = Symbol("AssertFailed");

/**
 * @constant
 * @type {Symbol}
 **/
const $Unwind_PreCond = Symbol("PreCondFailed");

/**
 * @constant
 * @type {Symbol}
 **/
const $Unwind_PostCond = Symbol("PostCondFailed");

/**
 * @constant
 * @type {Symbol}
 **/
const $Unwind_Format = Symbol("FormatFailed");

/**
 * @constant
 * @type {Symbol}
 **/
const $Unwind_Invariant = Symbol("InvariantFailed");

/**
 * @constant
 * @type {Symbol}
 **/
const $Unwind_Validate = Symbol("ValidateFailed");

/**
 * @constant
 * @type {Symbol}
 **/
const $Unwind_TypeAs = Symbol("TypeAsFailed");


/**
 * @constant
 * @type {Symbol}
 **/
const $Unwind_NonExhaustive = Symbol("ExhaustiveFailed");

/**
 * @constructor
 * @param {Symbol} tag
 * @param {string | undefined} info
 **/
function $Unwind(tag, info) {
    this.$tag = tag;
    this.$info = info;
}

/**
 * @constant
 * @type {object}
 */
let _$supertypes = {};

/**
 * @constructor
 * @param {Symbol} t 
 * @param {any} v 
 **/
function $Boxed(t, v) {
    this.$tag = t;
    this.$val = v;
}

/**
 * @constant
 * @type {Symbol}
 **/
const $SymbolNone = Symbol.for("None");

/**
 * @constant
 * @type {$Boxed}
 **/
const _$BoxedNone = new $Boxed(Symbol.for("None"), null);

/**
 * @function
 * @param {any} v1
 * @param {any} v2
 * @returns {boolean}
 **/
function _$feqraw(v1, v2) {
    return v1 === v2;
}

/**
 * @function
 * @param {any} v1
 * @param {any} v2
 * @returns {boolean}
 **/
function _$fneqraw(v1, v2) {
    return v1 !== v2;
}

/**
 * @function
 * @param {any} v1
 * @param {any} v2
 * @returns {boolean}
 **/
function _$flessraw(v1, v2) {
    return v1 < v2;
}

/**
 * @method
 * @param {any} v
 * @returns {boolean}
 **/
$Boxed.prototype._$keyEqOf = function(v) {
    return _$feqraw(this.$val, v);
};

/**
 * @method
 * @param {any} v
 * @returns {boolean}
 **/
$Boxed.prototype._$keyNeqOf = function(v) {
    return !_$feqraw(this.$val, v);
};

/**
 * @method
 * @returns {boolean}
 **/
$Boxed.prototype._$isNone = function() {
    return this.$tag === $SymbolNone;
};

/**
 * @method
 * @returns {boolean}
 **/
$Boxed.prototype._$isNotNone = function() {
    return this.$tag !== $SymbolNone;
};

/**
 * @method
 * @returns {boolean}
 **/
$Boxed.prototype._$isSome = function() {
    return this.$tag !== $SymbolNone;
};

/**
 * @method
 * @param {Symbol} tsym
 * @returns {boolean}
 **/
$Boxed.prototype._$is = function(tsym) {
    return this.$tag === tsym;
};

/**
 * @method
 * @param {Symbol} tsym
 * @returns {boolean}
 **/
$Boxed.prototype._$isNot = function(tsym) {
    return this.$tag !== tsym;
};

/**
 * @method
 * @param {Symbol} tsym
 * @returns {boolean}
 **/
$Boxed.prototype._$isSubtype = function(tsym) {
    return _$supertypes.get(this.$tag).has(tsym);
};

/**
 * @method
 * @param {Symbol} tsym
 * @returns {boolean}
 **/
$Boxed.prototype._$isNotSubtype = function(tsym) {
    return !_$supertypes.get(this.$tag).has(tsym);
};

/**
 * @function
 * @param {Symbol} tag 
 * @param {Symbol} tsym 
 * @returns {boolean}
 */
function _$fisSubtype(tag, tsym) {
    return _$supertypes.get(tag).has(tsym);
}

/**
 * @function
 * @param {Symbol} tag 
 * @param {Symbol} tsym 
 * @returns {boolean}
 */
function _$fisNotSubtype(tag, tsym) {
    return !_$supertypes.get(tag).has(tsym);
}

/**
 * @method
 * @param {string | undefined} info
 * @returns {any}
 * @throws {$Unwind}
 **/
$Boxed.prototype._$asNone = function(info) {
    if (this._$isNone()) {
        return null;
    }
    else {
        throw new $Unwind($Unwind_TypeAs, info);
    }
};

/**
 * @method
 * @param {string | undefined} info
 * @returns {any}
 * @throws {$Unwind}
 **/
$Boxed.prototype._$asSome = function(info) {
    if (this._$isSome()) {
        return this.$val;
    }
    else {
        throw new $Unwind($Unwind_TypeAs, info);
    }
};

/**
 * @method
 * @param {Symbol} tsym
 * @param {boolean} ubx
 * @param {string | undefined} info
 * @returns {any}
 * @throws {$Unwind}
 **/
$Boxed.prototype._$as = function(tsym, ubx, info) {
    if (this._$is(tsym)) {
        return ubx ? this.$val : this;
    } else {
        throw new $Unwind($Unwind_TypeAs, info);
    }
};

/**
 * @method
 * @param {Symbol} tsym
 * @param {boolean} ubx
 * @param {string | undefined} info
 * @returns {any}
 * @throws {$Unwind}
 **/
$Boxed.prototype._$asNot = function(tsym, ubx, info) {
    if (this._$isNot(tsym)) {
        return ubx ? this.$val : this;
    } else {
        throw new $Unwind($Unwind_TypeAs, info);
    }
};

/**
 * @method
 * @param {Symbol} tsym
 * @param {boolean} ubx
 * @param {string | undefined} info
 * @returns {any}
 * @throws {$Unwind}
 **/
$Boxed.prototype._$asSubtype = function(tsym, ubx, info) {
    if (this._$isSubtype(tsym)) {
        return ubx ? this.$val : this;
    } else {
        throw new $Unwind($Unwind_TypeAs, info);
    }
};

/**
 * @method
 * @param {Symbol} tsym
 * @param {boolean} ubx
 * @param {string | undefined} info
 * @returns {any}
 * @throws {$Unwind}
 **/
$Boxed.prototype._$asNotSubtype = function(tsym, ubx, info) {
    if (this._$isNotSubtype(tsym)) {
        return ubx ? this.$val : this;
    } else {
        throw new $Unwind($Unwind_TypeAs, info);
    }
};

/**
 * @function
 * @param {any} val
 * @param {Symbol} tag
 * @param {Symbol} tsym
 * @param {boolean} ubx
 * @param {string | undefined} info
 * @returns {any}
 * @throws {$Unwind}
 **/
function _$fasSubtype(val, tag, tsym, ubx, info) {
    if (_$fisSubtype(tag, tsym)) {
        return ubx ? val : _$b(tag, val);
    } else {
        throw new $Unwind($Unwind_TypeAs, info);
    }
};

/**
 * @function
 * @param {any} val
 * @param {Symbol} tag
 * @param {Symbol} tsym
 * @param {boolean} ubx
 * @param {string | undefined} info
 * @returns {any}
 * @throws {$Unwind}
 **/
function _$fasNotSubtype(val, tag, tsym, ubx, info) {
    if (_$fisNotSubtype(tag, tsym)) {
        return ubx ? val : _$b(tag, val);
    } else {
        throw new $Unwind($Unwind_TypeAs, info);
    }
};

/**
 * @function
 * @param {Symbol} tsym
 * @returns {any}
 * @returns {$Boxed}
 **/ 
function _$b(t, v) {
    return v !== null ? new $Boxed(t, v) : _$BoxedNone;
}

/**
 * @function
 * @param {bigint} v
 * @param {string | undefined} info
 * @returns {bigint}
 * @throws {$Unwind}
 **/
function _$rc_i(v, info) {
    if (v < MIN_SAFE_INT || MAX_SAFE_INT < v) {
        throw new $Unwind($Unwind_NumericRange, info);
    }

    return v;
}

/**
 * @function
 * @param {bigint} v
 * @param {string|undefined} info
 * @returns {bigint}
 * @throws {$Unwind}
 **/
function _$rc_n(v, info) {
    if (v < 0n || MAX_SAFE_NAT < v) {
        throw new $Unwind($Unwind_NumericRange, info);
    }

    return v;
}

/**
 * @function
 * @param {bigint} v
 * @param {string | undefined} info
 * @returns {bigint}
 * @throws {$Unwind}
 **/
function _$rc_N(v, info) {
    if (v < 0n) {
        throw new $Unwind($Unwind_NumericRange, info);
    }

    return v;
}

/**
 * @function
 * @param {number} v
 * @param {string | undefined} info
 * @returns {number}
 * @throws {$Unwind}
 **/
function _$rc_f(v, info) {
    if (Number.isNaN(v)) {
        throw new $Unwind($Unwind_NumericRange, info.replace("[EVALUE]", "NaN"));
    }

    if (!Number.isFinite(v)) {
        throw new $Unwind($Unwind_NumericRange, info.replace("[EVALUE]", "Infinite"));
    }

    return v;
}

/**
 * @function
 * @param {bigint} v
 * @param {bigint} d
 * @param {string | undefined} infod
 * @returns {bigint}
 * @throws {$Unwind}
 **/
function _$dc_i(v, d, infod) {
    if (d === 0n) {
        throw new $Unwind($Unwind_DivZero, infod);
    }

    return v / d;
}

/**
 * @function
 * @param {bigint} v
 * @param {bigint} d
 * @param {string | undefined} infod
 * @returns {bigint}
 * @throws {$Unwind}
 **/
function _$dc_n(v, d, infod) {
    if (d === 0n) {
        throw new $Unwind($Unwind_DivZero, infod);
    }

    return v / d;
}

/**
 * @function
 * @param {bigint} v
 * @param {bigint} d
 * @param {string | undefined} infod
 * @returns {bigint}
 * @throws {$Unwind}
 **/
function _$dc_I(v, d, infod) {
    if (d === 0n) {
        throw new $Unwind($Unwind_DivZero, infod);
    }

    return v / d;
}

/**
 * @function
 * @param {bigint} v
 * @param {bigint} d
 * @param {string | undefined} infod
 * @returns {bigint}
 * @throws {$Unwind}
 **/
function _$dc_N(v, d, infod) {
    if (d === 0n) {
        throw new $Unwind($Unwind_DivZero, infod);
    }

    return v / d;
}

/**
 * @function
 * @param {number} v
 * @param {number} d
 * @param {string | undefined} infod
 * @returns {number}
 * @throws {$Unwind}
 **/
function _$dc_f(v, d, infod) {
    if (d === 0) {
        throw new $Unwind($Unwind_DivZero, infod);
    }

    return v / d;
}

/**
 * @function
 * @param {boolean} cond 
 * @param {string | undefined} info 
 * @throws {$Unwind}
 **/
function _$exhaustive(cond, info) {
    if (!cond) {
        throw new $Unwind($Unwind_NonExhaustive, info);
    }
}

/**
 * @function
 * @param {string | undefined} info 
 * @throws {$Unwind}
 **/
function _$abort(info) {
    throw new $Unwind($Unwind_Assert, info);
}

/**
 * @function
 * @param {boolean} cond 
 * @param {string | undefined} info 
 * @throws {$Unwind}
 **/
function _$assert(cond, info) {
    if (!cond) {
        throw new $Unwind($Unwind_Assert, info);
    }
}

/**
 * @function
 * @param {boolean} cond 
 * @param {string | undefined} info 
 * @throws {$Unwind}
 **/
function _$formatchk(ok, info) {
    if (!ok) {
        throw new $Unwind($Unwind_Format, info);
    }
}

/**
 * @function
 * @param {boolean} cond 
 * @param {string | undefined} info 
 * @throws {$Unwind}
 **/
function _$invariant(cond, info) {
    if (!cond) {
        throw new $Unwind($Unwind_Invariant, info);
    }
}

/**
 * @function
 * @param {boolean} cond 
 * @param {string | undefined} info 
 * @throws {$Unwind}
 **/
function _$validate(cond, info) {
    if (!cond) {
        throw new $Unwind($Unwind_Validate, info);
    }
}

/**
 * @function
 * @param {boolean} cond 
 * @param {string | undefined} info 
 * @throws {$Unwind}
 **/
function _$precond(cond, info) {
    if (!cond) {
        throw new $Unwind($Unwind_PreCond, info);
    }
}

/**
 * @function
 * @param {boolean} cond 
 * @param {string | undefined} info
 **/
function _$softprecond(cond, info) {
   if (!cond) {
        //TODO: later we need to do this in a task-local context
        _$softfails.push(info);
    }
}


/**
 * @function
 * @param {boolean} cond 
 * @param {string | undefined} info 
 * @throws {$Unwind}
 **/
function _$postcond(cond, info) {
    if (!cond) {
        throw new $Unwind($Unwind_PostCond, info);
    }
}

/**
 * @function
 * @param {boolean} cond 
 * @param {string | undefined} info 
 **/
function _$softpostcond(cond, info) {
   if (!cond) {
        //TODO: later we need to do this in a task-local context
        _$softfails.push(info);
    }
}

/**
 * @function
 * @param {Map<string, any>} memmap
 * @param {string} key
 * @param {function(): any} comp
 **/ 
function _$memoconstval(memmap, key, comp) {
    const vval = memmap.get(key);
    if(vval !== undefined) {
        return vval;
    }

    const nval = comp();
    memmap.set(key, nval);

    return nval;
}

/**
 * @function
 * @param {string} pattern
 * @param {string} input
 * @param {string} inns
 * @throws {$Unwind}
 * @returns {boolean}
 **/
function _$accepts(pattern, input, inns) {
    try {
        return accepts(pattern, input, inns);
    }
    catch(e) {
        throw new $Unwind($Unwind_TypeAs, `Invalid regex pattern -- ${e.msg}`);
    }
}

export {
    _$softfails,
    _$supertypes,
    _$feqraw, _$fneqraw, _$flessraw,
    _$fisSubtype, _$fisNotSubtype, _$fasSubtype, _$fasNotSubtype,
    _$b, 
    _$rc_i, _$rc_n, _$rc_N, _$rc_f, _$dc_i, _$dc_n, _$dc_I, _$dc_N, _$dc_f,
    _$exhaustive,
    _$abort, _$assert, _$formatchk, _$invariant, _$validate, _$precond, _$softprecond, _$postcond, _$softpostcond,
    _$memoconstval,
    _$accepts
};
