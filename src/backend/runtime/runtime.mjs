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
 * @function
 * @param {any} val
 * @param {Symbol} tag
 * @param {Symbol} tsym
 * @param {string | undefined} info
 * @returns {any}
 * @throws {$Unwind}
 **/
function _$fasSubtype(val, tag, tsym, info) {
    if (_$fisNotSubtype(tag, tsym)) {
        throw new $Unwind($Unwind_TypeAs, info);
    }
        
    return val;
};

/**
 * @function
 * @param {any} val
 * @param {Symbol} tag
 * @param {Symbol} tsym
 * @param {string | undefined} info
 * @returns {any}
 * @throws {$Unwind}
 **/
function _$fasNotSubtype(val, tag, tsym, info) {
    if (_$fisSubtype(tag, tsym)) {
        throw new $Unwind($Unwind_TypeAs, info);
    }
        
    return val;
};

/**
 * @constant
 * @type {Symbol}
 **/
const $SymbolNone = Symbol.for("None");

const $VRepr = {
    _$isNone: function() { return this.$tag === $SymbolNone; },
    _$isNotNone: function() { return this.$tag !== $SymbolNone; },

    _$isSome: function() { return this.$tag !== $SymbolNone; },
    _$isNotSome: function() { return this.$tag === $SymbolNone; },

    _$asNone: function(info) { if (this._$isNotNone()) { throw new $Unwind($Unwind_TypeAs, info); } return this; },
    _$asNotNone: function(info) { if (this._$isNone()) { throw new $Unwind($Unwind_TypeAs, info); } return this; },
    
    _$asSome: function(info) { if (this._$isNone()) { throw new $Unwind($Unwind_TypeAs, info); } return this; },
    _$asNotSome: function(info) { if (this._$isSome()) { throw new $Unwind($Unwind_TypeAs, info); } return this; },

    _$is: function(tsym) { return this.$tag === tsym; },
    _$isNot: function(tsym) { return this.$tag !== tsym; },

    _$isSubtype: function(tsym) { return _$fisSubtype(this.$tag, tsym); },
    _$isNotSubtype: function(tsym) { return _$fisNotSubtype(this.$tag, tsym); },

    _$as: function(tsym, info) { if (this._$isNot(tsym)) { throw new $Unwind($Unwind_TypeAs, info); } return this; },
    _$asNot: function(tsym, info) { if (this._$is(tsym)) { throw new $Unwind($Unwind_TypeAs, info); } return this; },
    
    _$asSubtype: function(tsym, info) { return _$fasSubtype(this, this.$tag, tsym, info); },
    _$asNotSubtype: function(tsym, info) { return _$fasNotSubtype(this, this.$tag, tsym, info); },

    _$isOptionSubtype: function(tsym) { return this._$isNone() || _$fisSubtype(this.$tag, tsym); },
    _$isNotOptionSubtype: function(tsym) { return this._$isNotNone() && _$fisNotSubtype(this.$tag, tsym); },

    _$asOptionSubtype: function(tsym, info) { if (this._$isNotOptionSubtype(tsym)) { throw new $Unwind($Unwind_TypeAs, info); } return this; },
    _$asNotOptionSubtype: function(tsym, info) { if (this._$isOptionSubtype(tsym)) { throw new $Unwind($Unwind_TypeAs, info); } return this; }
};

/**
 * @constant
 * @type {any}
 **/
const _$None = Object.create($VRepr, { 
    $tag: { value: Symbol.for("None"), writable: false, configurable: false, enumerable: true }
});

function _$opubx(v) { return (typeof(v) === "object") ? v.value : v; }

function _$checkbounds(v, cc, low, high) {
    if (v < low) {
        throw new $Unwind($Unwind_NumericRange, "Overflow");
    }

    if(high !== undefined && high < v) {
        throw new $Unwind($Unwind_NumericRange, "Overflow");
    }

    return cc !== undefined ? cc(v) : v;
}

function _$opcreate(v, cc) {
    return cc !== undefined ? cc(v) : v;
}

function _$not(v, cc) { return _$opcreate(!_$opubx(v), cc); }

function _$addtt(v1, v2) { return _$opubx(v1) + _$opubx(v2); }
function _$subtt(v1, v2) { return _$opubx(v1) - _$opubx(v2); }
function _$multt(v1, v2) { return _$opubx(v1) * _$opubx(v2); }

function _$divtt(n, d) { 
    const dd = _$opubx(v2);
    if (dd === 0n) {
        throw new $Unwind($Unwind_DivZero, "Division by 0");
    }

    return _$opubx(v1) / dd; 
}

const _$negate = {
    "Int": function(v, cc) { return _$opcreate(-v, cc); },
    "BigInt": function(v, cc) { return _$opcreate(-v, cc); },
    "Float": function(v, cc) { return _$opcreate(-v, cc); }
};

const _$add = {
    "Int": function(v1, v2, cc) { return _$checkbounds(_$addtt(v1, v2), cc, MIN_SAFE_INT, MAX_SAFE_INT); },
    "Nat": function(v1, v2, cc) { return _$checkbounds(_$addtt(v1, v2), cc, 0n, MAX_SAFE_NAT); },
    "BigInt": function(v1, v2, cc) { return _$opcreate(_$addtt(v1, v2), cc); },
    "BigNat": function(v1, v2, cc) { return _$opcreate(_$addtt(v1, v2), cc); },
    "Float": function(v1, v2, cc) { return _$opcreate(_$addtt(v1, v2), cc); }
};

const _$sub = {
    "Int": function(v1, v2, cc) { return _$checkbounds(_$subtt(v1, v2), cc, MIN_SAFE_INT, MAX_SAFE_INT); },
    "Nat": function(v1, v2, cc) { return _$checkbounds(_$subtt(v1, v2), cc, 0n, MAX_SAFE_NAT); },
    "BigInt": function(v1, v2, cc) { return _$opcreate(_$subtt(v1, v2), cc); },
    "BigNat": function(v1, v2, cc) { return _$checkbounds(_$subtt(v1, v2), cc, 0n, undefined); },
    "Float": function(v1, v2, cc) { return _$opcreate(_$subtt(v1, v2), cc); }
};

const _$mult = {
    "Int": function(v1, v2, cc) { return _$checkbounds(_$multt(v1, v2), cc, MIN_SAFE_INT, MAX_SAFE_INT); },
    "Nat": function(v1, v2, cc) { return _$checkbounds(_$multt(v1, v2), cc, 0n, MAX_SAFE_NAT); },
    "BigInt": function(v1, v2, cc) { return _$opcreate(_$multt(v1, v2), cc); },
    "BigNat": function(v1, v2, cc) { return _$opcreate(_$multt(v1, v2), cc); },
    "Float": function(v1, v2, cc) { return _$opcreate(_$multt(v1, v2), cc); }
};

const _$div = {
    "Int": function(v1, v2, cc) { return _$opcreate(_$divtt(v1, v2), cc); },
    "Nat": function(v1, v2, cc) { return _$opcreate(_$divtt(v1, v2), cc); },
    "BigInt": function(v1, v2, cc) { return _$opcreate(_$divtt(v1, v2), cc); },
    "BigNat": function(v1, v2, cc) { return _$opcreate(_$divtt(v1, v2), cc); },
    "Float": function(v1, v2, cc) { return _$opcreate(_$divtt(v1, v2), cc); }
};

function _$bval(v) {
    return _$opubx(v);
}

const _$fkeq = {
    "Bool": function(v1, v2) { return _$opubx(v1) && _$opubx(v2); },
    "Int": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); },
    "Nat": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); },
    "BigInt": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); },
    "BigNat": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); },
    "String": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); },
    "CString": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); }
};

const _$fkneq = {
    "Bool": function(v1, v2) { return _$opubx(v1) !== _$opubx(v2); },
    "Int": function(v1, v2) { return _$opubx(v1) !== _$opubx(v2); },
    "Nat": function(v1, v2) { return _$opubx(v1) !== _$opubx(v2); },
    "BigInt": function(v1, v2) { return _$opubx(v1) !== _$opubx(v2); },
    "BigNat": function(v1, v2) { return _$opubx(v1) !== _$opubx(v2); },
    "String": function(v1, v2) { return _$opubx(v1) !== _$opubx(v2); },
    "CString": function(v1, v2) { return _$opubx(v1) !== _$opubx(v2); }
};


const _$fkless = {
    "Bool": function(v1, v2) { return !_$opubx(v1) && _$opubx(v2); },
    "Int": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); },
    "Nat": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); },
    "BigInt": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); },
    "BigNat": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); },
    "String": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); },
    "CString": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); }
};


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
    $VRepr,
    _$softfails,
    _$supertypes,
    _$feqraw, _$fneqraw, _$flessraw,
    _$fisSubtype, _$fisNotSubtype, _$fasSubtype, _$fasNotSubtype,
    _$None,
    _$bval,
    _$not, _$negate,
    _$add, _$sub, _$mult, _$div,
    _$fkeq, _$fkneq, _$fkless,
    _$exhaustive,
    _$abort, _$assert, _$formatchk, _$invariant, _$validate, _$precond, _$softprecond, _$postcond, _$softpostcond,
    _$memoconstval,
    _$accepts
};
