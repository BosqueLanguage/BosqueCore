"use strict;"

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
const $Unwind_Assert = Symbol("AssertFailed");

/**
 * @constant
 * @type {Symbol}
 **/
const $Unwind_TypeAs = Symbol("TypeAsFailed");

function $Unwind(tag, info) {
    this.$tag = tag;
    this.$info = info;
}

/**
 * @constant
 * @type {Map<Symbol, Set<Symbol>>}
 */
let $supertypes = new Map();

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
 * @type {$Boxed}
 **/
const $BoxedNone = new $Boxed(Symbol.for("None"), null);

/**
 * @method
 * @param {any} v
 * @returns {boolean}
 **/
$Boxed.prototype._$keyEqOf = function(v) {
    return this.$val !== null && this.$val === v;
};

/**
 * @method
 * @param {any} v
 * @returns {boolean}
 **/
$Boxed.prototype._$keyNeqOf = function(v) {
    return this.$val === null || this.$val !== v;
};

/**
 * @method
 * @returns {boolean}
 **/
$Boxed.prototype._$isNone = function() {
    return this.$val === null;
};

/**
 * @method
 * @returns {boolean}
 **/
$Boxed.prototype._$isSome = function() {
    return this.$val !== null;
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
    return $supertypes.get(this.$tag).has(tsym);
};

/**
 * @method
 * @param {Symbol} tsym
 * @returns {boolean}
 **/
$Boxed.prototype._$isNotSubtype = function(tsym) {
    return !$supertypes.get(this.$tag).has(tsym);
};

/**
 * @method
 * @returns {any}
 * @throws {$Unwind}
 **/
$Boxed.prototype._$asNone = function() {
    if (this._$isNone()) {
        return null;
    }
    else {
        throw new $Unwind($Unwind_TypeAs, "Expected None but got Some");
    }
};

/**
 * @method
 * @returns {any}
 * @throws {$Unwind}
 **/
$Boxed.prototype._$asSome = function() {
    if (this._$isSome()) {
        return this.$val;
    }
    else {
        throw new $Unwind($Unwind_TypeAs, "Expected Some but got None");
    }
};

/**
 * @method
 * @param {Symbol} tsym
 * @param {boolean} ubx
 * @returns {any}
 * @throws {$Unwind}
 **/
$Boxed.prototype._$as = function(tsym, ubx) {
    if (this._$is(tsym)) {
        return ubx ? this.$val : this;
    } else {
        throw new $Unwind($Unwind_TypeAs, `Expected ${tsym.toString()} but got ${this.$tag.toString()}`);
    }
};

/**
 * @method
 * @param {Symbol} tsym
 * @param {boolean} ubx
 * @returns {any}
 * @throws {$Unwind}
 **/
$Boxed.prototype._$asNot = function(tsym, ubx) {
    if (this._$isNot(tsym)) {
        return ubx ? this.$val : this;
    } else {
        throw new $Unwind($Unwind_TypeAs, `Expected type other than ${tsym.toString()}`);
    }
};

/**
 * @method
 * @param {Symbol} tsym
 * @param {boolean} ubx
 * @returns {any}
 * @throws {$Unwind}
 **/
$Boxed.prototype._$asSubtype = function(tsym, ubx) {
    if (this._$isSubtype(tsym)) {
        return ubx ? this.$val : this;
    } else {
        throw new $Unwind($Unwind_TypeAs, `Expected ${tsym.toString()} but got ${this.$tag.toString()}`);
    }
};

/**
 * @method
 * @param {Symbol} tsym
 * @param {boolean} ubx
 * @returns {any}
 * @throws {$Unwind}
 **/
$Boxed.prototype._$asNotSubtype = function(tsym, ubx) {
    if (this._$isNotSubtype(tsym)) {
        return ubx ? this.$val : this;
    } else {
        throw new $Unwind($Unwind_TypeAs, `Expected type other than ${tsym.toString()}`);
    }
};

/**
 * @function
 * @param {Symbol} tsym
 * @returns {any}
 * @returns {$Boxed}
 **/ 
function _$b(t, v) {
    return v !== null ? new $Boxed(t, v) : $BoxedNone;
}

/**
 * @function
 * @param {bigint} v
 * @returns {bigint}
 * @throws {$Unwind}
 **/
function _$rc_i($v) {
    if ($v < MIN_SAFE_INT || MAX_SAFE_INT < $v) {
        throw new $Unwind($Unwind_NumericRange, "Int value out of range");
    }

    return $v;
}

/**
 * @function
 * @param {bigint} v
 * @returns {bigint}
 * @throws {$Unwind}
 **/
function _$rc_n($v) {
    if ($v < 0n || MAX_SAFE_NAT < $v) {
        throw new $Unwind($Unwind_NumericRange, "Nat value out of range");
    }

    return $v;
}

/**
 * @function
 * @param {bigint} v
 * @returns {bigint}
 * @throws {$Unwind}
 **/
function _$rc_N($v) {
    if ($v < 0n) {
        throw new $Unwind($Unwind_NumericRange, "BigNat value is negative");
    }

    return $v;
}

/**
 * @function
 * @param {number} v
 * @returns {number}
 * @throws {$Unwind}
 **/
function _$rc_f($v) {
    if (Number.isNaN($v)) {
        throw new $Unwind($Unwind_NumericRange, "Value is NaN");
    }

    if (!Number.isFinite($v)) {
        throw new $Unwind($Unwind_NumericRange, "Value is Infinity");
    }

    return $v;
}

/**
 * @function
 * @param {bigint} v
 * @returns {bigint}
 * @throws {$Unwind}
 **/
function _$dc_i($v, $d) {
    if ($d === 0n) {
        throw new $Unwind($Unwind_DivZero, "Division by zero");
    }

    return _$rc_i($v / $d);
}

/**
 * @function
 * @param {bigint} v
 * @returns {bigint}
 * @throws {$Unwind}
 **/
function _$dc_n($v, $d) {
    if ($d === 0n) {
        throw new $Unwind($Unwind_DivZero, "Division by zero");
    }

    return _$rc_n($v / $d);
}

/**
 * @function
 * @param {bigint} v
 * @returns {bigint}
 * @throws {$Unwind}
 **/
function _$dc_I($v, $d) {
    if ($d === 0n) {
        throw new $Unwind($Unwind_DivZero, "Division by zero");
    }

    return _$rc_N($v / $d);
}

/**
 * @function
 * @param {bigint} v
 * @returns {bigint}
 * @throws {$Unwind}
 **/
function _$dc_N($v, $d) {
    if ($d === 0n) {
        throw new $Unwind($Unwind_DivZero, "Division by zero");
    }

    return _$rc_N($v / $d);
}

/**
 * @function
 * @param {number} v
 * @returns {number}
 * @throws {$Unwind}
 **/
function _$dc_f($v, $d) {
    if ($d === 0) {
        throw new $Unwind($Unwind_DivZero, "Division by zero");
    }

    return _$rc_f($v / $d);
}

export {
    _$b, 
    _$rc_i, _$rc_n, _$rc_N, _$rc_f, _$dc_i, _$dc_n, _$dc_I, _$dc_N, _$dc_f
};
