"use strict;"

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
 * @throws {Error}
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
 * @throws {Error}
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
 * @throws {Error}
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
 * @throws {Error}
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
 * @throws {Error}
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
 * @throws {Error}
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
    return new $Boxed(t, v);
}

export {
    _$b
};
