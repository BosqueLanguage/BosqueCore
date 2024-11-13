"use strict;"

import { accepts } from "@bosque/jsbrex";

let _$softfails = [];

const MIN_SAFE_INT = -9223372036854775807n;
const MAX_SAFE_INT = 9223372036854775807n;

const MAX_SAFE_NAT = 9223372036854775807n;

const $Unwind_NumericRange = Symbol("NumericRangeFailed");
const $Unwind_DivZero = Symbol("DivZeroFailed");
const $Unwind_BadRegex = Symbol("BadRegexFailed");

const $Unwind_Assert = Symbol("AssertFailed");
const $Unwind_PreCond = Symbol("PreCondFailed");
const $Unwind_PostCond = Symbol("PostCondFailed");

const $Unwind_Format = Symbol("FormatFailed");
const $Unwind_Invariant = Symbol("InvariantFailed");
const $Unwind_Validate = Symbol("ValidateFailed");

const $Unwind_TypeAs = Symbol("TypeAsFailed");
const $Unwind_NonExhaustive = Symbol("ExhaustiveFailed");

function $Unwind(tag, info) {
    this.$tag = tag;
    this.$info = info;
}

let _$supertypes = {};

function _$fisSubtype(tag, tsym) {
    return _$supertypes.get(tag).has(tsym);
}

function _$fisNotSubtype(tag, tsym) {
    return !_$supertypes.get(tag).has(tsym);
}

function _$fasSubtype(val, tag, tsym, info) {
    if (_$fisNotSubtype(tag, tsym)) {
        throw new $Unwind($Unwind_TypeAs, info);
    }
        
    return val;
};

function _$fasNotSubtype(val, tag, tsym, info) {
    if (_$fisSubtype(tag, tsym)) {
        throw new $Unwind($Unwind_TypeAs, info);
    }
        
    return val;
};

const $SymbolNone = Symbol.for("None");

const $VRepr = {
    _$isNone: function() { return this.$tsym === $SymbolNone; },
    _$isNotNone: function() { return this.$tsym !== $SymbolNone; },

    _$isSome: function() { return this.$tsym !== $SymbolNone; },
    _$isNotSome: function() { return this.$tsym === $SymbolNone; },

    _$asNone: function(info) { if (this._$isNotNone()) { throw new $Unwind($Unwind_TypeAs, info); } return this; },
    _$asNotNone: function(info) { if (this._$isNone()) { throw new $Unwind($Unwind_TypeAs, info); } return this.value; },
    
    _$asSome: function(info) { if (this._$isNotSome()) { throw new $Unwind($Unwind_TypeAs, info); } return this.value; },
    _$asNotSome: function(info) { if (this._$isSome()) { throw new $Unwind($Unwind_TypeAs, info); } return this; },

    _$asOk: function(oktype, info) { if (this._$isNot(oktype)) { throw new $Unwind($Unwind_TypeAs, info); } return this.value; },
    _$asNotOk: function(oktype, info) { if (this._$is(oktype)) { throw new $Unwind($Unwind_TypeAs, info); } return this.value; },
    
    _$asFail: function(failtype, info) { if (this._$is(failtype)) { throw new $Unwind($Unwind_TypeAs, info); } return this.value; },
    _$asNotFail: function(failtype, info) { if (this._$isNot(failtype)) { throw new $Unwind($Unwind_TypeAs, info); } return this.value; },

    _$is: function(tsym) { return this.$tsym === tsym; },
    _$isNot: function(tsym) { return this.$tsym !== tsym; },

    _$isSubtype: function(tsym) { return _$fisSubtype(this.$tsym, tsym); },
    _$isNotSubtype: function(tsym) { return _$fisNotSubtype(this.$tsym, tsym); },

    _$as: function(tsym, info) { if (this._$isNot(tsym)) { throw new $Unwind($Unwind_TypeAs, info); } return this; },
    _$asNot: function(tsym, info) { if (this._$is(tsym)) { throw new $Unwind($Unwind_TypeAs, info); } return this; },
    
    _$asSubtype: function(tsym, info) { return _$fasSubtype(this, this.$tsym, tsym, info); },
    _$asNotSubtype: function(tsym, info) { return _$fasNotSubtype(this, this.$tsym, tsym, info); },

    _$isOptionSubtype: function(tsym) { return this._$isNone() || _$fisSubtype(this.$tsym, tsym); },
    _$isNotOptionSubtype: function(tsym) { return this._$isNotNone() && _$fisNotSubtype(this.$tsym, tsym); },

    _$asOptionSubtype: function(tsym, info) { if (this._$isNotOptionSubtype(tsym)) { throw new $Unwind($Unwind_TypeAs, info); } return this; },
    _$asNotOptionSubtype: function(tsym, info) { if (this._$isOptionSubtype(tsym)) { throw new $Unwind($Unwind_TypeAs, info); } return this; }
};

const _$None = Object.create($VRepr, { 
    $tsym: { value: Symbol.for("None") }
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
    const dd = _$opubx(d);
    if (dd === 0n) {
        throw new $Unwind($Unwind_DivZero, "Division by 0");
    }

    return _$opubx(n) / dd; 
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
    "Enum": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); },
    "Bool": function(v1, v2) { return _$opubx(v1) && _$opubx(v2); },
    "Int": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); },
    "Nat": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); },
    "BigInt": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); },
    "BigNat": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); },
    "String": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); },
    "CString": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); }
};

const _$fkeqopt = {
    "Enum": function(v1, v2) { return v1._$isNone() && _$fkeq.Enum(v1.value, v2); },
    "Bool": function(v1, v2) { return v1._$isSome() && _$fkeq.Bool(v1.value, v2); },
    "Int": function(v1, v2) { return v1._$isSome() && _$fkeq.Int(v1.value, v2); },
    "Nat": function(v1, v2) { return v1._$isSome() && _$fkeq.Nat(v1.value, v2); },
    "BigInt": function(v1, v2) { return v1._$isSome() && _$fkeq.BigInt(v1.value, v2); },
    "BigNat": function(v1, v2) { return v1._$isSome() && _$fkeq.BigNat(v1.value, v2); },
    "String": function(v1, v2) { return v1._$isSome() && _$fkeq.String(v1.value, v2); },
    "CString": function(v1, v2) { return v1._$isSome() && _$fkeq.CString(v1.value, v2); }
};

const _$fkneq = {
    "Enum": function(v1, v2) { return _$opubx(v1) !== _$opubx(v2); },
    "Bool": function(v1, v2) { return _$opubx(v1) !== _$opubx(v2); },
    "Int": function(v1, v2) { return _$opubx(v1) !== _$opubx(v2); },
    "Nat": function(v1, v2) { return _$opubx(v1) !== _$opubx(v2); },
    "BigInt": function(v1, v2) { return _$opubx(v1) !== _$opubx(v2); },
    "BigNat": function(v1, v2) { return _$opubx(v1) !== _$opubx(v2); },
    "String": function(v1, v2) { return _$opubx(v1) !== _$opubx(v2); },
    "CString": function(v1, v2) { return _$opubx(v1) !== _$opubx(v2); }
};

const _$fkneqopt = {
    "Enum": function(v1, v2) { return v1._$isNone() || _$fkneq.Enum(v1.value, v2); },
    "Bool": function(v1, v2) { return v1._$isNone() || _$fkneq.Bool(v1.value, v2); },
    "Int": function(v1, v2) { return v1._$isNone() || _$fkneq.Int(v1.value, v2); },
    "Nat": function(v1, v2) { return v1._$isNone() || _$fkneq.Nat(v1.value, v2); },
    "BigInt": function(v1, v2) { return v1._$isNone() || _$fkneq.BigInt(v1.value, v2); },
    "BigNat": function(v1, v2) { return v1._$isNone() || _$fkneq.BigNat(v1.value, v2); },
    "String": function(v1, v2) { return v1._$isNone() || _$fkneq.String(v1.value, v2); },
    "CString": function(v1, v2) { return v1._$isNone() || _$fkneq.CString(v1.value, v2); }
};

const _$fkless = {
    "Enum": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); },
    "Bool": function(v1, v2) { return !_$opubx(v1) && _$opubx(v2); },
    "Int": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); },
    "Nat": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); },
    "BigInt": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); },
    "BigNat": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); },
    "String": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); },
    "CString": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); }
};

const _$fnumeq = {
    "Int": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); },
    "Nat": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); },
    "BigInt": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); },
    "BigNat": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); },
    "Float": function(v1, v2) { return _$opubx(v1) === _$opubx(v2); }
};

const _$fnumless = {
    "Int": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); },
    "Nat": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); },
    "BigInt": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); },
    "BigNat": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); },
    "Float": function(v1, v2) { return _$opubx(v1) < _$opubx(v2); }
};

const _$fnumlesseq = {
    "Int": function(v1, v2) { return _$opubx(v1) <= _$opubx(v2); },
    "Nat": function(v1, v2) { return _$opubx(v1) <= _$opubx(v2); },
    "BigInt": function(v1, v2) { return _$opubx(v1) <= _$opubx(v2); },
    "BigNat": function(v1, v2) { return _$opubx(v1) <= _$opubx(v2); },
    "Float": function(v1, v2) { return _$opubx(v1) <= _$opubx(v2); }
};

function _$exhaustive(cond, info) {
    if (!cond) {
        throw new $Unwind($Unwind_NonExhaustive, info);
    }
}

function _$formatchk(ok, info) {
    if (!ok) {
        throw new $Unwind($Unwind_Format, info);
    }
}

function _$abort(info) {
    throw new $Unwind($Unwind_Assert, info);
}

function _$assert(cond, info) {
    if (!_$opubx(cond)) {
        throw new $Unwind($Unwind_Assert, info);
    }
}

function _$invariant(cond, info) {
    if (!_$opubx(cond)) {
        throw new $Unwind($Unwind_Invariant, info);
    }
}

function _$validate(cond, info) {
    if (!_$opubx(cond)) {
        throw new $Unwind($Unwind_Validate, info);
    }
}

function _$precond(cond, info) {
    if (!_$opubx(cond)) {
        throw new $Unwind($Unwind_PreCond, info);
    }
}

function _$softprecond(cond, info) {
   if (!_$opubx(cond)) {
        //TODO: later we need to do this in a task-local context
        _$softfails.push(info);
    }
}

function _$postcond(cond, info) {
    if (!_$opubx(cond)) {
        throw new $Unwind($Unwind_PostCond, info);
    }
}

function _$softpostcond(cond, info) {
   if (!_$opubx(cond)) {
        //TODO: later we need to do this in a task-local context
        _$softfails.push(info);
    }
}

function _$memoconstval(memmap, key, comp) {
    const vval = memmap.get(key);
    if(vval !== undefined) {
        return vval;
    }

    const nval = comp();
    memmap.set(key, nval);

    return nval;
}

function _$accepts(pattern, input, inns) {
    try {
        return accepts(pattern, input, inns);
    }
    catch(e) {
        throw new $Unwind($Unwind_BadRegex, `Invalid regex pattern -- ${e.msg}`);
    }
}

export {
    $VRepr,
    _$softfails,
    _$supertypes,
    _$fisSubtype, _$fisNotSubtype, _$fasSubtype, _$fasNotSubtype,
    _$None,
    _$not, _$negate,
    _$add, _$sub, _$mult, _$div,
    _$bval,
    _$fkeq, _$fkeqopt, _$fkneq, _$fkneqopt, _$fkless,
    _$fnumeq, _$fnumless, _$fnumlesseq,
    _$exhaustive,
    _$abort, _$assert, _$formatchk, _$invariant, _$validate, _$precond, _$softprecond, _$postcond, _$softpostcond,
    _$memoconstval,
    _$accepts
};
