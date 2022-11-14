import * as assert from "assert";
import Decimal from "decimal.js";

import {ResolvedType} from "../frontend/tree_ir/tir_type"

class InterpreterType {
    readonly tritype: ResolvedType;
    readonly xxx -;
}

type BSQNone = undefined;
type BSQNothing = null;

type BSQBool = boolean;
type BSQNat = bigint;
type BSQInt = bigint;
type BSQBigNat = bigint;
type BSQBigInt = bigint;

type BSQRational = {num: bigint, denom: bigint};
type BSQFloat = number;
type BSQDecimal = Decimal;

type BSQString = string;
type BSQASCIIString = string;

type BSQByteBuffer = Uint8Array;

type BSQDateTime = {year: number, month: number, day: number, hour: number, min: number, tzdata: String};
type BSQUTCDateTime = {year: number, month: number, day: number, hour: number, min: number};
type BSQPlainDate = {year: number, month: number, day: number};
type BSQPlainTime = {hour: number, min: number};

type BSQTickTime = bigint;
type BSQLogicalTime = bigint;
type BSQISOTimeStamp = {year: number, month: number, day: number, hour: number, min: number, sec: number, millis: number};

type BSQUUID4 = string;
type BSQUUID7 = string;
type BSQSHAContentHash = string;
type BSQLatLongCoordinate = {lat: number, long: number};

type BSQRegex = number;

type BSQRecord = Map<BSQPropertyID, BSQValue>;
type BSQTuple = BSQValue[];
type BSQEntity = Map<BSQFieldID, BSQValue>;

type BSQEphemeralList = BSQValue[];

class BSQUnion {
    readonly utype: InterpreterType;
    readonly uvalue: BSQValue;

    constructor(utype: InterpreterType, uvalue: BSQValue) {
        this.utype = utype;
        this.uvalue = uvalue;
    }
}

type BSQValue = BSQNone | BSQNothing | BSQBool | BSQNat | BSQInt | BSQBigNat | BSQBigInt | BSQRational | BSQFloat | BSQDecimal | BSQString | BSQASCIIString |
        BSQByteBuffer | BSQDateTime | BSQUTCDateTime | BSQPlainDate | BSQPlainTime | BSQTickTime | BSQLogicalTime | BSQISOTimeStamp | BSQUUID4 | BSQUUID7 | 
        BSQSHAContentHash | BSQLatLongCoordinate | BSQRegex | BSQRecord | BSQTuple | BSQEntity | BSQEphemeralList | BSQUnion;

export {
    BSQNone, BSQNothing, BSQBool, BSQNat, BSQInt, BSQBigNat, BSQBigInt, BSQRational, BSQFloat, BSQDecimal, BSQString, BSQASCIIString,
    BSQByteBuffer, BSQDateTime, BSQUTCDateTime, BSQPlainDate, BSQPlainTime, BSQTickTime, BSQLogicalTime, BSQISOTimeStamp, BSQUUID4, BSQUUID7, BSQSHAContentHash,
    BSQLatLongCoordinate, BSQRegex, BSQRecord, BSQTuple, BSQEntity, BSQEphemeralList, BSQUnion,
    BSQValue    
};
