import { MAX_SAFE_INT, MAX_SAFE_NAT, MIN_SAFE_INT } from "../frontend/assembly";
import { IRExpression, IRExpressionTag, IRLiteralBigIntExpression, IRLiteralBigNatExpression, IRLiteralBoolExpression, IRLiteralComplexExpression, IRLiteralFloatExpression, IRLiteralIntExpression, IRLiteralNatExpression, IRLiteralSHAContentHashExpression, IRLiteralUUIDv4Expression, IRLiteralUUIDv7Expression } from "./irbody";

import assert from "node:assert";

class CPPEmitter {
    private emitExpression(exp: IRExpression): string {
        const ttag = exp.tag;

        if(ttag === IRExpressionTag.IRLiteralNoneExpression) {
            return "none";
        }
        else if(ttag === IRExpressionTag.IRLiteralBoolExpression) {
            return (exp as IRLiteralBoolExpression).value ? "btrue" : "bfalse";
        }
        else if(ttag === IRExpressionTag.IRLiteralNatExpression) {
            return `${(exp as IRLiteralNatExpression).value}_Nat`;
        }
        else if(ttag === IRExpressionTag.IRLiteralIntExpression) {
            return `${(exp as IRLiteralIntExpression).value}_Int`;
        }
        else if(ttag === IRExpressionTag.IRLiteralBigNatExpression) {
            const nval = BigInt((exp as IRLiteralBigNatExpression).value);
            if(nval <= MAX_SAFE_NAT) {
                return `${(exp as IRLiteralBigNatExpression).value}_BigNat`;
            }
            else {
                assert(false, `CPPEmitter: need to do bit shift construction for (really big) big nat -- ${(exp as IRLiteralBigNatExpression).value}`);
            }
        }
        else if(ttag === IRExpressionTag.IRLiteralBigIntExpression) {
            const ival = BigInt((exp as IRLiteralBigIntExpression).value);
            if(MIN_SAFE_INT <= ival && ival <= MAX_SAFE_INT) {
                return `${(exp as IRLiteralBigIntExpression).value}_BigInt`;
            }
            else {
                assert(false, `CPPEmitter: need to do bit shift construction for (really big) big int -- ${(exp as IRLiteralBigIntExpression).value}`);
            }
        }
        else if(ttag === IRExpressionTag.IRLiteralRationalExpression) {
            assert(false, "Rationals are currently unsupported in CPPEmitter");
        }
        else if(ttag === IRExpressionTag.IRLiteralFloatExpression) {
            return `${(exp as IRLiteralFloatExpression).value}_Float`;
        }
        else if(ttag === IRExpressionTag.IRLiteralDecimalExpression) {
            assert(false, "Decimals are currently unsupported in CPPEmitter");
        }
        else if(ttag === IRExpressionTag.IRLiteralDecimalDegreeExpression) {
            assert(false, "Decimal degrees are currently unsupported in CPPEmitter");
        }
        else if(ttag === IRExpressionTag.IRLiteralLatLongCoordinateExpression) {
            assert(false, "Lat/Long coordinates are currently unsupported in CPPEmitter");
        }
        else if(ttag === IRExpressionTag.IRLiteralComplexExpression) {
            return `Complex{${(exp as IRLiteralComplexExpression).real}_Float, ${(exp as IRLiteralComplexExpression).imaginary}_Float}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralByteBufferExpression) {
            assert(false, "ByteBuffers are currently unsupported in CPPEmitter");
        }
        else if(ttag === IRExpressionTag.IRLiteralUUIDv4Expression) {
            const bytes = (exp as IRLiteralUUIDv4Expression).bytes.map((b) => `0x${b.toString(16).padStart(2, '0')}`).join(", ");
            return `UUIDv4{${bytes}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralUUIDv7Expression) {
            const bytes = (exp as IRLiteralUUIDv7Expression).bytes.map((b) => `0x${b.toString(16).padStart(2, '0')}`).join(", ");
            return `UUIDv7{${bytes}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralSHAContentHashExpression) {
            const bytes = (exp as IRLiteralSHAContentHashExpression).bytes.map((b) => `0x${b.toString(16).padStart(2, '0')}`).join(", ");
            return `SHAContentHash{${bytes}}`;
        }

        IRLiteralTZDateTimeExpression, IRLiteralTAITimeExpression, IRLiteralPlainDateExpression, IRLiteralPlainTimeExpression, IRLiteralLogicalTimeExpression, IRLiteralISOTimeStampExpression,
        IRLiteralDeltaDateTimeExpression, IRLiteralDeltaISOTimeStampExpression, IRLiteralDeltaSecondsExpression, IRLiteralDeltaLogicalExpression,

        else {
            assert(false, `CPPEmitter: Unsupported IR expression type -- ${exp.constructor.name}`);
        }
    }
}

export {
    CPPEmitter
};
