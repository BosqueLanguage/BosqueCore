import { MAX_SAFE_INT, MAX_SAFE_NAT, MIN_SAFE_INT } from "../frontend/assembly";
import { IRExpression, IRExpressionTag, IRLiteralBigIntExpression, IRLiteralBigNatExpression, IRLiteralBoolExpression, IRLiteralComplexExpression, IRLiteralFloatExpression, IRLiteralIntExpression, IRLiteralNatExpression } from "./irbody";

import assert from "node:assert";

class CPPEmitter {
    private emitExpression(exp: IRExpression): string {
        const ttag = exp.tag;

        if(ttag === IRExpressionTag.IRLiteralNoneExpression) {
            return "Core::none";
        }
        else if(ttag === IRExpressionTag.IRLiteralBoolExpression) {
            return (exp as IRLiteralBoolExpression).value ? "true" : "false";
        }
        else if(ttag === IRExpressionTag.IRLiteralNatExpression) {
            return `${(exp as IRLiteralNatExpression).value}ull`;
        }
        else if(ttag === IRExpressionTag.IRLiteralIntExpression) {
            return `${(exp as IRLiteralIntExpression).value}ll`;
        }
        else if(ttag === IRExpressionTag.IRLiteralBigNatExpression) {
            const nval = BigInt((exp as IRLiteralBigNatExpression).value);
            if(nval <= MAX_SAFE_NAT) {
                return `${(exp as IRLiteralBigNatExpression).value}ull`;
            }
            else {
                assert(false, `CPPEmitter: need to do bit shift construction for (really big) big nat -- ${(exp as IRLiteralBigNatExpression).value}`);
            }
        }
        else if(ttag === IRExpressionTag.IRLiteralBigIntExpression) {
            const ival = BigInt((exp as IRLiteralBigIntExpression).value);
            if(MIN_SAFE_INT <= ival && ival <= MAX_SAFE_INT) {
                return `${(exp as IRLiteralBigIntExpression).value}ll`;
            }
            else {
                assert(false, `CPPEmitter: need to do bit shift construction for (really big) big int -- ${(exp as IRLiteralBigIntExpression).value}`);
            }
        }
        else if(ttag === IRExpressionTag.IRLiteralRationalExpression) {
            assert(false, "Rationals are currently unsupported in CPPEmitter");
        }
        else if(ttag === IRExpressionTag.IRLiteralFloatExpression) {
            return `${(exp as IRLiteralFloatExpression).value}f64`;
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
            return `std::complex<double>{${(exp as IRLiteralComplexExpression).real}f64, ${(exp as IRLiteralComplexExpression).imaginary}f64}`;
        }
        else {
            assert(false, `CPPEmitter: Unsupported IR expression type -- ${exp.constructor.name}`);
        }
    }
}

export {
    CPPEmitter
};
