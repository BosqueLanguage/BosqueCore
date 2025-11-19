import { MAX_SAFE_INT, MAX_SAFE_NAT, MIN_SAFE_INT } from "../frontend/assembly";
import { IRExpression, IRExpressionTag, IRLiteralBigIntExpression, IRLiteralBigNatExpression, IRLiteralBoolExpression, IRLiteralComplexExpression, IRLiteralCRegexExpression, IRLiteralDeltaDateTimeExpression, IRLiteralDeltaISOTimeStampExpression, IRLiteralDeltaLogicalTimeExpression, IRLiteralDeltaSecondsExpression, IRLiteralFloatExpression, IRLiteralIntExpression, IRLiteralISOTimeStampExpression, IRLiteralLogicalTimeExpression, IRLiteralNatExpression, IRLiteralPlainDateExpression, IRLiteralPlainTimeExpression, IRLiteralSHAContentHashExpression, IRLiteralTAITimeExpression, IRLiteralTZDateTimeExpression, IRLiteralUnicodeRegexExpression, IRLiteralUUIDv4Expression, IRLiteralUUIDv7Expression } from "./irbody";

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
        else if(ttag === IRExpressionTag.IRLiteralTZDateTimeExpression) {
            const dtinfo = (exp as IRLiteralTZDateTimeExpression);
            return `TZDateTime{{${dtinfo.date.year}, ${dtinfo.date.month}, ${dtinfo.date.day}}, {${dtinfo.time.hour}, ${dtinfo.time.minute}, ${dtinfo.time.second}}, "${dtinfo.timezone}"};`;
        }
        else if(ttag === IRExpressionTag.IRLiteralTAITimeExpression) {
            const taiinfo = (exp as IRLiteralTAITimeExpression);
            return `TAITime{{${taiinfo.date.year}, ${taiinfo.date.month}, ${taiinfo.date.day}}, {${taiinfo.time.hour}, ${taiinfo.time.minute}, ${taiinfo.time.second}}};`;
        }
        else if(ttag === IRExpressionTag.IRLiteralPlainDateExpression) {
            const pdate = (exp as IRLiteralPlainDateExpression);
            return `PlainDate{${pdate.date.year}, ${pdate.date.month}, ${pdate.date.day}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralPlainTimeExpression) {
            const ptime = (exp as IRLiteralPlainTimeExpression);
            return `PlainTime{${ptime.time.hour}, ${ptime.time.minute}, ${ptime.time.second}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralLogicalTimeExpression) {
            const ltime = (exp as IRLiteralLogicalTimeExpression);
            return `LogicalTime{${ltime.ticks}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralISOTimeStampExpression) {
            const isotimestamp = (exp as IRLiteralISOTimeStampExpression);
            return `ISOTimeStamp{{${isotimestamp.date.year}, ${isotimestamp.date.month}, ${isotimestamp.date.day}}, {${isotimestamp.time.hour}, ${isotimestamp.time.minute}, ${isotimestamp.time.second}}, ${isotimestamp.milliseconds}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralDeltaDateTimeExpression) {
            const ddtexp = (exp as IRLiteralDeltaDateTimeExpression);
            return `DeltaDateTime{'${ddtexp.sign}', {${ddtexp.deltadate.years}, ${ddtexp.deltadate.months}, ${ddtexp.deltadate.days}, {${ddtexp.deltatime.hours}, ${ddtexp.deltatime.minutes}, ${ddtexp.deltatime.seconds}}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralDeltaISOTimeStampExpression) {
            const itsexp = (exp as IRLiteralDeltaISOTimeStampExpression);
            return `DeltaISOTimeStamp{'${itsexp.sign}', {${itsexp.deltadate.years}, ${itsexp.deltadate.months}, ${itsexp.deltadate.days}}, {${itsexp.deltatime.hours}, ${itsexp.deltatime.minutes}, ${itsexp.deltatime.seconds}}, ${itsexp.deltatime.milliseconds}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralDeltaSecondsExpression) {
            const dsexp = (exp as IRLiteralDeltaSecondsExpression);
            return `DeltaSeconds{'${dsexp.sign}', ${dsexp.seconds}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralDeltaLogicalTimeExpression) {
            const dltexp = (exp as IRLiteralDeltaLogicalTimeExpression);
            return `DeltaLogicalTime{'${dltexp.sign}', ${dltexp.ticks}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralUnicodeRegexExpression) {
            return `Runtime::g_regexs[${(exp as IRLiteralUnicodeRegexExpression).regexID}]`;
        }
        else if(ttag === IRExpressionTag.IRLiteralCRegexExpression) {
            return `Runtime::g_regexs[${(exp as IRLiteralCRegexExpression).regexID}]`;
        }
        else {
            assert(false, `CPPEmitter: Unsupported IR expression type -- ${exp.constructor.name}`);
        }
    }
}

export {
    CPPEmitter
};
