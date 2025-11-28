import { MAX_SAFE_INT, MAX_SAFE_NAT, MIN_SAFE_INT } from "../../frontend/assembly";
import { IRExpression, IRExpressionTag, IRLiteralChkIntExpression, IRLiteralChkNatExpression, IRLiteralBoolExpression, IRLiteralByteExpression, IRLiteralCCharExpression, IRLiteralComplexExpression, IRLiteralCRegexExpression, IRLiteralDeltaDateTimeExpression, IRLiteralDeltaISOTimeStampExpression, IRLiteralDeltaLogicalTimeExpression, IRLiteralDeltaSecondsExpression, IRLiteralFloatExpression, IRLiteralIntExpression, IRLiteralISOTimeStampExpression, IRLiteralLogicalTimeExpression, IRLiteralNatExpression, IRLiteralPlainDateExpression, IRLiteralPlainTimeExpression, IRLiteralSHAContentHashExpression, IRLiteralStringExpression, IRLiteralTAITimeExpression, IRLiteralTZDateTimeExpression, IRLiteralUnicodeCharExpression, IRLiteralUnicodeRegexExpression, IRLiteralUUIDv4Expression, IRLiteralUUIDv7Expression, IRLiteralExpression, IRImmediateExpression, IRLiteralTypedExpression, IRLiteralTypedCStringExpression, IRAccessEnvHasExpression, IRAccessEnvGetExpression, IRAccessEnvTryGetExpression } from "../irdefs/irbody";

import assert from "node:assert";
import { TransformCPPNameManager } from "./namemgr";

const RUNTIME_NAMESPACE = "ᐸRuntimeᐳ";

class CPPEmitter {
    //The C++ TaskInfoRepr<U> for accessing the global info for the task we are emitting
    private cppTaskType: string;

    constructor(cppTaskType: string) {
        this.cppTaskType = cppTaskType;
    }

    private escapeLiteralCString(cstrbytes: number[]): string {
        let escstr = '"';
        for(const b of cstrbytes) {
            if(b === 0x5C) {
                escstr += "\\\\";
            }
            else if(b === 0x22) {
                escstr += '\\"';
            }
            else if(b === 0x0A) {
                escstr += "\\n";
            }
            else if(b === 0x09) {
                escstr += "\\t";
            }
            else {
                escstr += String.fromCodePoint(b);
            }
        }
        escstr += '"';
        return escstr;
    }

    private emitIRLiteral(exp: IRLiteralExpression): string {
        const ttag = exp.tag;

        if(ttag === IRExpressionTag.IRLiteralNoneExpression) {
            return "none";
        }
        else if(ttag === IRExpressionTag.IRLiteralBoolExpression) {
            return `${RUNTIME_NAMESPACE}::` + ((exp as IRLiteralBoolExpression).value ? "btrue" : "bfalse");
        }
        else if(ttag === IRExpressionTag.IRLiteralNatExpression) {
            return `${(exp as IRLiteralNatExpression).value}_n`;
        }
        else if(ttag === IRExpressionTag.IRLiteralIntExpression) {
            return `${(exp as IRLiteralIntExpression).value}_i`;
        }
        else if(ttag === IRExpressionTag.IRLiteralChkNatExpression) {
            const nval = BigInt((exp as IRLiteralChkNatExpression).value);
            if(nval <= MAX_SAFE_NAT) {
                return `${(exp as IRLiteralChkNatExpression).value}_N`;
            }
            else {
                assert(false, `CPPEmitter: need to do bit shift construction for (really big) safe nat -- ${(exp as IRLiteralChkNatExpression).value}`);
            }
        }
        else if(ttag === IRExpressionTag.IRLiteralChkIntExpression) {
            const ival = BigInt((exp as IRLiteralChkIntExpression).value);
            if(MIN_SAFE_INT <= ival && ival <= MAX_SAFE_INT) {
                return `${(exp as IRLiteralChkIntExpression).value}_I`;
            }
            else {
                assert(false, `CPPEmitter: need to do bit shift construction for (really big) safe int -- ${(exp as IRLiteralChkIntExpression).value}`);
            }
        }
        else if(ttag === IRExpressionTag.IRLiteralRationalExpression) {
            assert(false, "Rationals are currently unsupported in CPPEmitter");
        }
        else if(ttag === IRExpressionTag.IRLiteralFloatExpression) {
            return `${(exp as IRLiteralFloatExpression).value}_f`;
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
            return `${RUNTIME_NAMESPACE}::Complex(${(exp as IRLiteralComplexExpression).real}, ${(exp as IRLiteralComplexExpression).imaginary})`;
        }
        else if(ttag === IRExpressionTag.IRLiteralByteBufferExpression) {
            assert(false, "ByteBuffers are currently unsupported in CPPEmitter");
        }
        else if(ttag === IRExpressionTag.IRLiteralUUIDv4Expression) {
            const bytes = (exp as IRLiteralUUIDv4Expression).bytes.map((b) => `0x${b.toString(16).padStart(2, '0')}`).join(", ");
            return `${RUNTIME_NAMESPACE}::UUIDv4(${bytes})`;
        }
        else if(ttag === IRExpressionTag.IRLiteralUUIDv7Expression) {
            const bytes = (exp as IRLiteralUUIDv7Expression).bytes.map((b) => `0x${b.toString(16).padStart(2, '0')}`).join(", ");
            return `${RUNTIME_NAMESPACE}::UUIDv7(${bytes})`;
        }
        else if(ttag === IRExpressionTag.IRLiteralSHAContentHashExpression) {
            const bytes = (exp as IRLiteralSHAContentHashExpression).bytes.map((b) => `0x${b.toString(16).padStart(2, '0')}`).join(", ");
            return `${RUNTIME_NAMESPACE}::SHAContentHash(${bytes})`;
        }
        else if(ttag === IRExpressionTag.IRLiteralTZDateTimeExpression) {
            const dtinfo = (exp as IRLiteralTZDateTimeExpression);
            return `${RUNTIME_NAMESPACE}::TZDateTime({${dtinfo.date.year}, ${dtinfo.date.month}, ${dtinfo.date.day}}, {${dtinfo.time.hour}, ${dtinfo.time.minute}, ${dtinfo.time.second}}, "${dtinfo.timezone}");`;
        }
        else if(ttag === IRExpressionTag.IRLiteralTAITimeExpression) {
            const taiinfo = (exp as IRLiteralTAITimeExpression);
            return `${RUNTIME_NAMESPACE}::TAITime({${taiinfo.date.year}, ${taiinfo.date.month}, ${taiinfo.date.day}}, {${taiinfo.time.hour}, ${taiinfo.time.minute}, ${taiinfo.time.second}});`;
        }
        else if(ttag === IRExpressionTag.IRLiteralPlainDateExpression) {
            const pdate = (exp as IRLiteralPlainDateExpression);
            return `${RUNTIME_NAMESPACE}::PlainDate({${pdate.date.year}, ${pdate.date.month}, ${pdate.date.day}})`;
        }
        else if(ttag === IRExpressionTag.IRLiteralPlainTimeExpression) {
            const ptime = (exp as IRLiteralPlainTimeExpression);
            return `${RUNTIME_NAMESPACE}::PlainTime({${ptime.time.hour}, ${ptime.time.minute}, ${ptime.time.second}})`;
        }
        else if(ttag === IRExpressionTag.IRLiteralLogicalTimeExpression) {
            const ltime = (exp as IRLiteralLogicalTimeExpression);
            return `${RUNTIME_NAMESPACE}::LogicalTime(${ltime.ticks})`;
        }
        else if(ttag === IRExpressionTag.IRLiteralISOTimeStampExpression) {
            const isotimestamp = (exp as IRLiteralISOTimeStampExpression);
            return `${RUNTIME_NAMESPACE}::ISOTimeStamp({${isotimestamp.date.year}, ${isotimestamp.date.month}, ${isotimestamp.date.day}}, {${isotimestamp.time.hour}, ${isotimestamp.time.minute}, ${isotimestamp.time.second}}, ${isotimestamp.milliseconds})`;
        }
        else if(ttag === IRExpressionTag.IRLiteralDeltaDateTimeExpression) {
            const ddtexp = (exp as IRLiteralDeltaDateTimeExpression);
            return `${RUNTIME_NAMESPACE}::DeltaDateTime('${ddtexp.sign}', {${ddtexp.deltadate.years}, ${ddtexp.deltadate.months}, ${ddtexp.deltadate.days}}, {${ddtexp.deltatime.hours}, ${ddtexp.deltatime.minutes}, ${ddtexp.deltatime.seconds}})`;
        }
        else if(ttag === IRExpressionTag.IRLiteralDeltaISOTimeStampExpression) {
            const itsexp = (exp as IRLiteralDeltaISOTimeStampExpression);
            return `${RUNTIME_NAMESPACE}::DeltaISOTimeStamp('${itsexp.sign}', {${itsexp.deltadate.years}, ${itsexp.deltadate.months}, ${itsexp.deltadate.days}}, {${itsexp.deltatime.hours}, ${itsexp.deltatime.minutes}, ${itsexp.deltatime.seconds}}, ${itsexp.deltamilliseconds})`;
        }
        else if(ttag === IRExpressionTag.IRLiteralDeltaSecondsExpression) {
            const dsexp = (exp as IRLiteralDeltaSecondsExpression);
            return `${RUNTIME_NAMESPACE}::DeltaSeconds('${dsexp.sign}', ${dsexp.seconds})`;
        }
        else if(ttag === IRExpressionTag.IRLiteralDeltaLogicalTimeExpression) {
            const dltexp = (exp as IRLiteralDeltaLogicalTimeExpression);
            return `${RUNTIME_NAMESPACE}::DeltaLogicalTime('${dltexp.sign}', ${dltexp.ticks})`;
        }
        else if(ttag === IRExpressionTag.IRLiteralUnicodeRegexExpression) {
            return `${RUNTIME_NAMESPACE}::g_regexs[${(exp as IRLiteralUnicodeRegexExpression).regexID}]`;
        }
        else if(ttag === IRExpressionTag.IRLiteralCRegexExpression) {
            return `${RUNTIME_NAMESPACE}::g_regexs[${(exp as IRLiteralCRegexExpression).regexID}]`;
        }
        else if(ttag === IRExpressionTag.IRLiteralByteExpression) {
            const b = (exp as IRLiteralByteExpression).value;
            return `${RUNTIME_NAMESPACE}::Byte(0x${b.toString(16).padStart(2, '0')})`;
        }
        else if(ttag === IRExpressionTag.IRLiteralCCharExpression) {
            const ccv = (exp as IRLiteralCCharExpression).value;
            return `${RUNTIME_NAMESPACE}::CChar('${String.fromCodePoint(ccv)}')`;
        }
        else if(ttag === IRExpressionTag.IRLiteralUnicodeCharExpression) {
            const ucv = (exp as IRLiteralUnicodeCharExpression).value;
            return (31 < ucv && ucv < 127) ? `${RUNTIME_NAMESPACE}::UnicodeChar('${String.fromCodePoint(ucv)}')` : `${RUNTIME_NAMESPACE}::UnicodeChar(${ucv})`;
        }
        else if(ttag === IRExpressionTag.IRLiteralCStringExpression) {
            const cstr = (exp as IRLiteralStringExpression).bytes;
            if(cstr.length <= 24) {
                return `${RUNTIME_NAMESPACE}::CString::literal(${this.escapeLiteralCString(cstr)})`;
            }
            else {
                assert(false, "CPPEmitter: need to do heap allocation for long cstrings");
            }
        }
        else if(ttag === IRExpressionTag.IRLiteralStringExpression) {
            assert(false, "CPPEmitter: need to handle full Unicode string literals");
        }
        else if(ttag === IRExpressionTag.IRLiteralFormatStringExpression) {
            //TODO: probably represent this natively as a Bosque List<FormatArgComponent>
            assert(false, "CPPEmitter: need to handle format String literals");
        }
        else if(ttag === IRExpressionTag.IRLiteralFormatCStringExpression) {
            //TODO: probably represent this natively as a Bosque List<FormatArgComponent>
            assert(false, "CPPEmitter: need to handle format CString literals");
        }
        else if(ttag === IRExpressionTag.IRLiteralTypedExpression) {
            const ilte = exp as IRLiteralTypedExpression
            const cce = TransformCPPNameManager.convertTypeKey(ilte.constype.tkeystr);

            return `${cce}(${this.emitIRLiteral(ilte.value as IRLiteralExpression)})`;
        }
        else if(ttag === IRExpressionTag.IRLiteralTypedStringExpression) {
            assert(false, "CPPEmitter: need to handle full Unicode string literals")
        }
        else if(ttag === IRExpressionTag.IRLiteralTypedCStringExpression) {
            const ilte = exp as IRLiteralTypedCStringExpression
            const cce = TransformCPPNameManager.convertTypeKey(ilte.constype.tkeystr);

            if(ilte.bytes.length <= 24) {
                return `${cce}(${RUNTIME_NAMESPACE}::CString::literal(${this.escapeLiteralCString(ilte.bytes)}))`;
            }
            else {
                assert(false, "CPPEmitter: need to do heap allocation for long cstrings");
            }
        }
        else if(ttag === IRExpressionTag.IRLiteralTypedFormatStringExpression) {
            //TODO: probably represent this natively as a Bosque List<FormatArgComponent>
            assert(false, "CPPEmitter: need to handle format String literals");
        }
        else if(ttag === IRExpressionTag.IRLiteralTypedFormatCStringExpression) {
            //TODO: probably represent this natively as a Bosque List<FormatArgComponent>
            assert(false, "CPPEmitter: need to handle format CString literals");
        }
        else {
            assert(false, `CPPEmitter: Unsupported IR literal type -- ${exp.constructor.name}`);
        }
    }

    private emitIRImmediateExpression(exp: IRImmediateExpression): string {
        if(exp instanceof IRLiteralExpression) {
            return this.emitIRLiteral(exp);
        }
        else {
            const ttag = exp.tag;
            
            if(ttag === IRExpressionTag.IRAccessNamespaceConstantExpression) {
                xxxx;
            }
            else if(ttag === IRExpressionTag.IRAccessStaticFieldExpression) {
                xxxx;
            }
            else if (ttag === IRExpressionTag.IRAccessParameterVariableExpression) {
                xxxx;
            }
            else if(ttag === IRExpressionTag.IRAccessLocalVariableExpression) {
                xxxx;
            }
            else if(ttag === IRExpressionTag.IRAccessCapturedVariableExpression) {
                xxxx;
            }
            else {
                assert(false, `CPPEmitter: Unsupported IR immediate expression type -- ${exp.constructor.name}`);
            }
        }
    }

    private emitExpression(exp: IRExpression): string {
        const ttag = exp.tag;

        if(exp instanceof IRImmediateExpression) {
            return this.emitIRImmediateExpression(exp);
        }
        else {
            const ttag = exp.tag;
            
            if(ttag === IRExpressionTag.IRAccessEnvHasExpression) {
                const iehe = exp as IRAccessEnvHasExpression;
                return `${this.cppTaskType}::asRepr(&${RUNTIME_NAMESPACE}::tl_info)->environment.has(${RUNTIME_NAMESPACE}::CString::literal(${this.escapeLiteralCString(iehe.keybytes)}))`;
            }
            else if(ttag === IRExpressionTag.IRAccessEnvGetExpression) {
                const iege = exp as IRAccessEnvGetExpression;
                const mname = TransformCPPNameManager.generateNameForUnionMember(iege.oftype.tkeystr);
                return `${this.cppTaskType}::asRepr(&${RUNTIME_NAMESPACE}::tl_info)->environment.tryGetEntry(${RUNTIME_NAMESPACE}::CString::literal(${this.escapeLiteralCString(iege.keybytes)}))->value.${mname}`;
            }
            else if(ttag === IRExpressionTag.IRAccessEnvTryGetExpression) {
                const iege = exp as IRAccessEnvTryGetExpression;
                const mname = TransformCPPNameManager.generateNameForUnionMember(iege.oftype.tkeystr);

                const chkstr = `${this.cppTaskType}::asRepr(&${RUNTIME_NAMESPACE}::tl_info)->environment.has(${RUNTIME_NAMESPACE}::CString::literal(${this.escapeLiteralCString(iege.keybytes)}))`;
                const gettype = `${this.cppTaskType}::asRepr(&${RUNTIME_NAMESPACE}::tl_info)->environment.get(${RUNTIME_NAMESPACE}::CString::literal(${this.escapeLiteralCString(iege.keybytes)}))->typeinfo`;
                const getstr = `${this.cppTaskType}::asRepr(&${RUNTIME_NAMESPACE}::tl_info)->environment.get(${RUNTIME_NAMESPACE}::CString::literal(${this.escapeLiteralCString(iege.keybytes)}))->value.${mname}`;

                const makeopt = `${RUNTIME_NAMESPACE}::Option<${TransformCPPNameManager.convertTypeKey(iege.oftype.tkeystr)}>::makeSome(${gettype}, ${getstr})`;
                const makenone = `${RUNTIME_NAMESPACE}::Option<${TransformCPPNameManager.convertTypeKey(iege.oftype.tkeystr)}>::optnone`;
                return `(${chkstr} ? ${makeopt} : ${makenone})`;
            }
            else if(ttag === IRExpressionTag.IRTaskAccessIDExpression) {
                return `${RUNTIME_NAMESPACE}::tl_info.taskid`;
            }
            else if(ttag === IRExpressionTag.IRTaskAccessParentIDExpression) {
                return `(${RUNTIME_NAMESPACE}::tl_info.parent !== nullptr ? ${RUNTIME_NAMESPACE}::tl_info.parent->taskid : 0)`;
            }
            else {
                assert(false, `CPPEmitter: Unsupported IR expression type -- ${exp.constructor.name}`);
            }
        }
    }
}

export {
    CPPEmitter
};
