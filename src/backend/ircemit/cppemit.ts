import { TransformCPPNameManager } from "./namemgr.js";
import { TypeInfoManager } from "./typeinfomgr.js";

import { MAX_SAFE_INT, MAX_SAFE_NAT, MIN_SAFE_INT } from "../../frontend/assembly.js";
import { IRExpression, IRExpressionTag, IRLiteralChkIntExpression, IRLiteralChkNatExpression, IRLiteralBoolExpression, IRLiteralByteExpression, IRLiteralCCharExpression, IRLiteralComplexExpression, IRLiteralCRegexExpression, IRLiteralDeltaDateTimeExpression, IRLiteralDeltaISOTimeStampExpression, IRLiteralDeltaLogicalTimeExpression, IRLiteralDeltaSecondsExpression, IRLiteralFloatExpression, IRLiteralIntExpression, IRLiteralISOTimeStampExpression, IRLiteralLogicalTimeExpression, IRLiteralNatExpression, IRLiteralPlainDateExpression, IRLiteralPlainTimeExpression, IRLiteralSHAContentHashExpression, IRLiteralStringExpression, IRLiteralTAITimeExpression, IRLiteralTZDateTimeExpression, IRLiteralUnicodeCharExpression, IRLiteralUnicodeRegexExpression, IRLiteralUUIDv4Expression, IRLiteralUUIDv7Expression, IRLiteralExpression, IRImmediateExpression, IRLiteralTypedExpression, IRLiteralTypedCStringExpression, IRAccessEnvHasExpression, IRAccessEnvGetExpression, IRAccessEnvTryGetExpression, IRAccessConstantExpression, IRAccessParameterVariableExpression, IRAccessLocalVariableExpression, IRAccessCapturedVariableExpression, IRAccessEnumExpression, IRAccessTempVariableExpression, IRSimpleExpression, IRAtomicStatement, IRStatement, IRStatementTag, IRPrefixNotOpExpression, IRPrefixPlusOpExpression, IRPrefixNegateOpExpression, IRBinAddExpression, IRBinSubExpression, IRBinMultExpression, IRBinDivExpression, IRNumericEqExpression, IRNumericNeqExpression, IRNumericLessExpression, IRNumericLessEqExpression, IRNumericGreaterExpression, IRNumericGreaterEqExpression, IRLogicAndExpression, IRLogicOrExpression, IRReturnValueSimpleStatement, IRErrorAdditionBoundsCheckStatement, IRErrorSubtractionBoundsCheckStatement, IRErrorMultiplicationBoundsCheckStatement, IRErrorDivisionByZeroCheckStatement, IRAbortStatement, IRVariableDeclarationStatement, IRVariableInitializationStatement, IRTempAssignExpressionStatement, IRTypeDeclInvariantCheckStatement, IRDebugStatement, IRAccessTypeDeclValueExpression, IRConstructSafeTypeDeclExpression, IRChkLogicImpliesShortCircuitStatement, IRPreconditionCheckStatement, IRPostconditionCheckStatement, IRVariableInitializationDirectInvokeStatement, IRLogicSimpleConditionalExpression, IRLogicConditionalStatement, IRAssertStatement, IRValidateStatement, IRBody, IRBuiltinBody, IRStandardBody, IRHoleBody } from "../irdefs/irbody.js";
import { IRAbstractNominalTypeDecl, IRAssembly, IRConstantDecl, IREnumTypeDecl, IRInvariantDecl, IRInvokeDecl, IRInvokeParameterDecl, IRTypedeclCStringDecl, IRTypedeclStringDecl, IRTypedeclTypeDecl, IRValidateDecl } from "../irdefs/irassembly.js";

import assert from "node:assert";
import { IRNominalTypeSignature, IRTypeSignature } from "../irdefs/irtype.js";

const RUNTIME_NAMESPACE = "ᐸRuntimeᐳ";
const CLOSURE_CAPTURE_NAME = "ᐸclosureᐳ";

//Make sure to keep these in sync with runtime limits
const SMALL_CSTRING_MAX_SIZE = 15;
const SMALL_STRING_MAX_SIZE = 7;

class CPPEmitter {
    readonly irasm: IRAssembly;
    readonly typeInfoManager: TypeInfoManager;

    //The C++ TaskInfoRepr<U> for accessing the global info for the task we are emitting
    private cppTaskType: string | undefined = undefined;

    constructor(irasm: IRAssembly, typeInfoManager: TypeInfoManager) {
        this.irasm = irasm;
        this.typeInfoManager = typeInfoManager;
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

    private escapeLiteralString(cstrbytes: number[]): string {
        let escstr = 'U"';
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
                if(32 <= b && b < 127) {
                    escstr += String.fromCodePoint(b);
                }
                else {
                    assert(false, "CPPEmitter: need to do unicode escape for non-ascii characters in string literals");
                }
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
            return (exp as IRLiteralBoolExpression).value ? "TRUE" : "FALSE";
        }
        else if(ttag === IRExpressionTag.IRLiteralNatExpression) {
            const ll = (exp as IRLiteralNatExpression).value;
            return `${ll.startsWith("+") ? ll.slice(1) : ll}_n`;
        }
        else if(ttag === IRExpressionTag.IRLiteralIntExpression) {
            const ll = (exp as IRLiteralIntExpression).value;
            return `${ll.startsWith("+") ? ll.slice(1) : ll}_i`;
        }
        else if(ttag === IRExpressionTag.IRLiteralChkNatExpression) {
            const ll = (exp as IRLiteralChkNatExpression).value;
            const nval = BigInt(ll.startsWith("+") ? ll.slice(1) : ll);
            if(nval <= MAX_SAFE_NAT) {
                return `${ll.startsWith("+") ? ll.slice(1) : ll}_N`;
            }
            else {
                assert(false, `CPPEmitter: need to do bit shift construction for (really big) safe nat -- ${(exp as IRLiteralChkNatExpression).value}`);
            }
        }
        else if(ttag === IRExpressionTag.IRLiteralChkIntExpression) {
            const ll = (exp as IRLiteralChkIntExpression).value;
            const ival = BigInt(ll.startsWith("+") ? ll.slice(1) : ll);
            if(MIN_SAFE_INT <= ival && ival <= MAX_SAFE_INT) {
                return `${ll.startsWith("+") ? ll.slice(1) : ll}_I`;
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
            return `${RUNTIME_NAMESPACE}::XComplex(${(exp as IRLiteralComplexExpression).real}, ${(exp as IRLiteralComplexExpression).imaginary})`;
        }
        else if(ttag === IRExpressionTag.IRLiteralByteBufferExpression) {
            //const bbexp = (exp as IRLiteralByteBufferExpression);
            assert(false, "CPPEmitter: need to handle byte buffer literals -- must be heap allocated");
        }
        else if(ttag === IRExpressionTag.IRLiteralUUIDv4Expression) {
            const bytes = (exp as IRLiteralUUIDv4Expression).bytes.map((b) => `0x${b.toString(16).padStart(2, '0')}`).join(", ");
            return `${RUNTIME_NAMESPACE}::XUUIDv4{${bytes}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralUUIDv7Expression) {
            const bytes = (exp as IRLiteralUUIDv7Expression).bytes.map((b) => `0x${b.toString(16).padStart(2, '0')}`).join(", ");
            return `${RUNTIME_NAMESPACE}::XUUIDv7{${bytes}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralSHAContentHashExpression) {
            const bytes = (exp as IRLiteralSHAContentHashExpression).bytes.map((b) => `0x${b.toString(16).padStart(2, '0')}`).join(", ");
            return `${RUNTIME_NAMESPACE}::XSHAContentHash{${bytes}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralTZDateTimeExpression) {
            const dtinfo = (exp as IRLiteralTZDateTimeExpression);
            return `${RUNTIME_NAMESPACE}::XTZDateTime{{${dtinfo.date.year}, ${dtinfo.date.month}, ${dtinfo.date.day}}, {${dtinfo.time.hour}, ${dtinfo.time.minute}, ${dtinfo.time.second}}, "${dtinfo.timezone}"};`;
        }
        else if(ttag === IRExpressionTag.IRLiteralTAITimeExpression) {
            const taiinfo = (exp as IRLiteralTAITimeExpression);
            return `${RUNTIME_NAMESPACE}::XTAITime{{${taiinfo.date.year}, ${taiinfo.date.month}, ${taiinfo.date.day}}, {${taiinfo.time.hour}, ${taiinfo.time.minute}, ${taiinfo.time.second}}};`;
        }
        else if(ttag === IRExpressionTag.IRLiteralPlainDateExpression) {
            const pdate = (exp as IRLiteralPlainDateExpression);
            return `${RUNTIME_NAMESPACE}::XPlainDate{{${pdate.date.year}, ${pdate.date.month}, ${pdate.date.day}}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralPlainTimeExpression) {
            const ptime = (exp as IRLiteralPlainTimeExpression);
            return `${RUNTIME_NAMESPACE}::XPlainTime{{${ptime.time.hour}, ${ptime.time.minute}, ${ptime.time.second}}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralLogicalTimeExpression) {
            const ltime = (exp as IRLiteralLogicalTimeExpression);
            return `${RUNTIME_NAMESPACE}::XLogicalTime{${ltime.ticks}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralISOTimeStampExpression) {
            const isotimestamp = (exp as IRLiteralISOTimeStampExpression);
            return `${RUNTIME_NAMESPACE}::XISOTimeStamp{{${isotimestamp.date.year}, ${isotimestamp.date.month}, ${isotimestamp.date.day}}, {${isotimestamp.time.hour}, ${isotimestamp.time.minute}, ${isotimestamp.time.second}}, ${isotimestamp.milliseconds}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralDeltaDateTimeExpression) {
            const ddtexp = (exp as IRLiteralDeltaDateTimeExpression);
            return `${RUNTIME_NAMESPACE}::XDeltaDateTime{'${ddtexp.sign}', {${ddtexp.deltadate.years}, ${ddtexp.deltadate.months}, ${ddtexp.deltadate.days}}, {${ddtexp.deltatime.hours}, ${ddtexp.deltatime.minutes}, ${ddtexp.deltatime.seconds}}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralDeltaISOTimeStampExpression) {
            const itsexp = (exp as IRLiteralDeltaISOTimeStampExpression);
            return `${RUNTIME_NAMESPACE}::XDeltaISOTimeStamp{'${itsexp.sign}', {${itsexp.deltadate.years}, ${itsexp.deltadate.months}, ${itsexp.deltadate.days}}, {${itsexp.deltatime.hours}, ${itsexp.deltatime.minutes}, ${itsexp.deltatime.seconds}}, ${itsexp.deltamilliseconds}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralDeltaSecondsExpression) {
            const dsexp = (exp as IRLiteralDeltaSecondsExpression);
            return `${RUNTIME_NAMESPACE}::XDeltaSeconds{'${dsexp.sign}', ${dsexp.seconds}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralDeltaLogicalTimeExpression) {
            const dltexp = (exp as IRLiteralDeltaLogicalTimeExpression);
            return `${RUNTIME_NAMESPACE}::XDeltaLogicalTime{'${dltexp.sign}', ${dltexp.ticks}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralUnicodeRegexExpression) {
            return `${RUNTIME_NAMESPACE}::g_regexs[${(exp as IRLiteralUnicodeRegexExpression).regexID}]`;
        }
        else if(ttag === IRExpressionTag.IRLiteralCRegexExpression) {
            return `${RUNTIME_NAMESPACE}::g_regexs[${(exp as IRLiteralCRegexExpression).regexID}]`;
        }
        else if(ttag === IRExpressionTag.IRLiteralByteExpression) {
            const b = (exp as IRLiteralByteExpression).value;
            return `${RUNTIME_NAMESPACE}::XByte{0x${b.toString(16).padStart(2, '0')}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralCCharExpression) {
            const ccv = (exp as IRLiteralCCharExpression).value;
            return `${RUNTIME_NAMESPACE}::XCChar{'${String.fromCodePoint(ccv)}'}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralUnicodeCharExpression) {
            const ucv = (exp as IRLiteralUnicodeCharExpression).value;
            return (31 < ucv && ucv < 127) ? `${RUNTIME_NAMESPACE}::XUnicodeChar{'${String.fromCodePoint(ucv)}'}` : `${RUNTIME_NAMESPACE}::XUnicodeChar{${ucv}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralCStringExpression) {
            const cstr = (exp as IRLiteralStringExpression).bytes;
            if(cstr.length <= SMALL_CSTRING_MAX_SIZE) {
                return `${RUNTIME_NAMESPACE}::XCString::smliteral(${this.escapeLiteralCString(cstr)})`;
            }
            else {
                assert(false, "CPPEmitter: need to do heap allocation for long cstrings");
            }
        }
        else if(ttag === IRExpressionTag.IRLiteralStringExpression) {
            const cstr = (exp as IRLiteralStringExpression).bytes;
            if(cstr.length <= SMALL_STRING_MAX_SIZE) {
                return `${RUNTIME_NAMESPACE}::XString::smliteral(${this.escapeLiteralString(cstr)})`;
            }
            else {
                assert(false, "CPPEmitter: need to do heap allocation for long strings");
            }
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

            if(ilte.bytes.length <= SMALL_CSTRING_MAX_SIZE) {
                return `${cce}(${RUNTIME_NAMESPACE}::XCString::smliteral(${this.escapeLiteralCString(ilte.bytes)}))`;
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
            
            if(ttag === IRExpressionTag.IRAccessConstantExpression) {
                return TransformCPPNameManager.generateNameForConstantKey((exp as IRAccessConstantExpression).constkey) + "()";
            }
            else if(ttag === IRExpressionTag.IRAccessEnumExpression) {
                return TransformCPPNameManager.generateNameForEnumKey((exp as IRAccessEnumExpression).tkey, (exp as IRAccessEnumExpression).membername);
            }
            else if (ttag === IRExpressionTag.IRAccessParameterVariableExpression) {
                return TransformCPPNameManager.convertIdentifier((exp as IRAccessParameterVariableExpression).pname);
            }
            else if(ttag === IRExpressionTag.IRAccessLocalVariableExpression) {
                return TransformCPPNameManager.convertIdentifier((exp as IRAccessLocalVariableExpression).vname);
            }
            else if(ttag === IRExpressionTag.IRAccessCapturedVariableExpression) {
                const cve = exp as IRAccessCapturedVariableExpression;
                return `${CLOSURE_CAPTURE_NAME}.scope${cve.scope}.${TransformCPPNameManager.convertIdentifier(cve.vname)}`;
            }
            else if(ttag === IRExpressionTag.IRAccessTempVariableExpression) {
                return TransformCPPNameManager.convertIdentifier((exp as IRAccessTempVariableExpression).vname);
            }
            else {
                assert(false, `CPPEmitter: Unsupported IR immediate expression type -- ${exp.constructor.name}`);
            }
        }
    }

    private emitIRSimpleExpression(exps: IRSimpleExpression, toplevel: boolean): string {
        if(exps instanceof IRImmediateExpression) {
            return this.emitIRImmediateExpression(exps);
        }
        else {
            const ttag = exps.tag;

            let bstr = "";
            if(ttag === IRExpressionTag.IRAccessTypeDeclValueExpression) {
                const cexp = exps as IRAccessTypeDeclValueExpression;
                bstr = `${this.emitIRSimpleExpression(cexp.exp, false)}.value`;
            }
            else if(ttag === IRExpressionTag.IRConstructSafeTypeDeclExpression) {
                const cexp = exps as IRConstructSafeTypeDeclExpression;
                bstr = `${TransformCPPNameManager.generateNameForConstructor(cexp.constype.tkeystr)}(${this.emitIRSimpleExpression(cexp.value, toplevel)})`;
            }
            else if(ttag === IRExpressionTag.IRPrefixNotOpExpression) {
                bstr = `!${this.emitIRSimpleExpression((exps as IRPrefixNotOpExpression).exp, false)}`;
            }
            else if(ttag === IRExpressionTag.IRPrefixPlusOpExpression) {
                bstr = `${this.emitIRSimpleExpression((exps as IRPrefixPlusOpExpression).exp, toplevel)}`;
            }
            else if(ttag === IRExpressionTag.IRPrefixNegateOpExpression) {
                bstr = `-${this.emitIRSimpleExpression((exps as IRPrefixNegateOpExpression).exp, false)}`;
            }
            else if(ttag === IRExpressionTag.IRBinAddExpression) {
                const bexp = exps as IRBinAddExpression;
                bstr = `${this.emitIRSimpleExpression(bexp.left, false)} + ${this.emitIRSimpleExpression(bexp.right, false)}`;
            }
            else if(ttag === IRExpressionTag.IRBinSubExpression) {
                const bexp = exps as IRBinSubExpression;
                bstr = `${this.emitIRSimpleExpression(bexp.left, false)} - ${this.emitIRSimpleExpression(bexp.right, false)}`;
            }
            else if(ttag === IRExpressionTag.IRBinMultExpression) {
                const bexp = exps as IRBinMultExpression;
                bstr = `${this.emitIRSimpleExpression(bexp.left, false)} * ${this.emitIRSimpleExpression(bexp.right, false)}`;
            }
            else if(ttag === IRExpressionTag.IRBinDivExpression) {
                const bexp = exps as IRBinDivExpression;
                bstr = `${this.emitIRSimpleExpression(bexp.left, false)} / ${this.emitIRSimpleExpression(bexp.right, false)}`;
            }
            else if(ttag === IRExpressionTag.IRNumericEqExpression) {
                const bexp = exps as IRNumericEqExpression;
                bstr = `${this.emitIRSimpleExpression(bexp.left, false)} == ${this.emitIRSimpleExpression(bexp.right, false)}`;
            }
            else if(ttag === IRExpressionTag.IRNumericNeqExpression) {
                const bexp = exps as IRNumericNeqExpression;
                bstr = `${this.emitIRSimpleExpression(bexp.left, false)} != ${this.emitIRSimpleExpression(bexp.right, false)}`;
            }
            else if(ttag === IRExpressionTag.IRNumericLessExpression) {
                const bexp = exps as IRNumericLessExpression;
                bstr = `${this.emitIRSimpleExpression(bexp.left, false)} < ${this.emitIRSimpleExpression(bexp.right, false)}`;
            }
            else if(ttag === IRExpressionTag.IRNumericLessEqExpression) {
                const bexp = exps as IRNumericLessEqExpression;
                bstr = `${this.emitIRSimpleExpression(bexp.left, false)} <= ${this.emitIRSimpleExpression(bexp.right, false)}`;
            }
            else if(ttag === IRExpressionTag.IRNumericGreaterExpression) {
                const bexp = exps as IRNumericGreaterExpression;
                bstr = `${this.emitIRSimpleExpression(bexp.left, false)} > ${this.emitIRSimpleExpression(bexp.right, false)}`;
            }
            else if(ttag === IRExpressionTag.IRNumericGreaterEqExpression) {
                const bexp = exps as IRNumericGreaterEqExpression;
                bstr = `${this.emitIRSimpleExpression(bexp.left, false)} >= ${this.emitIRSimpleExpression(bexp.right, false)}`;
            }
            else if(ttag === IRExpressionTag.IRLogicAndExpression) {
                const bexp = exps as IRLogicAndExpression;
                const args = bexp.args.map((arg) => this.emitIRSimpleExpression(arg, false));
                bstr = args.join(" & ");
            }
            else if(ttag === IRExpressionTag.IRLogicOrExpression) {
                const bexp = exps as IRLogicOrExpression;
                const args = bexp.args.map((arg) => this.emitIRSimpleExpression(arg, false));
                bstr = args.join(" | ");
            }
            else if(ttag === IRExpressionTag.IRLogicSimpleConditionalExpression) {
                const cexp = exps as IRLogicSimpleConditionalExpression;
                bstr = `(${this.emitIRSimpleExpression(cexp.condition, false)} ? ${this.emitIRSimpleExpression(cexp.trueexp, false)} : ${this.emitIRSimpleExpression(cexp.falseexp, false)})`;
            }
            else {
                assert(false, `CPPEmitter: Unsupported IR simple expression type -- ${exps.constructor.name}`);
            }

            return toplevel ? bstr : `(${bstr})`;
        }
    }

    private emitExpression(exp: IRExpression, toplevel: boolean): string {
        if(exp instanceof IRSimpleExpression) {
            return this.emitIRSimpleExpression(exp, toplevel);
        }
        else {
            const ttag = exp.tag;
            
            if(ttag === IRExpressionTag.IRAccessEnvHasExpression) {
                const iehe = exp as IRAccessEnvHasExpression;
                return `${this.cppTaskType}::asRepr(&${RUNTIME_NAMESPACE}::tl_info)->environment.has(${RUNTIME_NAMESPACE}::XCString::gliteral(${this.escapeLiteralCString(iehe.keybytes)}))`;
            }
            else if(ttag === IRExpressionTag.IRAccessEnvGetExpression) {
                const iege = exp as IRAccessEnvGetExpression;
                const mname = TransformCPPNameManager.generateNameForUnionMember(iege.oftype.tkeystr);
                return `${this.cppTaskType}::asRepr(&${RUNTIME_NAMESPACE}::tl_info)->environment.tryGetEntry(${RUNTIME_NAMESPACE}::XCString::gliteral(${this.escapeLiteralCString(iege.keybytes)}))->value.${mname}`;
            }
            else if(ttag === IRExpressionTag.IRAccessEnvTryGetExpression) {
                const iege = exp as IRAccessEnvTryGetExpression;
                const mname = TransformCPPNameManager.generateNameForUnionMember(iege.oftype.tkeystr);

                const chkstr = `${this.cppTaskType}::asRepr(&${RUNTIME_NAMESPACE}::tl_info)->environment.has(${RUNTIME_NAMESPACE}::XCString::gliteral(${this.escapeLiteralCString(iege.keybytes)}))`;
                const gettype = `${this.cppTaskType}::asRepr(&${RUNTIME_NAMESPACE}::tl_info)->environment.get(${RUNTIME_NAMESPACE}::XCString::gliteral(${this.escapeLiteralCString(iege.keybytes)}))->typeinfo`;
                const getstr = `${this.cppTaskType}::asRepr(&${RUNTIME_NAMESPACE}::tl_info)->environment.get(${RUNTIME_NAMESPACE}::XCString::gliteral(${this.escapeLiteralCString(iege.keybytes)}))->value.${mname}`;

                const makeopt = `${RUNTIME_NAMESPACE}::XOption<${TransformCPPNameManager.convertTypeKey(iege.oftype.tkeystr)}>::makeSome(${gettype}, ${getstr})`;
                const makenone = `${RUNTIME_NAMESPACE}::XOption<${TransformCPPNameManager.convertTypeKey(iege.oftype.tkeystr)}>::optnone`;
                return `(${chkstr} ? ${makeopt} : ${makenone})`;
            }
            else if(ttag === IRExpressionTag.IRTaskAccessIDExpression) {
                return `${RUNTIME_NAMESPACE}::tl_info.taskid`;
            }
            else if(ttag === IRExpressionTag.IRTaskAccessParentIDExpression) {
                return `(${RUNTIME_NAMESPACE}::tl_info.parent !== nullptr ? ${RUNTIME_NAMESPACE}::tl_info.parent->taskid : ${RUNTIME_NAMESPACE}::XUUIDv4::nil())`;
            }
            
            else if(ttag === IRExpressionTag.IRInvokeSimpleExpression) {
                assert(false, "CPPEmitter: need to implement simple invoke expression");
            }
            else if(ttag === IRExpressionTag.IRInvokeVirtualSimpleExpression) {
                assert(false, "CPPEmitter: need to implement virtual simple invoke expression");
            }
            else if(ttag === IRExpressionTag.IRInvokeSimpleWithImplicitsExpression) {
                assert(false, "CPPEmitter: need to implement simple with implicits invoke expression");
            }
            else if(ttag === IRExpressionTag.IRInvokeVirtualWithImplicitsExpression) {
                assert(false, "CPPEmitter: need to implement virtual with implicits invoke expression");
            }
            else {
                assert(false, `CPPEmitter: Unsupported IR expression type -- ${exp.constructor.name}`);
            }
        }
    }

    private emitAtomicStatement(stmt: IRAtomicStatement): string {
        const ttag = stmt.tag;

        if(ttag === IRStatementTag.IRNopStatement) {
            return ";";
        }
        else if(ttag === IRStatementTag.IRTempAssignExpressionStatement) {
            const tase = stmt as IRTempAssignExpressionStatement;
            
            const vdecltype = this.typeInfoManager.emitTypeAsStd(tase.ttype.tkeystr);
            const wval = this.emitExpression(tase.rhs, true);
            return `${vdecltype} ${TransformCPPNameManager.convertIdentifier(tase.tname)} = ${wval};`
        }
        else if(ttag === IRStatementTag.IRTempAssignStdInvokeStatement) {
            assert(false, "CPPEmitter: need to implement temp assign standard invoke expression");
        }
        else if(ttag === IRStatementTag.IRTempAssignRefInvokeStatement) {
            assert(false, "CPPEmitter: need to implement temp assign invoke with references expression");
            //TODO: but since we use by-ref passing it is actually just the same as the temp assign standard invoke
        }
        else if(ttag === IRStatementTag.IRVariableDeclarationStatement) {
            const vdeclstmt = stmt as IRVariableDeclarationStatement;

            const vdecltype = this.typeInfoManager.emitTypeAsStd(vdeclstmt.vtype.tkeystr);
            return `${vdecltype} ${TransformCPPNameManager.convertIdentifier(vdeclstmt.vname)};`
        }
        else if(ttag === IRStatementTag.IRVariableInitializationStatement) {
            const vistmt = stmt as IRVariableInitializationStatement;

            const vdecltype = this.typeInfoManager.emitTypeAsStd(vistmt.vtype.tkeystr);
            const wval = this.emitIRSimpleExpression(vistmt.initexp, true);
            return `${vdecltype} ${TransformCPPNameManager.convertIdentifier(vistmt.vname)} = ${wval};`
        }
        else if(ttag === IRStatementTag.IRVariableInitializationDirectInvokeStatement) {
            const vistmt = stmt as IRVariableInitializationDirectInvokeStatement;

            const vdecltype = this.typeInfoManager.emitTypeAsStd(vistmt.vtype.tkeystr);
            const wval = this.emitExpression(vistmt.initexp, true);
            return `${vdecltype} ${TransformCPPNameManager.convertIdentifier(vistmt.vname)} = ${wval};`
        }
        else if(ttag === IRStatementTag.IRReturnVoidSimpleStatement) {
            return "return;";
        }
        else if(ttag === IRStatementTag.IRReturnValueSimpleStatement) {
            const ires = stmt as IRReturnValueSimpleStatement;
            return `return ${this.emitIRSimpleExpression(ires.retexp, true)};`;
        }
        else if(ttag === IRStatementTag.IRReturnDirectInvokeStatement) {
            const ires = stmt as IRReturnValueSimpleStatement;
            return `return ${this.emitExpression(ires.retexp, true)};`;
        }
        else if(ttag === IRStatementTag.IRChkLogicImpliesShortCircuitStatement) {
            const icliss = stmt as IRChkLogicImpliesShortCircuitStatement;
            const bb = this.emitStatementList(icliss.rstmts, undefined, [`${TransformCPPNameManager.convertIdentifier(icliss.tvar)} = ${this.emitIRSimpleExpression(icliss.rexp, true)};`], undefined);
            return `Bool ${TransformCPPNameManager.convertIdentifier(icliss.tvar)} = TRUE; if(${this.emitIRSimpleExpression(icliss.lhs, true)}) ${bb}`;
        }
        else if(ttag === IRStatementTag.IRLogicConditionalStatement) {
            const ilcs = stmt as IRLogicConditionalStatement;
            const tb = this.emitStatementList(ilcs.truestmt, undefined, [`${TransformCPPNameManager.convertIdentifier(ilcs.tvar)} = ${this.emitIRSimpleExpression(ilcs.trueexp, true)};`], undefined);
            const fb = this.emitStatementList(ilcs.falsestmt, undefined, [`${TransformCPPNameManager.convertIdentifier(ilcs.tvar)} = ${this.emitIRSimpleExpression(ilcs.falseexp, true)};`], undefined);
            return `${this.typeInfoManager.emitTypeAsStd(ilcs.ttype.tkeystr)} ${TransformCPPNameManager.convertIdentifier(ilcs.tvar)}; if(${this.emitIRSimpleExpression(ilcs.condition, true)}) ${tb} else ${fb}`;
        }
        else if(ttag === IRStatementTag.IRErrorAdditionBoundsCheckStatement) {
            const ieabc = stmt as IRErrorAdditionBoundsCheckStatement;
            return `${RUNTIME_NAMESPACE}::X${ieabc.optypechk}::checkOverflowAddition(${this.emitIRSimpleExpression(ieabc.left, true)}, ${this.emitIRSimpleExpression(ieabc.right, true)}, "${ieabc.file}", ${ieabc.sinfo.line});`;
        }
        else if(ttag === IRStatementTag.IRErrorSubtractionBoundsCheckStatement) {
            const iesbc = stmt as IRErrorSubtractionBoundsCheckStatement;
            return `${RUNTIME_NAMESPACE}::X${iesbc.optypechk}::checkOverflowSubtraction(${this.emitIRSimpleExpression(iesbc.left, true)}, ${this.emitIRSimpleExpression(iesbc.right, true)}, "${iesbc.file}", ${iesbc.sinfo.line});`;
        }
        else if(ttag === IRStatementTag.IRErrorMultiplicationBoundsCheckStatement) {
            const iembc = stmt as IRErrorMultiplicationBoundsCheckStatement;
            return `${RUNTIME_NAMESPACE}::X${iembc.optypechk}::checkOverflowMultiplication(${this.emitIRSimpleExpression(iembc.left, true)}, ${this.emitIRSimpleExpression(iembc.right, true)}, "${iembc.file}", ${iembc.sinfo.line});`;
        }
        else if(ttag === IRStatementTag.IRErrorDivisionByZeroCheckStatement) {
            const iedzbc = stmt as IRErrorDivisionByZeroCheckStatement;
            return `${RUNTIME_NAMESPACE}::X${iedzbc.optypechk}::checkDivisionByZero(${this.emitIRSimpleExpression(iedzbc.left, true)}, "${iedzbc.file}", ${iedzbc.sinfo.line});`;
        }
        else if(ttag === IRStatementTag.IRTypeDeclInvariantCheckStatement) {
            const itdics = stmt as IRTypeDeclInvariantCheckStatement;

            const invchk = `${TransformCPPNameManager.generateNameForInvariantFunction(itdics.tkey, itdics.invariantidx)}(${this.emitIRSimpleExpression(itdics.targetValue, true)}, "${itdics.file}", ${itdics.sinfo.line})`
            const dtag = itdics.diagnosticTag !== null ? `"${itdics.diagnosticTag}"` : "nullptr";
            return `ᐸRuntimeᐳ::bsq_invariant(${invchk}, "${itdics.file}", ${itdics.sinfo.line}, ${dtag}, "Failed Invariant");`;
        }
        else if(ttag === IRStatementTag.IRPreconditionCheckStatement) {
            const ipcs = stmt as IRPreconditionCheckStatement;

            const prechk = `${TransformCPPNameManager.generateNameForInvokePreconditionCheck(ipcs.ikey, ipcs.requiresidx)}(${ipcs.args.map((arg) => this.emitIRSimpleExpression(arg, true)).join(", ")}, "${ipcs.file}", ${ipcs.sinfo.line})`
            const dtag = ipcs.diagnosticTag !== null ? `"${ipcs.diagnosticTag}"` : "nullptr";
            return `ᐸRuntimeᐳ::bsq_requires(${prechk}, "${ipcs.file}", ${ipcs.sinfo.line}, ${dtag}, "Failed Requires");`;
        }
        else if(ttag === IRStatementTag.IRPostconditionCheckStatement) {
            const ipcs = stmt as IRPostconditionCheckStatement;

            const postchk = `${TransformCPPNameManager.generateNameForInvokePostconditionCheck(ipcs.ikey, ipcs.ensuresidx)}(${ipcs.args.map((arg) => this.emitIRSimpleExpression(arg, true)).join(", ")}, "${ipcs.file}", ${ipcs.sinfo.line})`
            const dtag = ipcs.diagnosticTag !== null ? `"${ipcs.diagnosticTag}"` : "nullptr";
            return `ᐸRuntimeᐳ::bsq_ensures(${postchk}, "${ipcs.file}", ${ipcs.sinfo.line}, ${dtag}, "Failed Ensures");`;
        }
        else if(ttag === IRStatementTag.IRAbortStatement) {
            const ias = stmt as IRAbortStatement;
            return `${RUNTIME_NAMESPACE}::bsq_abort("${ias.file}", ${ias.sinfo.line}, nullptr, nullptr);`;
        }
        else if(ttag === IRStatementTag.IRAssertStatement) {
            const ias = stmt as IRAssertStatement;
            return `${RUNTIME_NAMESPACE}::bsq_assert(${this.emitIRSimpleExpression(ias.cond, true)}, "${ias.file}", ${ias.sinfo.line}, nullptr, "Assertion Failed");`;
        }
        else if(ttag === IRStatementTag.IRAssumeStatement) {
            return ";"; //nop for execution
        }
        else if(ttag === IRStatementTag.IRValidateStatement) {
            const ivs = stmt as IRValidateStatement;
            return `${RUNTIME_NAMESPACE}::bsq_validate(${this.emitIRSimpleExpression(ivs.cond, true)}, "${ivs.file}", ${ivs.sinfo.line}, nullptr, "Validation Failed");`;
        }
        else if(ttag === IRStatementTag.IRDebugStatement) {
            const ids = stmt as IRDebugStatement;

            const emf = `${TransformCPPNameManager.generateNameForBSQONEmitFunction(ids.oftype.tkeystr)}`;
            return `${emf + "_dbg"}(${this.emitIRSimpleExpression(ids.dbgexp, true)});`;
        }
        else {
            assert(false, `CPPEmitter: Unsupported IR atomic statement type -- ${stmt.constructor.name}`);
        }
    }

    private emitStatement(stmt: IRStatement): string {
        if(stmt instanceof IRAtomicStatement) {
            return this.emitAtomicStatement(stmt);
        }
        else {
            assert(false, `CPPEmitter: Unsupported IR statement type -- ${stmt.constructor.name}`);
        }
    }

    private emitStatementList(stmts: IRStatement[], prefx: string[] | undefined, postfix: string[] | undefined, indent: string | undefined): string {
        const slstrs = stmts.map((stmt) => this.emitStatement(stmt));
        const stmtstrs = (prefx !== undefined || postfix !== undefined) ? [...(prefx || []), ...slstrs, ...(postfix || [])] : slstrs;

        if(indent === undefined) {
            return stmtstrs.join(" ");
        }
        else {
            const bindent = indent + "    ";
            return `{\n${stmtstrs.map((s) => bindent + s).join("\n")}\n${indent}}`;
        }
    }

    /*
    private emitBlockStatement(stmts: IRBlockStatement, indent: string | undefined): string {
        return this.emitStatementList(stmts.statements, undefined, undefined, indent);
    }
    */

    private emitBuiltinBody(body: IRBuiltinBody, indent: string | undefined): string {
        assert(false, "CPPEmitter: need to implement builtin body emission");
    }

    private emitHoleBody(body: IRHoleBody, indent: string | undefined): string {
        assert(false, "CPPEmitter: need to implement builtin body emission");
    }

    private emitBody(body: IRBody, indent: string | undefined): string {
        if(body instanceof IRBuiltinBody) {
            return this.emitBuiltinBody(body, indent);
        }
        else if(body instanceof IRHoleBody) {
            return this.emitHoleBody(body, indent);
        }
        else {
            const sbody = body as IRStandardBody;

            return this.emitStatementList(sbody.statements, undefined, undefined, indent);
        }
    }

    /*
    private emitPreconditionCheckFunction(ipcs: IRPreConditionDecl, invk: IRInvokeDecl): string {
        assert(false, "CPPEmitter: need to implement precondition check function emission");
    }

    private emitPostconditionCheckFunction(ipcs: IRPostConditionDecl, invk: IRInvokeDecl): string {
        assert(false, "CPPEmitter: need to implement postcondition check function emission");
    }
    */

    private emitInvariantFunction(iinv: IRInvariantDecl, tdecl: IRAbstractNominalTypeDecl, pinfo: {pname: string, ptype: IRTypeSignature}[]): [string, string] {
        const fname = TransformCPPNameManager.generateNameForInvariantFunction(tdecl.tkey, iinv.invariantidx);
        const params = pinfo.map((p) => `${this.typeInfoManager.emitTypeAsParameter(p.ptype.tkeystr, false)} ${TransformCPPNameManager.convertIdentifier(p.pname)}`);

        const finalv = `return ${this.emitIRSimpleExpression(iinv.value, true)};`;
        const bodystr = this.emitStatementList(iinv.stmts, undefined, [finalv], "");

        const ideclstr = `bool ${fname}(${params.join(", ")});`;
        const idefstr = `bool ${fname}(${params.join(", ")}) ${bodystr}`;

        return [ideclstr, idefstr];
    }

    private emitValidateFunction(ival: IRValidateDecl, tdecl: IRAbstractNominalTypeDecl, pinfo: {pname: string, ptype: IRTypeSignature}[]): [string, string] {
        const fname = TransformCPPNameManager.generateNameForValidateFunction(tdecl.tkey, ival.validateidx);
        const params = pinfo.map((p) => `${this.typeInfoManager.emitTypeAsParameter(p.ptype.tkeystr, false)} ${TransformCPPNameManager.convertIdentifier(p.pname)}`);

        const finalv = `return ${this.emitIRSimpleExpression(ival.value, true)};`;
        const bodystr = this.emitStatementList(ival.stmts, undefined, [finalv], "");

        const ideclstr = `bool ${fname}(${params.join(", ")});`;
        const idefstr = `bool ${fname}(${params.join(", ")}) ${bodystr}`;

        return [ideclstr, idefstr];
    }
   
    emitConstantDeclInfo(iconst: IRConstantDecl): [string, string] {
        const gvname = `BSQ_g_${TransformCPPNameManager.generateNameForConstantKey(iconst.ckey)}`;
        const staticsstr = `std::optional<${this.typeInfoManager.emitTypeAsStd(iconst.declaredType.tkeystr)}> ${gvname} = std::nullopt;`;
        
        const bodystr = this.emitStatementList(iconst.stmts, [`if(${gvname}.has_value()) { return ${gvname}.value(); } `], [`${gvname} = std::make_optional(${this.emitIRSimpleExpression(iconst.value, true)}); return ${gvname}.value();`], undefined);
        
        const cdeclstr = `${this.typeInfoManager.emitTypeAsStd(iconst.declaredType.tkeystr)} ${TransformCPPNameManager.generateNameForConstantKey(iconst.ckey)}();`;
        const cdefstr = `${staticsstr}\n${this.typeInfoManager.emitTypeAsStd(iconst.declaredType.tkeystr)} ${TransformCPPNameManager.generateNameForConstantKey(iconst.ckey)}() ${bodystr}`;

        return [cdeclstr, cdefstr];
    }

    private emitIRInvokeParameterDecl(iparam: IRInvokeParameterDecl): string {
        assert(iparam.defaultValue === undefined, "CPPEmitter: need to implement default value handling in invoke parameter decl emission");

        const ptypstr = this.typeInfoManager.emitTypeAsParameter(iparam.type.tkeystr, iparam.pkind !== undefined);
        return `${ptypstr} ${TransformCPPNameManager.convertIdentifier(iparam.name)}`;
    }

    private emitIRInvokeDeclInfo(invk: IRInvokeDecl): [string, string] {
        assert(invk.preconditions.length === 0 && invk.postconditions.length === 0, "CPPEmitter: need to implement pre/post condition handling in invoke decl emission");

        const paramstrs = invk.params.map((param) => this.emitIRInvokeParameterDecl(param)).join(", ");
        const rettyps = this.typeInfoManager.emitTypeAsReturn(invk.resultType.tkeystr);

        const bodystr = this.emitBody(invk.body, "");
        
        const ideclstr = `${rettyps} ${TransformCPPNameManager.convertInvokeKey(invk.ikey)}(${paramstrs});`;
        const idefstr = `${rettyps} ${TransformCPPNameManager.convertInvokeKey(invk.ikey)}(${paramstrs}) ${bodystr}`;

        return [ideclstr, idefstr];
    }

    static createEmitter(irasm: IRAssembly): CPPEmitter {
        const tmgr = TypeInfoManager.generateTypeInfos(irasm);
        const ee = new CPPEmitter(irasm, tmgr);

        return ee;
    }

    private emitEnumTypeDeclInfo(eenum: IREnumTypeDecl): [string, string] {
        const ctname = TransformCPPNameManager.convertTypeKey(eenum.tkey);

        const edecl = `enum class ${ctname} : uint64_t {\n` +
        `${eenum.members.map((mem, ii) => `    ${TransformCPPNameManager.convertIdentifier(mem)} = ${ii}`).join(",\n")}\n` +
        `};`;
        const bsqparsedecl = `std::optional<${ctname}> BSQ_parse${ctname}();`;
        const bsqemitdecl = `void BSQ_emit${ctname}(${ctname} vv);`;

        const mmarray = `constexpr std::array<const char*, ${eenum.members.length}> BSQ_enum_values_${ctname} = { ${eenum.members.map((mem) => `"${mem}"`).join(", ")} };`;
        const bsqparsedef = `std::optional<${ctname}> BSQ_parse${ctname}() {\n` + 
        `    if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeType("${eenum.tkey}")) { return std::nullopt; };\n` +
        `    if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol('#')) { return std::nullopt; };\n` +
        '\n' +
        `    char enumstr[64] = {0}; ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeIdentifier(enumstr, 64);\n` +
        `    auto eiter = std::find_if(BSQ_enum_values_${ctname}.cbegin(), BSQ_enum_values_${ctname}.cend(), [enumstr](const char* ev) { return strcmp(ev, enumstr) == 0; });\n` +
        `    if(eiter == BSQ_enum_values_${ctname}.cend()) { return std::nullopt; }\n` +
        '\n' +
        `    return std::make_optional(static_cast<${ctname}>(std::distance(BSQ_enum_values_${ctname}.cbegin(), eiter)));\n` +  
        `}`;
        
        const bsqemitdef = `void BSQ_emit${ctname}(${ctname} vv) {\n` +
        `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitLiteralContent("${eenum.tkey}#");\n` +
        `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitLiteralContent(BSQ_enum_values_${ctname}[static_cast<int>(vv)]);\n` +
        `}`;

        return [
            [edecl, bsqparsedecl, bsqemitdecl].join("\n"), 
            [mmarray, bsqparsedef, bsqemitdef].join("\n")
        ];
    }

    private emitGeneralTypeDeclInfo(tdecl: IRTypedeclTypeDecl): [string, string] {
        const ctname = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
        const ctrepr = this.typeInfoManager.emitTypeAsStd(tdecl.tkey);
        const valuetype = this.typeInfoManager.emitTypeAsMemberField(tdecl.valuetype.tkeystr);

        const vfuncinfo = tdecl.invariants.map((inv) => this.emitInvariantFunction(inv, tdecl, [{pname: "value", ptype: new IRNominalTypeSignature(tdecl.tkey)}]));
        const valfuncinfo = tdecl.validates.map((val) => this.emitValidateFunction(val, tdecl, [{pname: "value", ptype: new IRNominalTypeSignature(tdecl.tkey)}]));

        const tclass = `class ${ctname} {\n` +
            `public:\n` +
            `    ${valuetype} value;\n` +
            `    //All constructor and assignment defaults\n` +
            (tdecl.iskeytype ? 
            `    friend constexpr bool operator<(const ${ctname}& lhs, const ${ctname}& rhs) { return lhs.value < rhs.value; }\n` +
            `    friend constexpr bool operator==(const ${ctname} &lhs, const ${ctname}& rhs) { return lhs.value == rhs.value; }\n` +
            `    friend constexpr bool operator>(const ${ctname} &lhs, const ${ctname}& rhs) { return rhs.value < lhs.value; }\n` +
            `    friend constexpr bool operator!=(const ${ctname} &lhs, const ${ctname}& rhs) { return !(lhs.value == rhs.value); }\n` :
            "") +
            `};`;


        const bsqparsedecl = `std::optional<${ctname}> BSQ_parse${ctname}();`;
        const bsqemitdecl = `void BSQ_emit${ctname}(${ctname} vv);`;

        const voptttname = TransformCPPNameManager.convertTypeKey(tdecl.valuetype.tkeystr);
        const voptt = this.typeInfoManager.emitTypeAsStd(tdecl.valuetype.tkeystr)
        if(vfuncinfo.length === 0 && valfuncinfo.length === 0) {
            const bsqparsedef = `std::optional<${ctrepr}> BSQ_parse${ctname}() {\n` +
            `    std::optional<${voptt}> cc = ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.parse${voptttname}();\n` +
            `    if(!cc.has_value()) { return std::nullopt; }\n` +
            `    if(ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.peekSymbol('<')) {\n` +
            `        if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol('<')) { return std::nullopt; };\n` +
            `        if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeType("${tdecl.tkey}")) { return std::nullopt; };\n` +
            `        if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol('>')) { return std::nullopt; };\n` +
            '    }\n' +
            `    return std::make_optional<${ctname}>(${ctname}{ cc.value() });\n` +
            '}';

            const bsqemitdef = `void BSQ_emit${ctname}(${ctname} vv) {\n` +
            `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emit${valuetype}(vv.value);\n` +
            '    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitLiteralContent("<"); \n' +
            `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitLiteralContent("${tdecl.tkey}"); \n` +
            `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitLiteralContent(">"); \n` +
            `}`;

            return [
                [tclass, bsqparsedecl, bsqemitdecl].join("\n"), 
                [bsqparsedef, bsqemitdef].join("\n")
            ];
        }
        else {
            assert(false, "CPPEmitter: need to implement invariant/validate handling in general type decl emission");
        }
    }

    private emitCStringTypeDeclInfo(tcstr: IRTypedeclCStringDecl): [string, string] {
        assert(false, "CPPEmitter: need to implement cstring type decl emission");
    }

    private emitStringTypeDeclInfo(tstr: IRTypedeclStringDecl): [string, string] {
        assert(false, "CPPEmitter: need to implement string type decl emission");
    }

    //Emit the type declarations needed for the .h file
    private emitTypeDeclInfo(): [string, string] {
        const pdecls = "//Primitive decls\n\n" + this.irasm.primitives.map((pdecl) => {
            const tusing = `using ${pdecl.tkey} = ᐸRuntimeᐳ::X${pdecl.tkey};`;
            const bsqparse = `std::optional<${pdecl.tkey}> BSQ_parse${pdecl.tkey}();`;
            const bsqemit = `void BSQ_emit${pdecl.tkey}(${pdecl.tkey} vv);`;

            return [tusing, bsqparse, bsqemit].join("\n");
        }).join("\n\n");
        const pdefs = "//Primitive defs\n\n" + this.irasm.primitives.map((pdecl) => {
            const bsqparse = `std::optional<${pdecl.tkey}> BSQ_parse${pdecl.tkey}() { return ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.parse${pdecl.tkey}(); }`;
            const bsqemit = `void BSQ_emit${pdecl.tkey}(${pdecl.tkey} vv) { ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emit${pdecl.tkey}(vv); }`;

            return [bsqparse, bsqemit].join("\n");
        }).join("\n\n");

        const enumdd = this.irasm.enums.map((eden) => this.emitEnumTypeDeclInfo(eden));

        const gtddd = this.irasm.typedecls.map((tgtd) =>  this.emitGeneralTypeDeclInfo(tgtd));
        const cstringdd = this.irasm.cstringoftypedecls.map((tcstr) => this.emitCStringTypeDeclInfo(tcstr));
        const stringdd = this.irasm.stringoftypedecls.map((tstr) => this.emitStringTypeDeclInfo(tstr));

        return [
            [pdecls, ...enumdd.map((tt) => tt[0]), ...gtddd.map((tt) => tt[0]), ...cstringdd.map((tt) => tt[0]), ...stringdd.map((tt) => tt[0])].join("\n\n"),
            [pdefs, ...enumdd.map((tt) => tt[1]), ...gtddd.map((tt) => tt[1]), ...cstringdd.map((tt) => tt[1]), ...stringdd.map((tt) => tt[1])].join("\n\n")
        ];
    }

    private emitAllInvokeInfo(): [string, string] {
        assert(this.irasm.predicates.length === 0, "CPPEmitter: need to implement predicate decl emission");
        const idecls = this.irasm.invokes.map((invk) => this.emitIRInvokeDeclInfo(invk));
        assert(this.irasm.taskactions.length === 0, "CPPEmitter: need to implement ADT decl emission");

        return [
            idecls.map((idecl) => idecl[0]).join("\n\n"),
            idecls.map((idecl) => idecl[1]).join("\n\n")
        ];
    }

    private generateHeaderSetup(): string {
        return [
            '#include "./runcpp/common.h"',
            '#include "./runcpp/core/bsqtype.h"',
            '#include "./runcpp/core/integrals.h"',
            '',
            '#include "./runcpp/core/coredecls.h"',
            '#include "./runcpp/runtime/taskinfo.h"'
        ].join("\n");
    }

    //Emit the initialization operations needed
    private emitStaticInitializationOps(): string {
        const stringunion = 'union StdEnvUnion { ᐸRuntimeᐳ::XCString strval; };';

        return [stringunion, '//TODO eventually need to set GC and other info'].join("\n\n");
    }

    //Emit command line main
    private emitCommandLineMain(ikey: string[]): string {
        const notes = "//TODO ---- need to dispatch on things and handle useage + agents.md";

        let dispatchstrs = "";
        if(ikey.length === 1) {
            const idecl = this.irasm.invokes.find((v) => v.ikey === ikey[0]) as IRInvokeDecl;

            dispatchstrs = 
            (idecl.params.length === 1 ?
            'auto iobb = ᐸRuntimeᐳ::g_alloc_info.io_buffer_alloc();\n' + 
            '    size_t ibytes = std::strlen(argv[1]);\n' +
            '    std::copy(argv[1], argv[1] + ibytes, iobb);\n\n' +
            '    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.initialize({iobb}, ibytes);\n' +
            `    auto x = BSQ_parse${TransformCPPNameManager.convertTypeKey(idecl.params[0].type.tkeystr)}();\n` +
            '    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.release();\n' +
            '    if(!x.has_value()) { printf("Error parsing input\\n"); exit(1); }\n\n'
            : '//No args\n\n') +
            '    if (setjmp(ᐸRuntimeᐳ::tl_bosque_info.current_task->error_handler) > 0) {\n' +
            '        auto perr = ᐸRuntimeᐳ::tl_bosque_info.current_task->pending_error.value();\n' +
            '        auto pfile = std::string(perr.file);\n' +
            '        auto pbfile = std::string(pfile.cbegin() + pfile.find_last_of("/") + 1, pfile.cend());\n' +
            '        printf("Error on line %d in file %s\\n", perr.line, pbfile.c_str());\n' +
            '        if(perr.message != nullptr) { printf("  with message: %s\\n", perr.message); }\n' +
            '        exit(1);\n' +
            '    }\n\n' +
            `    auto result = ${TransformCPPNameManager.convertInvokeKey(ikey[0])}(${idecl.params.length === 1 ? 'x.value()' : ''});\n\n` +
            '    size_t obytes = 0;\n' +
            '    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.prepForEmit(true);\n' +
            `    BSQ_emit${TransformCPPNameManager.convertTypeKey(idecl.resultType.tkeystr)}(result);\n` +
            '    auto oibb = ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.completeEmit(obytes);\n\n' +
            '    //TODO assume chars are all printable for now\n' +
            '    for(size_t i = 0; i < obytes; i++) {\n' +
            '        printf("%c", static_cast<char>(oibb.front()[i]));\n' +
            '    }\n' +
            '    printf("\\n");\n\n' +
            '    ᐸRuntimeᐳ::g_alloc_info.io_buffer_free_list(oibb);\n' +
            '    oibb.clear();';
        }
        else {
            assert(false, "CPPEmitter: need to implement multi-invoke command line dispatch");
        }

        return 'int main(int argc, char** argv) {\n' +
               '    ᐸRuntimeᐳ::TaskInfoRepr<StdEnvUnion> envunion; //and more setup here\n' +
               '    ᐸRuntimeᐳ::tl_bosque_info.current_task = &envunion;\n\n' +
               `    ${notes}\n` +
               `    ${dispatchstrs}\n` +
               '}\n';
    }

    emitInvokeForKey(ikey: string): string {
        const invk = this.irasm.invokes.find((v) => v.ikey === ikey);

        return this.emitIRInvokeDeclInfo(invk as IRInvokeDecl)[1];
    }

    public emitForCommandLine(ikey: string[]): [string, string] {
        const typeinfo = this.emitTypeDeclInfo();
        const iinfo = this.emitAllInvokeInfo();

        const headerstrs = [
            this.generateHeaderSetup(), '',
            typeinfo[0], '',
            iinfo[0],
        ].join("\n");

        const statisinitstr = this.emitStaticInitializationOps();
        const mainstr = this.emitCommandLineMain(ikey);

        const implstrs = [
            '#include "./app.h"', '',
            typeinfo[1], '',
            iinfo[1], '',
            statisinitstr, '',
            mainstr
        ].join("\n");

        return [headerstrs, implstrs];
    }
}

export {
    CPPEmitter
};
