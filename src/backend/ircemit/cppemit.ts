import { TransformCPPNameManager } from "./namemgr";
import { TypeInfoManager } from "./typeinfomgr";

import { MAX_SAFE_INT, MAX_SAFE_NAT, MIN_SAFE_INT } from "../../frontend/assembly";
import { IRExpression, IRExpressionTag, IRLiteralChkIntExpression, IRLiteralChkNatExpression, IRLiteralBoolExpression, IRLiteralByteExpression, IRLiteralCCharExpression, IRLiteralComplexExpression, IRLiteralCRegexExpression, IRLiteralDeltaDateTimeExpression, IRLiteralDeltaISOTimeStampExpression, IRLiteralDeltaLogicalTimeExpression, IRLiteralDeltaSecondsExpression, IRLiteralFloatExpression, IRLiteralIntExpression, IRLiteralISOTimeStampExpression, IRLiteralLogicalTimeExpression, IRLiteralNatExpression, IRLiteralPlainDateExpression, IRLiteralPlainTimeExpression, IRLiteralSHAContentHashExpression, IRLiteralStringExpression, IRLiteralTAITimeExpression, IRLiteralTZDateTimeExpression, IRLiteralUnicodeCharExpression, IRLiteralUnicodeRegexExpression, IRLiteralUUIDv4Expression, IRLiteralUUIDv7Expression, IRLiteralExpression, IRImmediateExpression, IRLiteralTypedExpression, IRLiteralTypedCStringExpression, IRAccessEnvHasExpression, IRAccessEnvGetExpression, IRAccessEnvTryGetExpression, IRAccessNamespaceConstantExpression, IRAccessStaticFieldExpression, IRAccessParameterVariableExpression, IRAccessLocalVariableExpression, IRAccessCapturedVariableExpression, IRAccessEnumExpression, IRLiteralByteBufferExpression, IRAccessTempVariableExpression, IRSimpleExpression, IRAtomicStatement, IRStatement, IRStatementTag, IRPrefixNotOpExpression, IRPrefixPlusOpExpression, IRPrefixNegateOpExpression, IRBinAddExpression, IRBinSubExpression, IRBinMultExpression, IRBinDivExpression, IRNumericEqExpression, IRNumericNeqExpression, IRNumericLessExpression, IRNumericLessEqExpression, IRNumericGreaterExpression, IRNumericGreaterEqExpression, IRLogicAndExpression, IRLogicOrExpression, IRReturnValueSimpleStatement, IRErrorAdditionBoundsCheckStatement, IRErrorSubtractionBoundsCheckStatement, IRErrorMultiplicationBoundsCheckStatement, IRErrorDivisionByZeroCheckStatement, IRAbortStatement, IRVariableDeclarationStatement, IRVariableInitializationStatement, IRTempAssignExpressionStatement, IRTypeDeclInvariantCheckStatement, IRDebugStatement, IRAccessTypeDeclValueExpression, IRConstructSafeTypeDeclExpression, IRChkLogicImpliesShortCircuitStatement, IRBlockStatement, IRPreconditionCheckStatement, IRPostconditionCheckStatement } from "../irdefs/irbody";

import assert from "node:assert";

const RUNTIME_NAMESPACE = "ᐸRuntimeᐳ";
const CLOSURE_CAPTURE_NAME = "ᐸclosureᐳ";

class CPPEmitter {
    //The C++ TaskInfoRepr<U> for accessing the global info for the task we are emitting
    private cppTaskType: string;

    private typeInfoManager: TypeInfoManager;

    constructor(cppTaskType: string, typeInfoManager: TypeInfoManager) {
        this.cppTaskType = cppTaskType;
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

    private emitIRLiteral(exp: IRLiteralExpression): string {
        const ttag = exp.tag;

        if(ttag === IRExpressionTag.IRLiteralNoneExpression) {
            return "none";
        }
        else if(ttag === IRExpressionTag.IRLiteralBoolExpression) {
            return (exp as IRLiteralBoolExpression).value ? "TRUE" : "FALSE";
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
            //const bbexp = (exp as IRLiteralByteBufferExpression);
            assert(false, "CPPEmitter: need to handle byte buffer literals -- must be heap allocated");
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
                return TransformCPPNameManager.generateNameForConstantKey((exp as IRAccessNamespaceConstantExpression).constkey) + "()";
            }
            else if(ttag === IRExpressionTag.IRAccessStaticFieldExpression) {
                return TransformCPPNameManager.generateNameForConstantKey((exp as IRAccessStaticFieldExpression).constkey) + "()";
            }
            else if(ttag === IRExpressionTag.IRAccessEnumExpression) {
                return TransformCPPNameManager.generateNameForEnumKey((exp as IRAccessEnumExpression).enumkey);
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
            let skipparens = false;
            if(ttag === IRExpressionTag.IRAccessTypeDeclValueExpression) {
                const cexp = exps as IRAccessTypeDeclValueExpression;
                bstr = `(${this.emitIRSimpleExpression(cexp.exp, false)}).value`;
            }
            else if(ttag === IRExpressionTag.IRConstructSafeTypeDeclExpression) {
                const cexp = exps as IRConstructSafeTypeDeclExpression;
                bstr = `${TransformCPPNameManager.generateNameForConstructor(cexp.constype.tkeystr)}(${this.emitIRSimpleExpression(cexp.value, toplevel)})`;
            }
            else if(ttag === IRExpressionTag.IRPrefixNotOpExpression) {
                skipparens = true;
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
            else {
                assert(false, `CPPEmitter: Unsupported IR simple expression type -- ${exps.constructor.name}`);
            }

            return (toplevel || skipparens) ? bstr : `(${bstr})`;
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
                return `(${RUNTIME_NAMESPACE}::tl_info.parent !== nullptr ? ${RUNTIME_NAMESPACE}::tl_info.parent->taskid : ${RUNTIME_NAMESPACE}::UUIDv4::nil())`;
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
            
            const vdecltype = this.typeInfoManager.emitTypeAsStd(tase.ttype.tkeystr, true);
            const wval = this.emitExpression(tase.rhs, true);
            return `${vdecltype} ${TransformCPPNameManager.convertIdentifier(tase.tname)} = ${wval};`
        }
        else if(ttag === IRStatementTag.IRTempAssignStdInvokeStatement) {
            assert(false, "CPPEmitter: need to implement std invoke temp assign");
        }
        else if(ttag === IRStatementTag.IRTempAssignRefInvokeStatement) {
            assert(false, "CPPEmitter: need to implement ref invoke temp assign");
        }
        else if(ttag === IRStatementTag.IRTempAssignConditionalStatement) {
            assert(false, "CPPEmitter: need to implement conditional temp assign");
        }
        else if(ttag === IRStatementTag.IRVariableDeclarationStatement) {
            const vdeclstmt = stmt as IRVariableDeclarationStatement;

            const vdecltype = this.typeInfoManager.emitTypeAsStd(vdeclstmt.vtype.tkeystr, false);
            return `${vdecltype} ${TransformCPPNameManager.convertIdentifier(vdeclstmt.vname)};`
        }
        else if(ttag === IRStatementTag.IRVariableInitializationStatement) {
            const vistmt = stmt as IRVariableInitializationStatement;

            const vdecltype = this.typeInfoManager.emitTypeAsStd(vistmt.vtype.tkeystr, vistmt.isconst);
            const wval = this.emitIRSimpleExpression(vistmt.initexp, true);
            return `${vdecltype} ${TransformCPPNameManager.convertIdentifier(vistmt.vname)} = ${wval};`
        }
        else if(ttag === IRStatementTag.IRReturnVoidSimpleStatement) {
            return "return;";
        }
        else if(ttag === IRStatementTag.IRReturnValueSimpleStatement) {
            const ires = stmt as IRReturnValueSimpleStatement;
            return `return ${this.emitIRSimpleExpression(ires.retexp, true)};`;
        }
        else if(ttag === IRStatementTag.IRChkLogicImpliesShortCircuitStatement) {
            const icliss = stmt as IRChkLogicImpliesShortCircuitStatement;
            return `Bool ${icliss.tvar} = TRUE; if(${this.emitIRSimpleExpression(icliss.lhs, true)}) ${this.emitBlockStatement(icliss.rhs, undefined)}`;
        }
        else if(ttag === IRStatementTag.IRErrorAdditionBoundsCheckStatement) {
            const ieabc = stmt as IRErrorAdditionBoundsCheckStatement;
            return `${RUNTIME_NAMESPACE}::${ieabc.optypechk}::checkOverflowAddition(${this.emitIRSimpleExpression(ieabc.left, true)}, ${this.emitIRSimpleExpression(ieabc.right, true)}, ${ieabc.file}, ${ieabc.sinfo.line});`;
        }
        else if(ttag === IRStatementTag.IRErrorSubtractionBoundsCheckStatement) {
            const iesbc = stmt as IRErrorSubtractionBoundsCheckStatement;
            return `${RUNTIME_NAMESPACE}::${iesbc.optypechk}::checkOverflowSubtraction(${this.emitIRSimpleExpression(iesbc.left, true)}, ${this.emitIRSimpleExpression(iesbc.right, true)}, ${iesbc.file}, ${iesbc.sinfo.line});`;
        }
        else if(ttag === IRStatementTag.IRErrorMultiplicationBoundsCheckStatement) {
            const iembc = stmt as IRErrorMultiplicationBoundsCheckStatement;
            return `${RUNTIME_NAMESPACE}::${iembc.optypechk}::checkOverflowMultiplication(${this.emitIRSimpleExpression(iembc.left, true)}, ${this.emitIRSimpleExpression(iembc.right, true)}, ${iembc.file}, ${iembc.sinfo.line});`;
        }
        else if(ttag === IRStatementTag.IRErrorDivisionByZeroCheckStatement) {
            const iedzbc = stmt as IRErrorDivisionByZeroCheckStatement;
            return `${RUNTIME_NAMESPACE}::${iedzbc.optypechk}::checkDivisionByZero(${this.emitIRSimpleExpression(iedzbc.left, true)}, ${iedzbc.file}, ${iedzbc.sinfo.line});`;
        }
        else if(ttag === IRStatementTag.IRTypeDeclInvariantCheckStatement) {
            const itdics = stmt as IRTypeDeclInvariantCheckStatement;

            const invchk = `${TransformCPPNameManager.generateNameForInvariantFunction(itdics.tkey, itdics.invariantidx)}(${this.emitIRSimpleExpression(itdics.targetValue, true)}, ${itdics.file}, ${itdics.sinfo.line})`
            const dtag = itdics.diagnosticTag !== null ? `"${itdics.diagnosticTag}"` : "nullptr";
            return `ᐸRuntimeᐳ::bsq_invariant(${invchk}, "${itdics.file}", ${itdics.sinfo.line}, ${dtag}, "Failed Invariant");`;
        }
        else if(ttag === IRStatementTag.IRPreconditionCheckStatement) {
            const ipcs = stmt as IRPreconditionCheckStatement;

            const prechk = `${TransformCPPNameManager.generateNameForInvokePreconditionCheck(ipcs.ikey, ipcs.requiresidx)}(${ipcs.args.map((arg) => this.emitIRSimpleExpression(arg, true)).join(", ")}, ${ipcs.file}, ${ipcs.sinfo.line})`
            const dtag = ipcs.diagnosticTag !== null ? `"${ipcs.diagnosticTag}"` : "nullptr";
            return `ᐸRuntimeᐳ::bsq_requires(${prechk}, "${ipcs.file}", ${ipcs.sinfo.line}, ${dtag}, "Failed Requires");`;
        }
        else if(ttag === IRStatementTag.IRPostconditionCheckStatement) {
            const ipcs = stmt as IRPostconditionCheckStatement;
            
            const postchk = `${TransformCPPNameManager.generateNameForInvokePostconditionCheck(ipcs.ikey, ipcs.ensuresidx)}(${ipcs.args.map((arg) => this.emitIRSimpleExpression(arg, true)).join(", ")}, ${ipcs.file}, ${ipcs.sinfo.line})`
            const dtag = ipcs.diagnosticTag !== null ? `"${ipcs.diagnosticTag}"` : "nullptr";
            return `ᐸRuntimeᐳ::bsq_ensures(${postchk}, "${ipcs.file}", ${ipcs.sinfo.line}, ${dtag}, "Failed Ensures");`;
        }
        else if(ttag === IRStatementTag.IRAbortStatement) {
            const ias = stmt as IRAbortStatement;
            return `${RUNTIME_NAMESPACE}::bsq_abort(${ias.file}, ${ias.sinfo.line}, nullptr, nullptr);`;
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

    private emitBlockStatement(stmts: IRBlockStatement, indent: string | undefined): string {
        const stmtstrs = stmts.statements.map((stmt) => this.emitStatement(stmt));
        if(indent === undefined) {
            return stmtstrs.join(" ");
        }
        else {
            const bindent = indent + "    ";
            return `{\n${bindent}${stmtstrs.map((s) => bindent + s).join("\n")}\n${indent}}`;
        }
    }
}

export {
    CPPEmitter
};
