import { TransformCPPNameManager } from "./namemgr.js";
import { LayoutTag, LIST_T_CAPACITY, TypeInfo, TypeInfoManager } from "./typeinfomgr.js";

import { MAX_SAFE_INT, MAX_SAFE_NAT, MIN_SAFE_INT } from "../../frontend/assembly.js";
import { IRExpression, IRExpressionTag, IRLiteralChkIntExpression, IRLiteralChkNatExpression, IRLiteralBoolExpression, IRLiteralByteExpression, IRLiteralCCharExpression, IRLiteralComplexExpression, IRLiteralCRegexExpression, IRLiteralDeltaDateTimeExpression, IRLiteralDeltaISOTimeStampExpression, IRLiteralDeltaLogicalTimeExpression, IRLiteralDeltaSecondsExpression, IRLiteralFloatExpression, IRLiteralIntExpression, IRLiteralISOTimeStampExpression, IRLiteralLogicalTimeExpression, IRLiteralNatExpression, IRLiteralPlainDateExpression, IRLiteralPlainTimeExpression, IRLiteralSHAContentHashExpression, IRLiteralStringExpression, IRLiteralTAITimeExpression, IRLiteralTZDateTimeExpression, IRLiteralUnicodeCharExpression, IRLiteralUnicodeRegexExpression, IRLiteralUUIDv4Expression, IRLiteralUUIDv7Expression, IRLiteralExpression, IRImmediateExpression, IRLiteralTypedExpression, IRLiteralTypedCStringExpression, IRAccessEnvHasExpression, IRAccessEnvGetExpression, IRAccessEnvTryGetExpression, IRAccessConstantExpression, IRAccessParameterVariableExpression, IRAccessLocalVariableExpression, IRAccessCapturedVariableExpression, IRAccessEnumExpression, IRAccessTempVariableExpression, IRSimpleExpression, IRAtomicStatement, IRStatement, IRStatementTag, IRPrefixNotOpExpression, IRPrefixPlusOpExpression, IRPrefixNegateOpExpression, IRBinAddExpression, IRBinSubExpression, IRBinMultExpression, IRBinDivExpression, IRNumericEqExpression, IRNumericNeqExpression, IRNumericLessExpression, IRNumericLessEqExpression, IRNumericGreaterExpression, IRNumericGreaterEqExpression, IRLogicAndExpression, IRLogicOrExpression, IRReturnValueSimpleStatement, IRErrorAdditionBoundsCheckStatement, IRErrorSubtractionBoundsCheckStatement, IRErrorMultiplicationBoundsCheckStatement, IRErrorDivisionByZeroCheckStatement, IRTypeDeclSizeRangeCheckCStringStatement, IRTypeDeclSizeRangeCheckUnicodeStringStatement, IRAbortStatement, IRVariableDeclarationStatement, IRVariableInitializationStatement, IRTempAssignExpressionStatement, IRTypeDeclInvariantCheckStatement, IRDebugStatement, IRAccessTypeDeclValueExpression, IRConstructSafeTypeDeclExpression, IRChkLogicImpliesShortCircuitStatement, IRPreconditionCheckStatement, IRPostconditionCheckStatement, IRVariableInitializationDirectInvokeStatement, IRLogicSimpleConditionalExpression, IRLogicConditionalStatement, IRAssertStatement, IRValidateStatement, IRBody, IRBuiltinBody, IRStandardBody, IRHoleBody, IRIsNoneOptionExpression, IRBinKeyEqDirectExpression, IRIsOptionEqValueExpression, IRIsSomeNeqValueExpression, IRIsOptionNeqValueExpression, IRIsSomeEqValueExpression, IRConstructorSomeTypeExpression, IRLiteralOptionOfNoneExpression, IRConstructOptionFromSomeExpression, IRExtractSomeFromOptionExpression, IRExtractSomeValueFromOptionExpression, IRBinKeyNeqDirectExpression, IRBinKeyLessDirectExpression, IRSimpleIfStatement, IRSimpleIfElseStatement, IRConstructorStandardEntityExpression, IRReturnDirectConstructStatement, IRReturnDirectInvokeStatement, IRVariableInitializationDirectConstructorStatement, IREntityInvariantCheckStatement, IRBoxEntityToConceptRepresentationExpression, IRVariableAssignmentStatement, IRVariableAssignmentDirectInvokeStatement, IRVariableAssignmentDirectConstructorStatement, IRConstructorListEmptyExpression, IRConstructorListSingletonsExpression, IRInvokeSimpleExpression, IRVariableInitializationDirectInvokeWithImplicitStatement, IRVariableAssignmentDirectInvokeWithImplicitStatement, IRReturnDirectConstructWithBoxStatement, IRReturnValueImplicitStatement, IRReturnDirectInvokeImplicitStatement, IRReturnDirectInvokeImplicitPassThroughStatement, IRReturnDirectConstructImplicitStatement, IRReturnDirectConstructWithBoxImplicitStatement, IRInvokeSimpleWithImplicitsExpression, IRTempAssignRefInvokeStatement, IRTempAssignStdInvokeStatement, IRVoidInvokeStatement, IRVariableInitializationDirectConstructorWithBoxStatement, IRVariableAssignmentDirectConstructorWithBoxStatement, IRLiteralFormatCStringExpression, IRLiteralFormatStringExpression, IRInterpolateFormatCStringExpression, IRFormatStringTextComponent, IRFormatStringArgComponent, IRTypeDeclFormatCheckCStringStatement, IRLiteralTypedStringExpression, IRAccessFieldSpecialExpression, IRAccessFieldVirtualExpression, IRIsConceptRepresentationOfTypeExpression } from "../irdefs/irbody.js";
import { IRAbstractCollectionTypeDecl, IRAbstractEntityTypeDecl, IRAbstractNominalTypeDecl, IRAssembly, IRConceptTypeDecl, IRConstantDecl, IRConstructableTypeDecl, IREntityTypeDecl, IREnumTypeDecl, IRFailTypeDecl, IRInternalConceptTypeDecl, IRInvariantDecl, IRInvokeDecl, IRInvokeParameterDecl, IRListTypeDecl, IRMapEntryTypeDecl, IRMapTypeDecl, IROkTypeDecl, IROptionTypeDecl, IRPrimitiveEntityTypeDecl, IRResultTypeDecl, IRSomeTypeDecl, IRTypedeclCStringDecl, IRTypedeclStringDecl, IRTypedeclTypeDecl, IRValidateDecl } from "../irdefs/irassembly.js";

import assert from "node:assert";
import { IRDashResultTypeSignature, IREListTypeSignature, IRFormatCStringTypeSignature, IRFormatStringTypeSignature, IRFormatTypeSignature, IRLambdaParameterPackTypeSignature, IRNominalTypeSignature, IRTypeSignature, IRVoidTypeSignature } from "../irdefs/irtype.js";
import { IRCRegex, IRURegex } from "../irdefs/irsupport.js";

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

    private escapeLiteralCString(cstrbytes: number[]): [string, number] {
        let escstr = '"';
        
        for(let i = 0; i < cstrbytes.length; i++) {
            const b = cstrbytes[i];
            
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

        return [escstr, cstrbytes.length];
    }

    private escapeLiteralString(cstrbytes: number[]): [string, number] {
        let escstr = 'U"';
        let lcount = 0;

        for(let i = 0; i < cstrbytes.length; i++) {
            const b = cstrbytes[i];

            if(b === 0x5C) {
                escstr += "\\\\";
                lcount++;
            }
            else if(b === 0x22) {
                escstr += '\\"';
                lcount++;
            }
            else if(b === 0x0A) {
                escstr += "\\n";
                lcount++;
            }
            else if(b === 0x09) {
                escstr += "\\t";
                lcount++;
            }
            else {
                if(32 <= b && b < 127) {
                    escstr += String.fromCodePoint(b);
                    lcount++;
                }
                else {
                    assert(false, "CPPEmitter: need to do unicode escape for non-ascii characters in string literals -- they are utf8 encoded btw");
                }
            }
        }
        escstr += '"';

        return [escstr, lcount];
    }

    private isNominalTypeUniqueEntity(t: IRTypeSignature): boolean {
        if(!(t instanceof IRNominalTypeSignature)) {
            return false;
        }

        const decl = this.irasm.alltypes.get(t.tkeystr) as IRAbstractNominalTypeDecl;
        return decl instanceof IRAbstractEntityTypeDecl;
    }

    private getAllConcreteSubtypeOptionsForNominalType(t: IRNominalTypeSignature): IRAbstractEntityTypeDecl[] {
        return (this.irasm.concretesubtypes.get(t.tkeystr) as IRTypeSignature[])
            .map((st) => this.irasm.alltypes.get(st.tkeystr) as IRAbstractEntityTypeDecl);
    }

    private emitIRLiteral(exp: IRLiteralExpression): string {
        const ttag = exp.tag;

        if(ttag === IRExpressionTag.IRLiteralNoneExpression) {
            return "none";
        }
        else if(ttag === IRExpressionTag.IRLiteralOptionOfNoneExpression) {
            const cexp = exp as IRLiteralOptionOfNoneExpression;
            return `${TransformCPPNameManager.convertTypeKey(cexp.opttype.tkeystr)}::optnone`
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
            if(ll === "ChkNat::npos") {
                return "ᐸRuntimeᐳ::XChkNat::bliteral()";
            }
            else {
                const nval = BigInt(ll.startsWith("+") ? ll.slice(1) : ll);
                if(nval <= MAX_SAFE_NAT) {
                    return `${ll.startsWith("+") ? ll.slice(1) : ll}_N`;
                }
                else {
                    assert(false, `CPPEmitter: need to do bit shift construction for (really big) safe nat -- ${(exp as IRLiteralChkNatExpression).value}`);
                }
            }
        }
        else if(ttag === IRExpressionTag.IRLiteralChkIntExpression) {
            const ll = (exp as IRLiteralChkIntExpression).value;
            if(ll === "ChkInt::npos") {
                return "ᐸRuntimeᐳ::XChkInt::bliteral()";
            }
            else {
                const ival = BigInt(ll.startsWith("+") ? ll.slice(1) : ll);
                if(MIN_SAFE_INT <= ival && ival <= MAX_SAFE_INT) {
                    return `${ll.startsWith("+") ? ll.slice(1) : ll}_I`;
                }
                else {
                    assert(false, `CPPEmitter: need to do bit shift construction for (really big) safe int -- ${(exp as IRLiteralChkIntExpression).value}`);
                }
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
            return `Regex{${(exp as IRLiteralUnicodeRegexExpression).regexID}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralCRegexExpression) {
            return `CRegex{${(exp as IRLiteralCRegexExpression).regexID}}`;
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
            const [escstr, lcount] = this.escapeLiteralCString((exp as IRLiteralStringExpression).bytes);

            if(lcount <= SMALL_CSTRING_MAX_SIZE) {
                return `${RUNTIME_NAMESPACE}::XCString::smliteral(${escstr})`;
            }
            else {
                assert(false, "CPPEmitter: need to do heap allocation for long cstrings");
            }
        }
        else if(ttag === IRExpressionTag.IRLiteralStringExpression) {
            const [ustr, lcount] = this.escapeLiteralString((exp as IRLiteralStringExpression).bytes);
        
            if(lcount <= SMALL_STRING_MAX_SIZE) {
                return `${RUNTIME_NAMESPACE}::XString::smliteral(${ustr})`;
            }
            else {
                assert(false, "CPPEmitter: need to do heap allocation for long strings");
            }
        }
        else if(ttag === IRExpressionTag.IRLiteralFormatStringExpression) {
            const ilfsexp = exp as IRLiteralFormatStringExpression;
            return `${RUNTIME_NAMESPACE}::XFString{${ilfsexp.fmtid}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralFormatCStringExpression) {
            const ilfcsexp = exp as IRLiteralFormatCStringExpression;
            return `${RUNTIME_NAMESPACE}::XFCString{${ilfcsexp.fmtid}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralTypedExpression) {
            const ilte = exp as IRLiteralTypedExpression
            const cce = TransformCPPNameManager.generateNameForConstructor(ilte.constype.tkeystr);

            return `${cce}{${this.emitIRLiteral(ilte.value as IRLiteralExpression)}}`;
        }
        else if(ttag === IRExpressionTag.IRLiteralTypedStringExpression) {
            const ilte = exp as IRLiteralTypedStringExpression
            const cce = TransformCPPNameManager.convertTypeKey(ilte.constype.tkeystr);
            const [escstr, lcount] = this.escapeLiteralString(ilte.bytes);

            if(lcount <= SMALL_STRING_MAX_SIZE) {
                return `${cce}(${RUNTIME_NAMESPACE}::XString::smliteral(${escstr}))`;
            }
            else {
                assert(false, "CPPEmitter: need to do heap allocation for long strings");
            }
        }
        else if(ttag === IRExpressionTag.IRLiteralTypedCStringExpression) {
            const ilte = exp as IRLiteralTypedCStringExpression
            const cce = TransformCPPNameManager.convertTypeKey(ilte.constype.tkeystr);
            const [escstr, lcount] = this.escapeLiteralCString(ilte.bytes);

            if(lcount <= SMALL_CSTRING_MAX_SIZE) {
                return `${cce}(${RUNTIME_NAMESPACE}::XCString::smliteral(${escstr}))`;
            }
            else {
                assert(false, "CPPEmitter: need to do heap allocation for long cstrings");
            }
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
                bstr = `${TransformCPPNameManager.generateNameForConstructor(cexp.constype.tkeystr)}{${this.emitIRSimpleExpression(cexp.value, toplevel)}}`;
            }
            else if(ttag === IRExpressionTag.IRConstructorSomeTypeExpression) {
                const cexp = exps as IRConstructorSomeTypeExpression;
                bstr = `${TransformCPPNameManager.generateNameForConstructor(cexp.oftype.tkeystr)}{${this.emitIRSimpleExpression(cexp.value, false)}}`;
            }
            else if(ttag === IRExpressionTag.IRConstructorOkTypeExpression) {
                assert(false, "CPPEmitter: need to implement ok type expression emission");
            }
            else if(ttag === IRExpressionTag.IRConstructorFailTypeExpression) {
                assert(false, "CPPEmitter: need to implement fail type expression emission");
            }
            else if(ttag === IRExpressionTag.IRConstructorMapEntryTypeExpression) {
                assert(false, "CPPEmitter: need to implement map entry type expression emission");
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
            else if(ttag === IRExpressionTag.IRIsNoneOptionExpression) {
                const nexp = exps as IRIsNoneOptionExpression;
                bstr = `${this.emitIRSimpleExpression(nexp.exp, false)}.isNone()`;
            }
            else if(ttag === IRExpressionTag.IRIsNotNoneOptionExpression) {
                const nexp = exps as IRIsNoneOptionExpression;
                bstr = `!${this.emitIRSimpleExpression(nexp.exp, false)}.isNone()`;
            }
            else if(ttag === IRExpressionTag.IRIsOptionEqValueExpression) {
                const eqvop = exps as IRIsOptionEqValueExpression;
                const optexp = this.emitIRSimpleExpression(eqvop.optexp, false);
                const valexp = this.emitIRSimpleExpression(eqvop.valexp, false);
                bstr = `${optexp} == ${valexp}`;
            }
            else if(ttag === IRExpressionTag.IRIsOptionNeqValueExpression) {
                const eqvop = exps as IRIsOptionNeqValueExpression
                const optexp = this.emitIRSimpleExpression(eqvop.optexp, false);
                const valexp = this.emitIRSimpleExpression(eqvop.valexp, false);
                bstr = `${optexp} != ${valexp}`;
            }
            else if(ttag === IRExpressionTag.IRIsSomeEqValueExpression) {
                const eqvop = exps as IRIsSomeEqValueExpression;
                const optexp = this.emitIRSimpleExpression(eqvop.someexp, false);
                const valexp = this.emitIRSimpleExpression(eqvop.valexp, false);
                bstr = `${optexp} == ${valexp}`;
            }
            else if(ttag === IRExpressionTag.IRIsSomeNeqValueExpression) {
                const eqvop = exps as IRIsSomeNeqValueExpression;
                const optexp = this.emitIRSimpleExpression(eqvop.someexp, false);
                const valexp = this.emitIRSimpleExpression(eqvop.valexp, false);
                bstr = `${optexp} != ${valexp}`;
            }
            else if(ttag === IRExpressionTag.IRBinKeyEqDirectExpression) {
                const bexp = exps as IRBinKeyEqDirectExpression;
                const leftexp = this.emitIRSimpleExpression(bexp.left, false);
                const rightexp = this.emitIRSimpleExpression(bexp.right, false);
                bstr = `${leftexp} == ${rightexp}`;
            }
            else if(ttag === IRExpressionTag.IRBinKeyNeqDirectExpression) {
                const bexp = exps as IRBinKeyNeqDirectExpression;
                const leftexp = this.emitIRSimpleExpression(bexp.left, false);
                const rightexp = this.emitIRSimpleExpression(bexp.right, false);
                bstr = `${leftexp} != ${rightexp}`;
            }
            else if(ttag === IRExpressionTag.IRBinKeyLessDirectExpression) {
                const bexp = exps as IRBinKeyLessDirectExpression;
                const leftexp = this.emitIRSimpleExpression(bexp.left, false);
                const rightexp = this.emitIRSimpleExpression(bexp.right, false);
                bstr = `${leftexp} < ${rightexp}`;
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
            else if(ttag === IRExpressionTag.IRConstructOptionFromSomeExpression) {
                const cexp = exps as IRConstructOptionFromSomeExpression;
                const octype = TransformCPPNameManager.convertTypeKey(cexp.opttype.tkeystr);
                const sometypeinfo = TransformCPPNameManager.generateTypeInfoNameForTypeKey(cexp.sometype.tkeystr);
                bstr = `${octype}::fromSome(&${sometypeinfo}, ${this.emitIRSimpleExpression(cexp.value, true)})`;
            }
            else if(ttag === IRExpressionTag.IRExtractSomeFromOptionExpression) {
                const eexp = exps as IRExtractSomeFromOptionExpression;
                bstr = `${this.emitIRSimpleExpression(eexp.value, false)}.asSome()`;
            }
            else if(ttag === IRExpressionTag.IRExtractSomeValueFromOptionExpression) {
                const eexp = exps as IRExtractSomeValueFromOptionExpression;
                bstr = `${this.emitIRSimpleExpression(eexp.value, false)}.unwrap()`;
            }
            else if(ttag === IRExpressionTag.IRConstructResultFromOkExpression) {
                assert(false, "CPPEmitter: need to implement construct ok from result expression");
            }
            else if(ttag === IRExpressionTag.IRConstructResultFromFailExpression) {
                assert(false, "CPPEmitter: need to implement construct fail from result expression");
            }
            else if(ttag === IRExpressionTag.IRExtractOkFromResultExpression) {
                assert(false, "CPPEmitter: need to implement extract ok from result expression");
            }
            else if(ttag === IRExpressionTag.IRExtractOkValueFromResultExpression) {
                assert(false, "CPPEmitter: need to implement extract ok value from result expression");
            }
            else if(ttag === IRExpressionTag.IRExtractFailFromResultExpression) {
                assert(false, "CPPEmitter: need to implement extract fail from result expression");
            }
            else if(ttag === IRExpressionTag.IRExtractFailValueFromResultExpression) {
                assert(false, "CPPEmitter: need to implement extract fail value from result expression");
            }
            else if(ttag === IRExpressionTag.IRIsConceptRepresentationOfTypeExpression) {
                const crep = exps as IRIsConceptRepresentationOfTypeExpression;
                const gmgr = TransformCPPNameManager.generateTypeInfoNameForTypeKey(crep.targettype.tkeystr);
                bstr = `${this.emitIRSimpleExpression(crep.exp, false)}.uval.isTypeOf(&${gmgr})`;
            }
            else if(ttag === IRExpressionTag.IRIsNotConceptRepresentationOfTypeExpression) {
                assert(false, "CPPEmitter: need to implement is not concept representation of type expression");
            }
            else if(ttag === IRExpressionTag.IRIsConceptRepresentationSubtypeOfTypeExpression) {
                assert(false, "CPPEmitter: need to implement is concept representation subtype of type expression");
            }
            else if(ttag === IRExpressionTag.IRIsNotConceptRepresentationSubtypeOfTypeExpression) {
                assert(false, "CPPEmitter: need to implement is not concept representation subtype of type expression");
            }
            else if(ttag === IRExpressionTag.IRStaticIsTypeSubtypeOfExpression) {
                assert(false, "CPPEmitter: need to implement static is type subtype of expression");
            }
            else if(ttag === IRExpressionTag.IRBoxEntityToConceptRepresentationExpression) {
                const bexp = exps as IRBoxEntityToConceptRepresentationExpression;
                const ctype = TransformCPPNameManager.convertTypeKey(bexp.totype.tkeystr); 
                bstr = `${ctype}(${this.emitIRSimpleExpression(bexp.value, true)})`;
            }
            else if(ttag === IRExpressionTag.IRUnboxEntityFromConceptRepresentationExpression) {
                assert(false, "CPPEmitter: need to implement unbox entity from concept representation expression");
            }
            else if(ttag === IRExpressionTag.IRWidenConceptRepresentationExpression) {
                assert(false, "CPPEmitter: need to implement widen concept representation expression");
            }
            else if(ttag === IRExpressionTag.IRNarrowConceptRepresentationExpression) {
                assert(false, "CPPEmitter: need to implement narrow concept representation expression");
            }
            else if(ttag === IRExpressionTag.IRConstructorListEmptyExpression) {
                const elcexp = exps as IRConstructorListEmptyExpression;

                bstr = `${TransformCPPNameManager.generateNameForConstructor(elcexp.ctype.tkeystr)}::make_empty()`;
            }
            else if(ttag === IRExpressionTag.IRAccessFieldSpecialExpression) {
                const afse = exps as IRAccessFieldSpecialExpression;
                const mname = TransformCPPNameManager.convertIdentifier(afse.fieldname);
                return `${this.emitIRSimpleExpression(afse.eexp, false)}.${mname}`;
            }
            else if(ttag === IRExpressionTag.IRAccessFieldDirectExpression) {
                const afse = exps as IRAccessFieldSpecialExpression;
                const tinfo = this.typeInfoManager.getTypeInfo(afse.eexptype.tkeystr);

                const mname = TransformCPPNameManager.convertIdentifier(afse.fieldname);
                return `${this.emitIRSimpleExpression(afse.eexp, false)}${tinfo.getAccessor()}${mname}`;
            }
            else if(ttag === IRExpressionTag.IRAccessFieldVirtualExpression) {
                const afse = exps as IRAccessFieldVirtualExpression;
                const tinfo = this.typeInfoManager.getTypeInfo(afse.eexptype.tkeystr);

                const mname = TransformCPPNameManager.convertIdentifier(afse.fieldname);
                if(this.isNominalTypeUniqueEntity(afse.eexptype)) {
                    return `${this.emitIRSimpleExpression(afse.eexp, false)}${tinfo.getAccessor()}${mname}`;
                }
                else {
                    const allsubs = this.getAllConcreteSubtypeOptionsForNominalType(afse.eexptype as IRNominalTypeSignature);
                    const fieldpfxs = allsubs.map((tt) => {
                        const fidx = tt.saturatedBFieldInfo.findIndex((bf) => bf.fname === afse.fieldname);
                        return tt.saturatedBFieldInfo.slice(0, fidx + 1);
                    });

                    const ffp = fieldpfxs[0];
                    const safepfxs = fieldpfxs.every((fp) => {
                        if(fp.length !== ffp.length) {
                            return false;
                        }
                        for(let i = 0; i < fp.length; i++) {
                            if(fp[i].fkey !== ffp[i].fkey) {
                                return false;
                            }
                        }
                        return true;
                    });

                    if(safepfxs) {
                        const rtype = this.typeInfoManager.emitTypeAsStd(afse.fieldtype.tkeystr);
                        const offset = ffp.slice(0, -1).map((bf) => this.typeInfoManager.getTypeInfo(bf.ftype.tkeystr).slotcount).reduce((a, b) => a + b, 0);
                        return `${this.emitIRSimpleExpression(afse.eexp, false)}.accessfield<${rtype}, ${offset}>()`;
                    }
                    else {
                        assert(false, "CPPEmitter: need to implement safe virtual field access for non-unique entity nominal types");
                    }
                }
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
            else if(ttag === IRExpressionTag.IRConstructorStandardEntityExpression) {
                const iccse = exp as IRConstructorStandardEntityExpression;
                const tlinfo = this.typeInfoManager.getTypeInfo(iccse.constype.tkeystr);
                
                if(tlinfo.tag === LayoutTag.Value) {
                    const cce = TransformCPPNameManager.generateNameForConstructor(iccse.constype.tkeystr);
                    const args = iccse.values.map((vv) => this.emitIRSimpleExpression(vv, true)).join(", ");
                    return `${cce}{${args}}`;
                }
                else {
                    const cce = TransformCPPNameManager.generateNameForConstructor(iccse.constype.tkeystr);
                    const args = iccse.values.map((vv) => this.emitIRSimpleExpression(vv, true)).join(", ");
                    return `ᐸRuntimeᐳ::${cce}_allocator.allocate(${args})`;
                }
            }
            else if(ttag === IRExpressionTag.IRConstructorListSingletonsExpression) {
                const iclse = exp as IRConstructorListSingletonsExpression;
                const cce = TransformCPPNameManager.convertTypeKey(iclse.constype.tkeystr);
                const args = iclse.elements.map((vv) => this.emitIRSimpleExpression(vv, true)).join(", ");

                const ldecl = this.irasm.alltypes.get(iclse.constype.tkeystr) as IRListTypeDecl;
                const tinfot = this.typeInfoManager.getTypeInfo(ldecl.oftype.tkeystr);
                if(iclse.elements.length <= LIST_T_CAPACITY(tinfot.bytesize)) {
                    const inlinetypeinfo = `ᐸRuntimeᐳ::g_typeinfo_${cce}Inline`;
                    return `${cce}::smliteral({${args}}, &${inlinetypeinfo})`;
                }
                else if(iclse.elements.length <= 2 * LIST_T_CAPACITY(tinfot.bytesize)) {
                    const treetypeinfo = `ᐸRuntimeᐳ::g_typeinfo_${cce}Tree`;
                    return `${cce}::slliteral({${args}}, &${treetypeinfo})`;
                }
                else {
                    assert(false, "CPPEmitter: need to implement list singleton construction for larger allocation");
                }
            }
            else if(ttag === IRExpressionTag.IRInvokeSimpleExpression) {
                const iise = exp as IRInvokeSimpleExpression;                
                
                const aargs = iise.args.map((arg) => this.emitIRSimpleExpression(arg, true));
                return `${TransformCPPNameManager.convertInvokeKey(iise.ikey)}(${aargs.join(", ")})`;
            }
            else if(ttag === IRExpressionTag.IRInvokeVirtualSimpleExpression) {
                assert(false, "CPPEmitter: need to implement virtual simple invoke expression");
            }
            else if(ttag === IRExpressionTag.IRInvokeSimpleWithImplicitsExpression) {
                const iise = exp as IRInvokeSimpleWithImplicitsExpression;
                
                const aargs = iise.args.map((arg) => this.emitIRSimpleExpression(arg, true));
                return `${TransformCPPNameManager.convertInvokeKey(iise.ikey)}(${aargs.join(", ")})`;
            }
            else if(ttag === IRExpressionTag.IRInvokeVirtualWithImplicitsExpression) {
                assert(false, "CPPEmitter: need to implement virtual with implicits invoke expression");
            }
            else if(ttag === IRExpressionTag.IRInterpolateFormatCStringExpression) {
                const ifcsexp = exp as IRInterpolateFormatCStringExpression;
                const icfs = this.emitIRSimpleExpression(ifcsexp.fmtString, true);
                const argstrs = ifcsexp.args.map((arg) => this.emitIRSimpleExpression(arg, true));
                return `${RUNTIME_NAMESPACE}::XFCString::interpolate<${argstrs.length}>(${icfs}.fcid, { ${argstrs.join(", ")} })`;
            }
            else if(ttag === IRExpressionTag.IRInterpolateFormatStringExpression) {
                assert(false, "CPPEmitter: need to implement interpolate format string expression");
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
            const tasi = stmt as IRTempAssignStdInvokeStatement;
            
            const vdecltype = this.typeInfoManager.emitTypeAsStd(tasi.ttype.tkeystr);
            const wval = this.emitExpression(tasi.rhs, true);
            return `${vdecltype} ${TransformCPPNameManager.convertIdentifier(tasi.tname)} = ${wval};`
        }
        else if(ttag === IRStatementTag.IRTempAssignRefInvokeStatement) {
            const tare = stmt as IRTempAssignRefInvokeStatement;
            
            const vdecltype = this.typeInfoManager.emitTypeAsStd(tare.ttype.tkeystr);
            const wval = this.emitExpression(tare.rhs, true);
            return `${vdecltype} ${TransformCPPNameManager.convertIdentifier(tare.tname)} = ${wval};`
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
        else if(ttag === IRStatementTag.IRVariableInitializationDirectInvokeWithImplicitStatement) {
            const vistmt = stmt as IRVariableInitializationDirectInvokeWithImplicitStatement;

            const vdecltype = this.typeInfoManager.emitTypeAsStd(vistmt.vtype.tkeystr);
            const wval = this.emitExpression(vistmt.initexp, true);
            return `${vdecltype} ${TransformCPPNameManager.convertIdentifier(vistmt.vname)} = ${wval};`
        }
        else if(ttag === IRStatementTag.IRVariableInitializationDirectConstructorStatement) {
            const vistmt = stmt as IRVariableInitializationDirectConstructorStatement;

            const vdecltype = this.typeInfoManager.emitTypeAsStd(vistmt.vtype.tkeystr);
            const wval = this.emitExpression(vistmt.initexp, true);
            return `${vdecltype} ${TransformCPPNameManager.convertIdentifier(vistmt.vname)} = ${wval};`
        }
        else if(ttag === IRStatementTag.IRVariableInitializationDirectConstructorWithBoxStatement) {
            const vistmt = stmt as IRVariableInitializationDirectConstructorWithBoxStatement;

            const vdecltype = this.typeInfoManager.emitTypeAsStd(vistmt.vtype.tkeystr);
            const ctype = TransformCPPNameManager.convertTypeKey(vistmt.vtype.tkeystr); 
            const wval = this.emitExpression(vistmt.initexp, true);
            return `${vdecltype} ${TransformCPPNameManager.convertIdentifier(vistmt.vname)} = ${ctype}(${wval});`
        }
        else if(ttag === IRStatementTag.IRVariableAssignmentStatement) {
            const vistmt = stmt as IRVariableAssignmentStatement;

            const wval = this.emitIRSimpleExpression(vistmt.aexp, true);
            return `${TransformCPPNameManager.convertIdentifier(vistmt.vname)} = ${wval};`
        }
        else if(ttag === IRStatementTag.IRVariableAssignmentDirectInvokeStatement) {
            const vistmt = stmt as IRVariableAssignmentDirectInvokeStatement;

            const wval = this.emitExpression(vistmt.aexp, true);
            return `${TransformCPPNameManager.convertIdentifier(vistmt.vname)} = ${wval};`
        }
        else if(ttag === IRStatementTag.IRVariableAssignmentDirectInvokeWithImplicitStatement) {
            const vistmt = stmt as IRVariableAssignmentDirectInvokeWithImplicitStatement;

            const wval = this.emitExpression(vistmt.aexp, true);
            return `${TransformCPPNameManager.convertIdentifier(vistmt.vname)} = ${wval};`
        }
        else if(ttag === IRStatementTag.IRVariableAssignmentDirectConstructorStatement) {
            const vistmt = stmt as IRVariableAssignmentDirectConstructorStatement;

            const wval = this.emitExpression(vistmt.aexp, true);
            return `${TransformCPPNameManager.convertIdentifier(vistmt.vname)} = ${wval};`
        }
        else if(ttag === IRStatementTag.IRVariableAssignmentDirectConstructorWithBoxStatement) {
            const vistmt = stmt as IRVariableAssignmentDirectConstructorWithBoxStatement;

            const ctype = TransformCPPNameManager.convertTypeKey(vistmt.vtype.tkeystr); 
            const wval = this.emitExpression(vistmt.aexp, true);
            return `${TransformCPPNameManager.convertIdentifier(vistmt.vname)} = ${ctype}(${wval});`
        }
        else if(ttag === IRStatementTag.IRReturnVoidSimpleStatement) {
            return "return;";
        }
        else if(ttag === IRStatementTag.IRReturnValueSimpleStatement) {
            const ires = stmt as IRReturnValueSimpleStatement;
            return `return ${this.emitIRSimpleExpression(ires.retexp, true)};`;
        }
        else if(ttag === IRStatementTag.IRReturnDirectInvokeStatement) {
            const ires = stmt as IRReturnDirectInvokeStatement;
            return `return ${this.emitExpression(ires.retexp, true)};`;
        }
        else if(ttag === IRStatementTag.IRReturnDirectConstructStatement) {
            const irdcs = stmt as IRReturnDirectConstructStatement;
            return `return ${this.emitExpression(irdcs.retexp, true)};`;
        }
        else if(ttag === IRStatementTag.IRReturnDirectConstructWithBoxStatement) {
            const irdcwbs = stmt as IRReturnDirectConstructWithBoxStatement;
            const ctype = TransformCPPNameManager.convertTypeKey(irdcwbs.totype.tkeystr); 
            return `return ${ctype}(${this.emitExpression(irdcwbs.retexp, true)});`;
        }
        else if(ttag === IRStatementTag.IRReturnVoidImplicitStatement) {
            return "return;";
        }
        else if(ttag === IRStatementTag.IRReturnValueImplicitStatement) {
            const ires = stmt as IRReturnValueImplicitStatement;
            return `return ${this.emitIRSimpleExpression(ires.retexp, true)};`;
        }
        else if(ttag === IRStatementTag.IRReturnDirectInvokeImplicitStatement) {
            const ires = stmt as IRReturnDirectInvokeImplicitStatement;
            return `return ${this.emitExpression(ires.retexp, true)};`;
        }
        else if(ttag === IRStatementTag.IRReturnDirectInvokeImplicitPassThroughStatement) {
            const ires = stmt as IRReturnDirectInvokeImplicitPassThroughStatement;
            return `return ${this.emitExpression(ires.retexp, true)};`;
        }
        else if(ttag === IRStatementTag.IRReturnDirectConstructImplicitStatement) {
            const irdcs = stmt as IRReturnDirectConstructImplicitStatement;
            return `return ${this.emitExpression(irdcs.retexp, true)};`;
        }
        else if(ttag === IRStatementTag.IRReturnDirectConstructWithBoxImplicitStatement) {
            const irdcwbs = stmt as IRReturnDirectConstructWithBoxImplicitStatement;
            const ctype = TransformCPPNameManager.convertTypeKey(irdcwbs.totype.tkeystr); 
            return `return ${ctype}(${this.emitExpression(irdcwbs.retexp, true)});`;
        }
        else if(ttag === IRStatementTag.IRVoidInvokeStatement) {
            const ivis = stmt as IRVoidInvokeStatement;
            
            return this.emitExpression(ivis.aexp, true) + ";";
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
            return `${RUNTIME_NAMESPACE}::X${iedzbc.optypechk}::checkDivisionByZero(${this.emitIRSimpleExpression(iedzbc.right, true)}, "${iedzbc.file}", ${iedzbc.sinfo.line});`;
        }
        else if(ttag === IRStatementTag.IRTypeDeclSizeRangeCheckCStringStatement) {
            const itdsrcc = stmt as IRTypeDeclSizeRangeCheckCStringStatement;
            const strarg = this.emitIRImmediateExpression(itdsrcc.strexp);
            const loc = `"${itdsrcc.file}", ${itdsrcc.sinfo.line}`;
            if(itdsrcc.min !== undefined && itdsrcc.max !== undefined) {
                return `${RUNTIME_NAMESPACE}::XCString::checkSizeRange(${strarg}, ${itdsrcc.min.slice(0, -1)}, ${itdsrcc.max.slice(0, -1)}, ${loc});`;
            }
            else if(itdsrcc.min !== undefined) {
                return `${RUNTIME_NAMESPACE}::XCString::checkSizeMin(${strarg}, ${itdsrcc.min.slice(0, -1)}, ${loc});`;
            }
            else if(itdsrcc.max !== undefined) {
                return `${RUNTIME_NAMESPACE}::XCString::checkSizeMax(${strarg}, ${itdsrcc.max.slice(0, -1)}, ${loc});`;
            }
            else {
                assert(false, "CPPEmitter: IRTypeDeclSizeRangeCheckCStringStatement with no min or max bound");
            }
        }
        else if(ttag === IRStatementTag.IRTypeDeclSizeRangeCheckUnicodeStringStatement) {
            const itdsrcu = stmt as IRTypeDeclSizeRangeCheckUnicodeStringStatement;
            const strarg = this.emitIRImmediateExpression(itdsrcu.strexp);
            const loc = `"${itdsrcu.file}", ${itdsrcu.sinfo.line}`;
            if(itdsrcu.min !== undefined && itdsrcu.max !== undefined) {
                return `${RUNTIME_NAMESPACE}::XString::checkSizeRange(${strarg}, ${itdsrcu.min.slice(0, -1)}, ${itdsrcu.max.slice(0, -1)}, ${loc});`;
            }
            else if(itdsrcu.min !== undefined) {
                return `${RUNTIME_NAMESPACE}::XString::checkSizeMin(${strarg}, ${itdsrcu.min.slice(0, -1)}, ${loc});`;
            }
            else if(itdsrcu.max !== undefined) {
                return `${RUNTIME_NAMESPACE}::XString::checkSizeMax(${strarg}, ${itdsrcu.max.slice(0, -1)}, ${loc});`;
            }
            else {
                assert(false, "CPPEmitter: IRTypeDeclSizeRangeCheckUnicodeStringStatement with no min or max bound");
            }
        }
        else if(ttag === IRStatementTag.IRTypeDeclFormatCheckCStringStatement) {
            const vvexp = stmt as IRTypeDeclFormatCheckCStringStatement;
            const reval = `${RUNTIME_NAMESPACE}::g_cregexs[${vvexp.re.regexID}]`;

            return `${RUNTIME_NAMESPACE}::XCString::checkFormat(${this.emitIRImmediateExpression(vvexp.strexp)}, ${reval}, "${vvexp.file}", ${vvexp.sinfo.line});`;
        }
        else if(ttag === IRStatementTag.IRTypeDeclFormatCheckUnicodeStringStatement) {
            assert(false, "CPPEmitter: need to implement type declaration format check for unicode string");
        }
        else if(ttag === IRStatementTag.IRTypeDeclInvariantCheckStatement) {
            const itdics = stmt as IRTypeDeclInvariantCheckStatement;

            const invchk = `${TransformCPPNameManager.generateNameForInvariantFunction(itdics.tkey, itdics.invariantidx)}(${this.emitIRImmediateExpression(itdics.targetValue)})`;
            const dtag = itdics.diagnosticTag !== undefined ? `"${itdics.diagnosticTag}"` : "nullptr";
            return `ᐸRuntimeᐳ::bsq_invariant((bool)(${invchk}), "${itdics.file}", ${itdics.sinfo.line}, ${dtag}, "Failed Invariant");`;
        }
        else if(ttag === IRStatementTag.IREntityInvariantCheckStatement) {
            const iedics = stmt as IREntityInvariantCheckStatement;
            
            const args = iedics.args.map((arg) => this.emitIRImmediateExpression(arg));
            const invchk = `${TransformCPPNameManager.generateNameForInvariantFunction(iedics.tkey, iedics.invariantidx)}(${args.join(", ")})`;

            const dtag = iedics.diagnosticTag !== undefined ? `"${iedics.diagnosticTag}"` : "nullptr";
            return `ᐸRuntimeᐳ::bsq_invariant((bool)(${invchk}), "${iedics.file}", ${iedics.sinfo.line}, ${dtag}, "Failed Invariant");`;
        }
        else if(ttag === IRStatementTag.IRPreconditionCheckStatement) {
            const ipcs = stmt as IRPreconditionCheckStatement;

            const prechk = `${TransformCPPNameManager.generateNameForInvokePreconditionCheck(ipcs.ikey, ipcs.requiresidx)}(${ipcs.args.map((arg) => this.emitIRImmediateExpression(arg)).join(", ")})`
            const dtag = ipcs.diagnosticTag !== undefined ? `"${ipcs.diagnosticTag}"` : "nullptr";
            return `ᐸRuntimeᐳ::bsq_requires((bool)(${prechk}), "${ipcs.file}", ${ipcs.sinfo.line}, ${dtag}, "Failed Requires");`;
        }
        else if(ttag === IRStatementTag.IRPostconditionCheckStatement) {
            const ipcs = stmt as IRPostconditionCheckStatement;

            const postchk = `${TransformCPPNameManager.generateNameForInvokePostconditionCheck(ipcs.ikey, ipcs.ensuresidx)}(${ipcs.args.map((arg) => this.emitIRImmediateExpression(arg)).join(", ")})`
            const dtag = ipcs.diagnosticTag !== undefined ? `"${ipcs.diagnosticTag}"` : "nullptr";
            return `ᐸRuntimeᐳ::bsq_ensures((bool)(${postchk}), "${ipcs.file}", ${ipcs.sinfo.line}, ${dtag}, "Failed Ensures");`;
        }
        else if(ttag === IRStatementTag.IRAbortStatement) {
            const ias = stmt as IRAbortStatement;
            return `${RUNTIME_NAMESPACE}::bsq_abort("${ias.file}", ${ias.sinfo.line}, nullptr, nullptr);`;
        }
        else if(ttag === IRStatementTag.IRAssertStatement) {
            const ias = stmt as IRAssertStatement;
            return `${RUNTIME_NAMESPACE}::bsq_assert((bool)(${this.emitIRSimpleExpression(ias.cond, true)}), "${ias.file}", ${ias.sinfo.line}, nullptr, "Assertion Failed");`;
        }
        else if(ttag === IRStatementTag.IRAssumeStatement) {
            return ";"; //nop for execution
        }
        else if(ttag === IRStatementTag.IRValidateStatement) {
            const ivs = stmt as IRValidateStatement;
            const ttagstr = ivs.diagnosticTag !== undefined ? `"${ivs.diagnosticTag.slice(1, -1)}"` : "nullptr";
            return `${RUNTIME_NAMESPACE}::bsq_validate((bool)(${this.emitIRSimpleExpression(ivs.cond, true)}), "${ivs.file}", ${ivs.sinfo.line}, ${ttagstr}, "Validation Failed");`;
        }
        else if(ttag === IRStatementTag.IRDebugStatement) {
            const ids = stmt as IRDebugStatement;

            const emf = `[=](){ BSQ_emit${TransformCPPNameManager.convertTypeKey(ids.oftype.tkeystr)}(${this.emitIRSimpleExpression(ids.dbgexp, true)}); }`;
            return `ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.debug_emit(${emf});`;
        }
        else {
            assert(false, `CPPEmitter: Unsupported IR atomic statement type -- ${stmt.constructor.name}`);
        }
    }

    private emitIRSimpleIfStatement(ifstmt: IRSimpleIfStatement, isfinal: boolean, indent: string | undefined): string {
        const ttest = this.emitIRSimpleExpression(ifstmt.cond, true);

        const bindent = indent !== undefined ? indent + "    " : undefined;
        const tbody = this.emitStatementList(ifstmt.tblock.statements, undefined, undefined, bindent);

        return `if(${ttest}) ${tbody}${isfinal ? "" : "\n"}`;
    }

    private emitIRSimpleIfElseStatement(ifstmt: IRSimpleIfElseStatement, isfinal: boolean, indent: string | undefined): string {
        const ttest = this.emitIRSimpleExpression(ifstmt.cond, true);

        const bindent = indent !== undefined ? indent + "    " : undefined;
        const tbody = this.emitStatementList(ifstmt.tblock.statements, undefined, undefined, bindent);
        const fbody = this.emitStatementList(ifstmt.eblock.statements, undefined, undefined, bindent);

        let ichk = " ";
        if(indent !== undefined) {
            ichk = `\n${bindent}`;
        }

        return `if(${ttest}) ${tbody}${ichk}else ${fbody}${isfinal ? "" : "\n"}`;
    }

    private emitStatement(stmt: IRStatement, isfinal: boolean, indent: string | undefined): string {
        if(stmt instanceof IRAtomicStatement) {
            return this.emitAtomicStatement(stmt);
        }
        else if(stmt instanceof IRSimpleIfStatement) {
            return this.emitIRSimpleIfStatement(stmt, isfinal, indent);
        }
        else if(stmt instanceof IRSimpleIfElseStatement) {
            return this.emitIRSimpleIfElseStatement(stmt, isfinal, indent);
        }
        else {
            assert(false, `CPPEmitter: Unsupported IR statement type -- ${stmt.constructor.name}`);
        }
    }

    private emitStatementList(stmts: IRStatement[], prefx: string[] | undefined, postfix: string[] | undefined, indent: string | undefined): string {
        const slstrs = stmts.map((stmt, ii) => this.emitStatement(stmt, postfix === undefined && ii === stmts.length - 1, indent));
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

        const ideclstr = `Bool ${fname}(${params.join(", ")});`;
        const idefstr = `Bool ${fname}(${params.join(", ")}) ${bodystr}`;

        return [ideclstr, idefstr];
    }

    private emitValidateFunction(ival: IRValidateDecl, tdecl: IRAbstractNominalTypeDecl, pinfo: {pname: string, ptype: IRTypeSignature}[]): [string, string] {
        const fname = TransformCPPNameManager.generateNameForValidateFunction(tdecl.tkey, ival.validateidx);
        const params = pinfo.map((p) => `${this.typeInfoManager.emitTypeAsParameter(p.ptype.tkeystr, false)} ${TransformCPPNameManager.convertIdentifier(p.pname)}`);

        const finalv = `return ${this.emitIRSimpleExpression(ival.value, true)};`;
        const bodystr = this.emitStatementList(ival.stmts, undefined, [finalv], "");

        const ideclstr = `Bool ${fname}(${params.join(", ")});`;
        const idefstr = `Bool ${fname}(${params.join(", ")}) ${bodystr}`;

        return [ideclstr, idefstr];
    }
   
    emitConstantDeclInfo(iconst: IRConstantDecl): [string, string] {
        const gvname = `BSQ_g_${TransformCPPNameManager.generateNameForConstantKey(iconst.ckey)}`;
        const staticsstr = `std::optional<${this.typeInfoManager.emitTypeAsStd(iconst.declaredType.tkeystr)}> ${gvname} = std::nullopt;`;
        
        const bodystr = this.emitStatementList(iconst.stmts, [`if(${gvname}.has_value()) { return ${gvname}.value(); } `], [`${gvname} = std::make_optional(${this.emitIRSimpleExpression(iconst.value, true)}); return ${gvname}.value();`], undefined);
        
        const cdeclstr = `${this.typeInfoManager.emitTypeAsStd(iconst.declaredType.tkeystr)} ${TransformCPPNameManager.generateNameForConstantKey(iconst.ckey)}();`;
        const cdefstr = `${staticsstr}\n${this.typeInfoManager.emitTypeAsStd(iconst.declaredType.tkeystr)} ${TransformCPPNameManager.generateNameForConstantKey(iconst.ckey)}() { ${bodystr} }`;

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

    private emitEnumTypeInfoDecl(tdecl: IREnumTypeDecl): string {
        const ctname = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
        const ttid = this.typeInfoManager.getTypeInfo(tdecl.tkey); 

        return `namespace ᐸRuntimeᐳ { inline constexpr TypeInfo g_typeinfo_${ctname} = {\n` +
        `        ${ttid.bsqtypeid},\n` +
        `        8,\n` +
        `        1,\n` +
        `        LayoutTag::Value,\n` +
        `        BSQ_TYPEINFO_NO_ESLOT,\n` +
        `        nullptr,\n` +
        `        nullptr,\n` +
        `        0,\n` +
        `        nullptr,\n` +
        `        0,\n` +
        `        nullptr,\n` +
        `        0,` +
        `        "${tdecl.tkey}"\n` +
        `    };\n` +
        `}`;
    }

    private emitListTypeInfoDecl(tdecl: IRListTypeDecl): [string, string] {
        const ctname = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
        const ttid = this.typeInfoManager.getTypeInfo(tdecl.tkey);

        const oftrepr = this.typeInfoManager.emitTypeAsStd(tdecl.oftype.tkeystr);
        const ofttid = this.typeInfoManager.getTypeInfo(tdecl.oftype.tkeystr);

        let eemask: string;
        if(ofttid.tag === LayoutTag.Ref) {
            eemask = "1";
        }
        else {
            if(ofttid.ptrmask !== undefined) {
                eemask = ofttid.ptrmask;
            }
            else {
                eemask = Array(ofttid.slotcount).fill("0").join("");
            }
        }
        
        let inlinemask: string | undefined = undefined; 
        let leafmask: string | undefined = undefined;
        if(eemask.includes("1") || eemask.includes("2")) {
            const icapacity = LIST_T_CAPACITY(ofttid.bytesize);

            inlinemask = "0" + Array(icapacity).fill(eemask).join("");
            leafmask = "0" + Array(2 * icapacity).fill(eemask).join("");
        }
        
        const posrb_treeleafid = ttid.bsqtypeid - 5;
        const posrb_treenodeid = ttid.bsqtypeid - 4;
        const posrb_treeid = ttid.bsqtypeid - 3;

        const listinlineid = ttid.bsqtypeid - 2;
        const listtreeid = ttid.bsqtypeid - 1;

        const tidecls = `namespace ᐸRuntimeᐳ {\n` +
        `    inline constexpr TypeInfo g_typeinfo_PosRBTreeLeaf_${ctname} = g_typeinfo_PosRBTreeLeaf_generate<${oftrepr}, ListTTreeContent<${oftrepr}, ${posrb_treeleafid}>::LIST_T_MAX_LEAF_SIZE>(${posrb_treeleafid}, ${ofttid.slotcount}, ${leafmask !== undefined ? `"${leafmask}"` : "nullptr"}, "PosRBTreeLeaf_${ctname}");\n` +
        `    inline constexpr TypeInfo g_typeinfo_PosRBTreeNode_${ctname} = g_typeinfo_PosRBTreeNode_generate<${oftrepr}, ListTTreeContent<${oftrepr}, ${posrb_treeleafid}>::LIST_T_MAX_LEAF_SIZE>(${posrb_treenodeid}, "PosRBTreeNode_${ctname}");\n` +
        `    inline constexpr TypeInfo g_typeinfo_PosRBTree_${ctname} = g_typeinfo_PosRBTree_generate<${oftrepr}, ListTTreeContent<${oftrepr}, ${posrb_treeleafid}>::LIST_T_MAX_LEAF_SIZE, ${posrb_treeid}>(${posrb_treeid}, "PosRBTree_${ctname}");\n` +
        '\n' +
        `    extern thread_local GCAllocator<PosRBTreeLeaf<${oftrepr}, ListTTreeContent<${oftrepr}, ${posrb_treeleafid}>::LIST_T_MAX_LEAF_SIZE>> PosRBTreeLeaf_${ctname}_allocator;\n` +
        `    extern thread_local GCAllocator<PosRBTreeNode<${oftrepr}, ListTTreeContent<${oftrepr}, ${posrb_treeleafid}>::LIST_T_MAX_LEAF_SIZE>> PosRBTreeNode_${ctname}_allocator;\n` +
        '\n' +
        `    inline constexpr TypeInfo g_typeinfo_${ctname}Inline = g_typeinfo_ListTInlineContent_generate<${oftrepr}>(${listinlineid}, ${ofttid.slotcount}, ${inlinemask !== undefined ? `"${inlinemask}"` : "nullptr"}, "${ctname}Inline");\n` +
        `    inline constexpr TypeInfo g_typeinfo_${ctname}Tree = g_typeinfo_ListTTreeContent<${oftrepr}, ${posrb_treeid}>(${listtreeid}, "${ctname}TreeContent");\n` +
        `    inline constexpr TypeInfo g_typeinfo_${ctname} = g_typeinfo_ListT_generate<${oftrepr}, ${posrb_treeid}>(${ttid.bsqtypeid}, "${ctname}");\n` +
        `}`;

        const tidefs = `namespace ᐸRuntimeᐳ {\n` +
        `    template<> const TypeInfo* XList<${oftrepr}, ${ttid.bsqtypeid}>::s_inlinetypeinfo = &g_typeinfo_${ctname}Inline;\n` +
        `    template<> const TypeInfo* XList<${oftrepr}, ${ttid.bsqtypeid}>::s_treetypeinfo = &g_typeinfo_${ctname}Tree;\n` +
        '\n' +
        `    thread_local GCAllocator<PosRBTreeLeaf<${oftrepr}, ListTTreeContent<${oftrepr}, ${posrb_treeleafid}>::LIST_T_MAX_LEAF_SIZE>> PosRBTreeLeaf_${ctname}_allocator(&g_typeinfo_PosRBTreeLeaf_${ctname});\n` +
        `    thread_local GCAllocator<PosRBTreeNode<${oftrepr}, ListTTreeContent<${oftrepr}, ${posrb_treeleafid}>::LIST_T_MAX_LEAF_SIZE>> PosRBTreeNode_${ctname}_allocator(&g_typeinfo_PosRBTreeNode_${ctname});\n` +
        '\n' +
        `    template<> const TypeInfo* PosRBTree<${oftrepr}, ListTTreeContent<${oftrepr}, ${posrb_treeleafid}>::LIST_T_MAX_LEAF_SIZE, ${posrb_treeid}>::s_leaftypeinfo = &g_typeinfo_PosRBTreeLeaf_${ctname};\n` +
        `    template<> thread_local GCAllocator<PosRBTreeLeaf<${oftrepr}, ListTTreeContent<${oftrepr}, ${posrb_treeleafid}>::LIST_T_MAX_LEAF_SIZE>>* PosRBTree<${oftrepr}, ListTTreeContent<${oftrepr}, ${posrb_treeleafid}>::LIST_T_MAX_LEAF_SIZE, ${posrb_treeid}>::s_leafallocator = &PosRBTreeLeaf_${ctname}_allocator;\n` +
        `    template<> const TypeInfo* PosRBTree<${oftrepr}, ListTTreeContent<${oftrepr}, ${posrb_treeleafid}>::LIST_T_MAX_LEAF_SIZE, ${posrb_treeid}>::s_nodetypeinfo = &g_typeinfo_PosRBTreeNode_${ctname};\n` +
        `    template<> thread_local GCAllocator<PosRBTreeNode<${oftrepr}, ListTTreeContent<${oftrepr}, ${posrb_treeleafid}>::LIST_T_MAX_LEAF_SIZE>>* PosRBTree<${oftrepr}, ListTTreeContent<${oftrepr}, ${posrb_treeleafid}>::LIST_T_MAX_LEAF_SIZE, ${posrb_treeid}>::s_nodeallocator = &PosRBTreeNode_${ctname}_allocator;\n` +
        `}`;

        return [tidecls, tidefs];
    }

    private emitEntityTypeInfoDecl(tdecl: IRAbstractEntityTypeDecl): string {
        const ctname = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
        const ttid = this.typeInfoManager.getTypeInfo(tdecl.tkey);

        const superlist = (this.irasm.concretesupertypes.get(tdecl.tkey) as IRTypeSignature[]).map((tt) => this.typeInfoManager.getTypeInfo(tt.tkeystr).bsqtypeid).sort();
        let superdecl = "";
        let supertable = "nullptr";
        if(superlist.length !== 0) {
            superdecl = `    inline constexpr uint32_t g_supertypes_${ctname}[${superlist.length}] = { ${superlist.join(", ")} };\n`;
            supertable = `g_supertypes_${ctname}`;
        }
        
        let ftdecl = "";
        let ftable = "nullptr";
        if(ttid.ftable.length !== 0) {
            ftdecl = `    inline constexpr FieldOffsetInfo g_ftable_${ctname}[${ttid.ftable.length}] = {\n` +
            ttid.ftable.map((fte) => {
                const fttid = this.typeInfoManager.getTypeInfo(fte.ftype.tkeystr);
                return `        { ${fte.fid}, ${fttid.bsqtypeid}, ${fte.offset * 8}, ${fte.offset}, "${fte.fkey}", "${fte.fname}" }`;
            }).join(",\n") + "\n" +
            `    };\n`;
            ftable = `g_ftable_${ctname}`;
        }

        return `namespace ᐸRuntimeᐳ {\n` +
            superdecl +
            ftdecl +
            `    inline constexpr TypeInfo g_typeinfo_${ctname} = {\n` +
            `        ${ttid.bsqtypeid},\n` +
            `        ${ttid.bytesize},\n` +
            `        ${ttid.slotcount},\n` +
            `        LayoutTag::${ttid.tag},\n` +
            `        BSQ_TYPEINFO_NO_ESLOT,\n` +
            `        ${ttid.ptrmask !== undefined ? ('"' + ttid.ptrmask + '"') : "nullptr"},\n` +
            `        ${supertable},\n` +
            `        ${superlist.length},\n` +
            `        ${ftable},\n` +
            `        ${ttid.ftable.length},\n` +
            `        ${ttid.itable.length !== 0 ? "xxx" : "nullptr"},\n` +
            `        ${ttid.itable.length},\n` +
            `        "${tdecl.tkey}"\n` +
            `    };\n` +
            `}`;
    }

     private emitEntityTypeInfoWAllocInfo(tdecl: IRAbstractEntityTypeDecl): [string, string] {
        const ctname = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
        const ttid = this.typeInfoManager.getTypeInfo(tdecl.tkey); 

        const superlist = (this.irasm.concretesupertypes.get(tdecl.tkey) as IRTypeSignature[]).map((tt) => this.typeInfoManager.getTypeInfo(tt.tkeystr).bsqtypeid).sort();
        let superdecl = "";
        let supertable = "nullptr";
        if(superlist.length !== 0) {
            superdecl = `    inline constexpr uint32_t g_supertypes_${ctname}[${superlist.length}] = { ${superlist.join(", ")} };\n`;
            supertable = `&g_supertypes_${ctname}`;
        }

        let ftdecl = "";
        let ftable = "nullptr";
        if(ttid.ftable.length !== 0) {
            ftdecl = `    inline constexpr FieldOffsetInfo g_ftable_${ctname}[${ttid.ftable.length}] = {\n` +
            ttid.ftable.map((fte) => {
                const fttid = this.typeInfoManager.getTypeInfo(fte.ftype.tkeystr);
                return `        { ${fte.fid}, ${fttid.bsqtypeid}, ${fte.offset * 8}, ${fte.offset}, "${fte.fkey}", "${fte.fname}" }`;
            }).join(",\n") + "\n" +
            `    };\n`;
            ftable = `g_ftable_${ctname}`;
        }

        return [`namespace ᐸRuntimeᐳ {\n` +
            superdecl +
            ftdecl +
            `    inline constexpr TypeInfo g_typeinfo_${ctname} = {\n` +
            `        ${ttid.bsqtypeid},\n` +
            `        ${ttid.bytesize},\n` +
            `        ${ttid.slotcount},\n` +
            `        LayoutTag::${ttid.tag},\n` +
            `        BSQ_TYPEINFO_NO_ESLOT,\n` +
            `        ${ttid.ptrmask !== undefined ? ('"' + ttid.ptrmask + '"') : "nullptr"},\n` +
            `        ${supertable},\n` +
            `        ${superlist.length},\n` +
            `        ${ftable},\n` +
            `        ${ttid.ftable.length},\n` +
            `        ${ttid.itable.length !== 0 ? "xxx" : "nullptr"},\n` +
            `        ${ttid.itable.length},\n` +
            `        "${tdecl.tkey}"\n` +
            `    };\n` +
            `    extern thread_local GCAllocator<${ctname}> ${ctname}_allocator;\n` +
            `}`,
            `namespace ᐸRuntimeᐳ { thread_local GCAllocator<${ctname}> ${ctname}_allocator(&g_typeinfo_${ctname}); }`
        ];
    }

    private emitConceptTypeInfoDecl(tdecl: IRAbstractEntityTypeDecl): string {
        const ctname = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
        const ttid = this.typeInfoManager.getTypeInfo(tdecl.tkey); 

        return `namespace ᐸRuntimeᐳ { inline constexpr TypeInfo g_typeinfo_${ctname} = {\n` +
            `        ${ttid.bsqtypeid},\n` +
            `        ${ttid.bytesize},\n` +
            `        ${ttid.slotcount},\n` +
            `        LayoutTag::Tagged,\n` +
            `        BSQ_TYPEINFO_NO_ESLOT,\n` +
            `        ${ttid.ptrmask !== undefined ? ('"' + ttid.ptrmask + '"') : "nullptr"},\n` +
            `        nullptr,\n` +
            `        0,\n` +
            `        nullptr,\n` +
            `        0,\n` +
            `        nullptr,\n` +
            `        0,\n` +
            `        "${tdecl.tkey}"\n` +
            `    };\n` +
            `}`;
    }

    private emitRegexInfos(cregexs: IRCRegex[], uregexs: IRURegex[]): [string, string] {
        const redecl = `namespace ᐸRuntimeᐳ {\n` +
        `    extern std::array<std::basic_regex<char>, ${cregexs.length}> g_cregexs;\n` +
        `    extern std::array<std::basic_regex<char32_t>, ${uregexs.length}> g_uregexs;\n` +
        `}`;

        const cflags = "std::regex::ECMAScript | std::regex::nosubs";
        const uflags = "std::regex::ECMAScript | std::regex::nosubs";
        const redef = `namespace ᐸRuntimeᐳ {\n` +
        `    std::array<std::basic_regex<char>, ${cregexs.length}> g_cregexs = { ${cregexs.map((re) => `std::basic_regex<char>("${re.cppregex}", ${cflags})`).join(", ")} };\n` +
        `    std::array<std::basic_regex<char32_t>, ${uregexs.length}> g_uregexs = { ${uregexs.map((re) => `std::basic_regex<char32_t>(U"${re.cppregex}", ${uflags})`).join(", ")} };\n` +
        `}`;

        return [redecl, redef];
    }

    private emitEnumTypeDeclInfo(eenum: IREnumTypeDecl): [string, string] {
        const ctname = TransformCPPNameManager.convertTypeKey(eenum.tkey);

        const edecl = `class ${ctname} {\n` +
        `public:\n` +
        `    uint64_t value;\n\n` +
        `${eenum.members.map((mem) => `    static constinit ${ctname} ${TransformCPPNameManager.convertIdentifier(mem)};`).join("\n")}\n\n` +
        `    friend constexpr Bool operator==(const ${ctname}& lhs, const ${ctname}& rhs) { return ᐸRuntimeᐳ::XBool::from(lhs.value == rhs.value); }\n` +
        `    friend constexpr Bool operator<(const ${ctname}& lhs, const ${ctname}& rhs) { return ᐸRuntimeᐳ::XBool::from(lhs.value < rhs.value); }\n` +
        `    friend constexpr Bool operator>(const ${ctname}& lhs, const ${ctname}& rhs) { return ᐸRuntimeᐳ::XBool::from(rhs.value < lhs.value); }\n` +
        `    friend constexpr Bool operator!=(const ${ctname}& lhs, const ${ctname}& rhs) { return ᐸRuntimeᐳ::XBool::from(!(lhs.value == rhs.value)); }\n` +
        `    friend constexpr Bool operator<=(const ${ctname}& lhs, const ${ctname}& rhs) { return ᐸRuntimeᐳ::XBool::from(!(rhs.value < lhs.value)); }\n` +
        `    friend constexpr Bool operator>=(const ${ctname}& lhs, const ${ctname}& rhs) { return ᐸRuntimeᐳ::XBool::from(!(lhs.value < rhs.value)); }\n` +
        `};`;
        const bsqparsedecl = `std::optional<${ctname}> BSQ_parse${ctname}();`;
        const bsqemitdecl = `void BSQ_emit${ctname}(${ctname} vv);`;

        const mmarray = `inline constexpr std::array<const char*, ${eenum.members.length}> BSQ_enum_values_${ctname} = { ${eenum.members.map((mem) => `"${mem}"`).join(", ")} };`;
        const mdecls = `${eenum.members.map((mem, ii) => `${ctname} ${ctname}::${TransformCPPNameManager.convertIdentifier(mem)} = ${ctname}{${ii}};`).join("\n")}\n`;
        const bsqparsedef = `std::optional<${ctname}> BSQ_parse${ctname}() {\n` + 
        `    if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeType("${eenum.tkey}")) { return std::nullopt; };\n` +
        `    if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol('#')) { return std::nullopt; };\n` +
        '\n' +
        `    char enumstr[128] = {0};\n` + 
        `    if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeIdentifier(enumstr, 128)) { return std::nullopt; }\n` +
        `    auto eiter = std::find_if(BSQ_enum_values_${ctname}.cbegin(), BSQ_enum_values_${ctname}.cend(), [enumstr](const char* ev) { return strcmp(ev, enumstr) == 0; });\n` +
        `    if(eiter == BSQ_enum_values_${ctname}.cend()) { return std::nullopt; }\n` +
        '\n' +
        `    return std::make_optional(${ctname}{(uint64_t)std::distance(BSQ_enum_values_${ctname}.cbegin(), eiter)});\n` +  
        `}`;
        
        const bsqemitdef = `void BSQ_emit${ctname}(${ctname} vv) {\n` +
        `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitLiteralContent("${eenum.tkey}#");\n` +
        `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitLiteralContent(BSQ_enum_values_${ctname}[vv.value]);\n` +
        `}`;

        return [
            [edecl,  this.emitEnumTypeInfoDecl(eenum), bsqparsedecl, bsqemitdecl].join("\n"), 
            [mmarray, mdecls, bsqparsedef, bsqemitdef].join("\n")
        ];
    }

    private emitGeneralTypeDeclInfo(tdecl: IRTypedeclTypeDecl, chkextra: string[] | undefined): [string, string] {
        const ctname = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
        const ctrepr = this.typeInfoManager.emitTypeAsStd(tdecl.tkey);

        const voptttname = TransformCPPNameManager.convertTypeKey(tdecl.valuetype.tkeystr);
        const voptt = this.typeInfoManager.emitTypeAsStd(tdecl.valuetype.tkeystr);
        const valuetype = this.typeInfoManager.emitTypeAsMemberField(tdecl.valuetype.tkeystr);

        const vfuncinfo = tdecl.invariants.map((inv) => this.emitInvariantFunction(inv, tdecl, [{pname: "$value", ptype: tdecl.valuetype}]));
        const valfuncinfo = tdecl.validates.map((val) => this.emitValidateFunction(val, tdecl, [{pname: "$value", ptype: tdecl.valuetype}]));

        const tclass = `class ${ctname} {\n` +
            `public:\n` +
            `    ${valuetype} value;\n` +
            `    //All constructor and assignment defaults\n` +
            ((tdecl.iskeytype || tdecl.isnumerictype) ? 
            `    friend constexpr Bool operator==(const ${ctrepr}& lhs, const ${ctrepr}& rhs) { return lhs.value == rhs.value; }\n` +
            `    friend constexpr Bool operator<(const ${ctrepr}& lhs, const ${ctrepr}& rhs) { return lhs.value < rhs.value; }\n` +
            `    friend constexpr Bool operator>(const ${ctrepr}& lhs, const ${ctrepr}& rhs) { return rhs.value < lhs.value; }\n` +
            `    friend constexpr Bool operator!=(const ${ctrepr}& lhs, const ${ctrepr}& rhs) { return !(lhs.value == rhs.value); }\n` +
            `    friend constexpr Bool operator<=(const ${ctrepr}& lhs, const ${ctrepr}& rhs) { return !(rhs.value < lhs.value); }\n` +
            `    friend constexpr Bool operator>=(const ${ctrepr}& lhs, const ${ctrepr}& rhs) { return !(lhs.value < rhs.value); }\n` :
            "") +
            `};`;

        const typeinfodecl = this.emitEntityTypeInfoDecl(tdecl);

        const bsqparsedecl = `std::optional<${ctrepr}> BSQ_parse${ctname}();`;
        
        const bsqemitdecl = `void BSQ_emit${ctname}(${ctrepr} vv);`;
        const bsqemitdef = `void BSQ_emit${ctname}(${ctrepr} vv) {\n` +
        `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emit${voptttname}(vv.value);\n` +
        `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitSymbol('<'); \n` +
        `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitLiteralContent("${tdecl.tkey}"); \n` +
        `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitSymbol('>'); \n` +
        `}`;

        if(vfuncinfo.length === 0 && valfuncinfo.length === 0 && chkextra === undefined) {
            const bsqparsedef = `std::optional<${ctrepr}> BSQ_parse${ctname}() {\n` +
            `    std::optional<${voptt}> cc = ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.parse${voptttname}();\n` +
            `    if(!cc.has_value()) { return std::nullopt; }\n` +
            `    if(ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.peekSymbol('<')) {\n` +
            `        if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol('<')) { return std::nullopt; };\n` +
            `        if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeType("${tdecl.tkey}")) { return std::nullopt; };\n` +
            `        if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol('>')) { return std::nullopt; };\n` +
            '    }\n' +
            `    return std::make_optional<${ctrepr}>(${ctname}{ cc.value() });\n` +
            '}';

            return [
                [tclass, typeinfodecl, bsqparsedecl, bsqemitdecl].join("\n"), 
                [bsqparsedef, bsqemitdef].join("\n")
            ];
        }
        else {
            const ivdecls = [...vfuncinfo.map((vf) => vf[0]), ...valfuncinfo.map((vf) => vf[0])];
            const ivdefs = [...vfuncinfo.map((vf) => vf[1]), ...valfuncinfo.map((vf) => vf[1])];

            const allchks = [
                ...(chkextra || []),
                ...tdecl.allInvariants.map((inv) => {
                    const ifname = TransformCPPNameManager.generateNameForInvariantFunction(inv.containingtype.tkeystr, inv.ii);
                    return `if(!((bool)${ifname}(vv))) { return std::nullopt; };`;
                }),
                ...tdecl.allValidates.map((val) => {
                    const vfname = TransformCPPNameManager.generateNameForValidateFunction(val.containingtype.tkeystr, val.ii);
                    return `if(!((bool)${vfname}(vv))) { return std::nullopt; };`;
                })
            ].join("\n    ");

            const bsqparsedef = `std::optional<${ctrepr}> BSQ_parse${ctname}() {\n` +
            `    std::optional<${voptt}> cc = ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.parse${voptttname}();\n` +
            `    if(!cc.has_value()) { return std::nullopt; }\n` +
            `    if(ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.peekSymbol('<')) {\n` +
            `        if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol('<')) { return std::nullopt; };\n` +
            `        if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeType("${tdecl.tkey}")) { return std::nullopt; };\n` +
            `        if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol('>')) { return std::nullopt; };\n` +
            '    }\n\n' +
            `    ${voptt} vv = cc.value();\n` +
            `    ${allchks}\n\n` +
            `    return std::make_optional<${ctrepr}>(${ctname}{ vv });\n` +
            '}';

            return [
                [tclass, typeinfodecl, ivdecls, bsqparsedecl, bsqemitdecl].join("\n"), 
                [ivdefs, bsqparsedef, bsqemitdef].join("\n")
            ];
        }
    }

    private emitCStringTypeDeclInfo(tcstr: IRTypedeclCStringDecl): [string, string] {
        let echks: string[] = [];
        if(tcstr.rngchk !== undefined) {
            if(tcstr.rngchk.min === undefined) {
                echks.push(`if(${(tcstr.rngchk.max as string).slice(0, -1)} < vv.size()) { return std::nullopt; };`);
            }
            else if(tcstr.rngchk.max === undefined) {
                echks.push(`if(vv.size() < ${(tcstr.rngchk.min as string).slice(0, -1)}) { return std::nullopt; };`);
            }
            else {
                echks.push(`if((vv.size() < ${(tcstr.rngchk.min as string).slice(0, -1)}) || (${(tcstr.rngchk.max as string).slice(0, -1)} < vv.size())) { return std::nullopt; };`);
            }
        }
        if(tcstr.rechk !== undefined) {
            echks.push(`if(!std::regex_match(vv.begin(), vv.end(), ᐸRuntimeᐳ::g_cregexs[${tcstr.rechk.regexID}])) { return std::nullopt; };`);
        }

        return this.emitGeneralTypeDeclInfo(tcstr, echks);
    }

    private emitStringTypeDeclInfo(tstr: IRTypedeclStringDecl): [string, string] {
        assert(false, "CPPEmitter: need to implement string type decl emission");
    }

    private emitFCStringDefInfo(tfcstr: IRLiteralFormatCStringExpression[]): string {
        const ddefs = tfcstr.map((def) => {
            const fmts = def.fmts.map((ff) => {
                if(ff instanceof IRFormatStringTextComponent) {
                    return `std::make_pair(0, ${this.escapeLiteralCString(ff.bytes)[0]})`;
                }
                else {
                    const ffarg = ff as IRFormatStringArgComponent;
                    return `std::make_pair(${ffarg.aidx}, nullptr)`;
                }
            });

            const cmpsize = def.fmts.filter((ff) => ff instanceof IRFormatStringTextComponent).reduce((acc, ff) => acc + ff.bytes.length, 0);

            return `        XFCStringRepr{ { ${fmts.join(", ")} }, ${cmpsize}, ${def.fmtid} }`;
        });

        if(ddefs.length === 0) {
            return "namespace ᐸRuntimeᐳ { std::vector<XFCStringRepr> XFCString::g_formatStringReprs = {}; }";
        }
        else {
            return `namespace ᐸRuntimeᐳ {\n` +
            `    std::vector<XFCStringRepr> XFCString::g_formatStringReprs = {\n` +
            ddefs.join(",\n") + "\n" +
            `    };\n` +
            `}`;
        }
    }

    private emitFStringDefInfo(tfstr: IRLiteralFormatStringExpression[]): string {
        assert(tfstr.length === 0, "CPPEmitter: need to implement format string def emission");
        return "//TODO: pending implementation of format string defs";
    }

    private emitSomeTypeInfo(tdecl: IRSomeTypeDecl): [string, string] {
        const ctname = TransformCPPNameManager.convertTypeKey(tdecl.tkey);

        const voptttname = TransformCPPNameManager.convertTypeKey(tdecl.ttype.tkeystr);
        const voptt = this.typeInfoManager.emitTypeAsStd(tdecl.ttype.tkeystr);
        
        const declusing = `using ${ctname} = ${RUNTIME_NAMESPACE}::XSome<${voptt}>;`;
        const decltypeinfo = this.emitEntityTypeInfoDecl(tdecl);
        const declbsqparse = `std::optional<${ctname}> BSQ_parse${ctname}();`;
        const declbsqemit = `void BSQ_emit${ctname}(const ${ctname}& vv);`;

        const defbsqparse = `std::optional<${ctname}> BSQ_parse${ctname}() { if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeKeyword("some")) { return std::nullopt; } if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol('(')) { return std::nullopt; } auto vval = BSQ_parse${voptttname}(); if(!vval.has_value()) { return std::nullopt; } if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol(')')) { return std::nullopt; } return ${TransformCPPNameManager.generateNameForConstructor(ctname)}{vval.value()}; }`;
        const defbsqemit = `void BSQ_emit${ctname}(const ${ctname}& vv) { ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitLiteralContent("some"); ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitSymbol('('); BSQ_emit${voptttname}(vv.value); ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitSymbol(')'); }`;
        
        return [
            [declusing, decltypeinfo, declbsqparse, declbsqemit].join("\n"),
            [defbsqparse, defbsqemit].join("\n")
        ];
    }

    private emitOkTypeInfo(tdecl: IROkTypeDecl): [string, string] {
        assert(false, "CPPEmitter: need to implement ok type decl emission");
    }

    private emitFailTypeInfo(tdecl: IRFailTypeDecl): [string, string] {
        assert(false, "CPPEmitter: need to implement fail type decl emission");
    }

    private emitListTypeInfo(tdecl: IRListTypeDecl): [string, string] {
        const ctname = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
        const tinfo = this.typeInfoManager.getTypeInfo(tdecl.tkey);

        //const oftname = TransformCPPNameManager.convertTypeKey(tdecl.oftype.tkeystr);
        const voft = this.typeInfoManager.emitTypeAsStd(tdecl.oftype.tkeystr);
        
        const declusing = `using ${ctname} = ${RUNTIME_NAMESPACE}::XList<${voft}, ${tinfo.bsqtypeid}>;`;
        const [decltypeinfo, deftypeinfo] = this.emitListTypeInfoDecl(tdecl);
        const declbsqparse = `std::optional<${ctname}> BSQ_parse${ctname}();`;
        const declbsqemit = `void BSQ_emit${ctname}(const ${ctname}& vv);`;

        const defbsqparse = `std::optional<${ctname}> BSQ_parse${ctname}() {\n` +
        `    if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeType("${tdecl.tkey}")) { return std::nullopt; };\n` +
        `    if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol('{')) { return std::nullopt; };\n` +
        `    ${voft} varr[16] = {};\n` +
        `    size_t count = 0;\n` +
        `    bool first = true;\n` +
        `    while(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.peekSymbol('}')) {\n` +
        `        if(first) { first = false; } else { if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol(',')) { return std::nullopt; }; }\n` +
        `        std::optional<${this.typeInfoManager.emitTypeAsStd(tdecl.oftype.tkeystr)}> vv = BSQ_parse${TransformCPPNameManager.convertTypeKey(tdecl.oftype.tkeystr)}();\n` +
        `        if(!vv.has_value()) { return std::nullopt; }\n` +
        `        varr[count++] = vv.value();\n\n` +
        `        if(count >= 16) { break; /* TODO: implement dynamic growth */ }\n` +
        `    }\n` +
        `    if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol('}')) { return std::nullopt; };\n` +
        `    return std::make_optional<${ctname}>(${ctname}::palloc(varr, count));\n` +
        `}`;

        const defbsqemit = `void BSQ_emit${ctname}(const ${ctname}& vv) {\n` +
        `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitLiteralContent("${tdecl.tkey}"); \n` +
        `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitSymbol('{'); \n` +
        `    bool first = true;\n` +
        `    for(auto iter = vv.begin(); iter != vv.end(); ++iter) {\n` +
        `        if(first) { first = false; } else { ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.writeImmediate(", "); }\n` +
        `        BSQ_emit${TransformCPPNameManager.convertTypeKey(tdecl.oftype.tkeystr)}((*iter));\n` +
        `    }\n` +
        `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitSymbol('}'); \n` +
        `}`;
        
        return [
            [declusing, decltypeinfo, declbsqparse, declbsqemit].join("\n"),
            [deftypeinfo, defbsqparse, defbsqemit].join("\n")
        ];
    }

    private emitOptionTypeInfo(tdecl: IROptionTypeDecl): [string, string] {
        const ctname = TransformCPPNameManager.convertTypeKey(tdecl.tkey);

        const voptttname = TransformCPPNameManager.convertTypeKey(tdecl.ttype.tkeystr);
        const voptt = this.typeInfoManager.emitTypeAsStd(tdecl.ttype.tkeystr);
        
        const declusing = `using ${ctname} = ${RUNTIME_NAMESPACE}::XOption<${voptt}>;`;
        const decltypeinfo = this.emitConceptTypeInfoDecl(tdecl);
        const declbsqparse = `std::optional<${ctname}> BSQ_parse${ctname}();`;
        const declbsqemit = `void BSQ_emit${ctname}(const ${ctname}& vv);`;

        const sometypeinfo = TransformCPPNameManager.generateTypeInfoNameForTypeKey(tdecl.ttype.tkeystr);

        const defbsqparse = `std::optional<${ctname}> BSQ_parse${ctname}() {\n` +
        `    if(ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.testAndConsumeTokenIf(ᐸRuntimeᐳ::BSQONTokenType::LiteralNone)) { return ${ctname}::optnone; }\n` +
        `    auto somev = BSQ_parseSomeᐸ${voptttname}ᐳ();\n` +
        `    if(!somev.has_value()) { return std::nullopt; }\n` +
        `    return ${TransformCPPNameManager.generateNameForConstructor(ctname)}::fromSome(&${sometypeinfo}, somev.value());\n` +
        `}`;
        
        const defbsqemit = `void BSQ_emit${ctname}(const ${ctname}& vv) {\n` +
        `    if(vv.isNone()) { ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.writeImmediate("none"); }\n` +
        `    else { BSQ_emitSomeᐸ${voptttname}ᐳ(vv.asSome()); }\n` +
        `}`;
        
        return [
            [declusing, decltypeinfo, declbsqparse, declbsqemit].join("\n"),
            [defbsqparse, defbsqemit].join("\n")
        ];
    }

    private emitResultTypeInfo(tdecl: IRResultTypeDecl): [string, string] {
        assert(false, "CPPEmitter: need to implement result type decl emission");
    }

    private emitStdCommonEntityTypeInfo(tdecl: IREntityTypeDecl, tlinfo: TypeInfo, isRef: boolean): [string, string] {
        const ctname = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
        const ctrepr = this.typeInfoManager.emitTypeAsStd(tdecl.tkey);

        const vvaccess = tlinfo.getAccessor();
        let vvcons: [string, string];
        if(tlinfo.tag === LayoutTag.Value) {
            vvcons = [`${ctname}{`, `}`];
        }
        else {
            vvcons = [`ᐸRuntimeᐳ::${ctname}_allocator.allocate(` , ")"];
        }
        
        const iifieldargl = tdecl.saturatedBFieldInfo.map((bf) => { return {pname: `${TransformCPPNameManager.convertIdentifier("$" + bf.fname)}`, ptype: bf.ftype}; }); 
        const vfuncinfo = tdecl.invariants.map((inv) => this.emitInvariantFunction(inv, tdecl, iifieldargl));
        const valfuncinfo = tdecl.validates.map((val) => this.emitValidateFunction(val, tdecl, iifieldargl));

        const fdecllist = tdecl.saturatedBFieldInfo.map((bf) => {
            const ftypstr = this.typeInfoManager.emitTypeAsMemberField(bf.ftype.tkeystr);
            const fname = TransformCPPNameManager.convertIdentifier(bf.fname);
            return `    ${ftypstr} ${fname};`;
        });
        const tclass = `class ${ctname} {\n` +
            `public:\n` +
            `${fdecllist.join("    \n")}\n` +
            `    //All constructor and assignment defaults\n` +
            `};`;

        let typeinfodecl: string;
        let typeinfodef: string;
        if(isRef) {
            [typeinfodecl, typeinfodef] = this.emitEntityTypeInfoWAllocInfo(tdecl);
        }
        else {
            typeinfodecl = this.emitEntityTypeInfoDecl(tdecl);
            typeinfodef = "//No allocator needed for value type";
        }

        const bsqparsedecl = `std::optional<${ctrepr}> BSQ_parse${ctname}();`;
        
        const bsqemitdecl = `void BSQ_emit${ctname}(${ctrepr} vv);`;
        const bsqemitdef = `void BSQ_emit${ctname}(${ctrepr} vv) {\n` +
        `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.emitLiteralContent("${tdecl.tkey}"); \n` +
        `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.writeImmediate("{ "); \n` +
        `${tdecl.saturatedBFieldInfo.map((bf, ii) => {
            const fname = TransformCPPNameManager.convertIdentifier(bf.fname);
            const fttname = TransformCPPNameManager.convertTypeKey(bf.ftype.tkeystr);
            return `    BSQ_emit${fttname}(vv${vvaccess}${fname});${ii !== tdecl.saturatedBFieldInfo.length - 1 ? ' ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.writeImmediate(", ");' : ""}`;
        }).join("\n")}\n` +
        `    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqemitter.writeImmediate(" }"); \n` +
        `}`;

        const bfparses = tdecl.saturatedBFieldInfo.map((bf, ii) => {
            const fname = TransformCPPNameManager.convertIdentifier(bf.fname);
            const fttname = TransformCPPNameManager.convertTypeKey(bf.ftype.tkeystr);
            return `    auto v_${fname} = BSQ_parse${fttname}(); if(!v_${fname}.has_value()) { return std::nullopt; } ${ii !== tdecl.saturatedBFieldInfo.length - 1 ? "if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol(',')) { return std::nullopt; };" : ""}`;
        });

        const consargs = tdecl.saturatedBFieldInfo.map((bf) => {
            const fname = TransformCPPNameManager.convertIdentifier(bf.fname);
            return `v_${fname}.value()`;
        });

        if(vfuncinfo.length === 0 && valfuncinfo.length === 0) {
            const bsqparsedef = `std::optional<${ctrepr}> BSQ_parse${ctname}() {\n` +
            `    if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeType("${tdecl.tkey}")) { return std::nullopt; };\n` +
            `    if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol('{')) { return std::nullopt; };\n` +
            `${bfparses.join("\n")}\n` +
            `    if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol('}')) { return std::nullopt; };\n` +
            `    return std::make_optional<${ctrepr}>(${vvcons[0]} ${consargs.join(", ")} ${vvcons[1]});\n` +
            '}';

            return [
                [tclass, typeinfodecl, bsqparsedecl, bsqemitdecl].join("\n"), 
                [typeinfodef, bsqparsedef, bsqemitdef].join("\n")
            ];
        }
        else {
            const ivdecls = [...vfuncinfo.map((vf) => vf[0]), ...valfuncinfo.map((vf) => vf[0])].join("\n");
            const ivdefs = [...vfuncinfo.map((vf) => vf[1]), ...valfuncinfo.map((vf) => vf[1])].join("\n");

            const allchks = [
                ...tdecl.allInvariants.map((inv) => {
                    const cttdecl = this.irasm.alltypes.get(inv.containingtype.tkeystr) as IRAbstractNominalTypeDecl;
                    const aargs = cttdecl.saturatedBFieldInfo.map((bf) => {
                        const aidx = tdecl.saturatedBFieldInfo.findIndex((fb) => fb.fkey === bf.fkey);
                        assert(aidx !== -1);

                        return consargs[aidx];
                    });

                    const ifname = TransformCPPNameManager.generateNameForInvariantFunction(inv.containingtype.tkeystr, inv.ii);
                    return `if(!((bool)${ifname}(${aargs.join(", ")}))) { return std::nullopt; };`;
                }),
                ...tdecl.allValidates.map((val) => {
                    const cttdecl = this.irasm.alltypes.get(val.containingtype.tkeystr) as IRAbstractNominalTypeDecl;
                    const aargs = cttdecl.saturatedBFieldInfo.map((bf) => {
                        const aidx = tdecl.saturatedBFieldInfo.findIndex((fb) => fb.fkey === bf.fkey);
                        assert(aidx !== -1);

                        return consargs[aidx];
                    });

                    const vfname = TransformCPPNameManager.generateNameForValidateFunction(val.containingtype.tkeystr, val.ii);
                    return `if(!((bool)${vfname}(${aargs.join(", ")}))) { return std::nullopt; };`;
                })
            ].join("\n    ");

            const bsqparsedef = `std::optional<${ctrepr}> BSQ_parse${ctname}() {\n` +
            `    if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeType("${tdecl.tkey}")) { return std::nullopt; };\n` +
            `    if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol('{')) { return std::nullopt; };\n` +
            `${bfparses.join("\n")}\n` +
            `    if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.ensureAndConsumeSymbol('}')) { return std::nullopt; };\n` +
            `    ${allchks}\n\n` +
            `    return std::make_optional<${ctrepr}>(${vvcons[0]} ${consargs.join(", ")} ${vvcons[1]});\n` +
            '}';

            return [
                [tclass, typeinfodecl, ivdecls, bsqparsedecl, bsqemitdecl].join("\n"), 
                [typeinfodef, ivdefs, bsqparsedef, bsqemitdef].join("\n")
            ];
        }
    }

    private emitStdValueEntityTypeInfo(tdecl: IREntityTypeDecl, tlinfo: TypeInfo): [string, string] {
        return this.emitStdCommonEntityTypeInfo(tdecl, tlinfo, false);
    }

    private emitStdRefEntityTypeInfo(tdecl: IREntityTypeDecl, tlinfo: TypeInfo): [string, string] {
        return this.emitStdCommonEntityTypeInfo(tdecl, tlinfo, true);
    }

    private emitStdEntityTypeInfo(tdecl: IREntityTypeDecl): [string, string] {
        const tlayout = this.typeInfoManager.getTypeInfo(tdecl.tkey);

        if(tlayout.tag === LayoutTag.Value) {
            return this.emitStdValueEntityTypeInfo(tdecl, tlayout);
        }
        else {
            return this.emitStdRefEntityTypeInfo(tdecl, tlayout);
        }
    }

    private emitConceptTypeInfo(tdecl: IRConceptTypeDecl): [string, string] {
        const ctname = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
        const uctname = TransformCPPNameManager.generateNameForUnionType(tdecl.tkey);
        
        const uoptions = this.irasm.concretesubtypes.get(tdecl.tkey) as IRTypeSignature[];
        const uopts = uoptions.map((opt) => {
            const ftype = this.typeInfoManager.emitTypeAsMemberField(opt.tkeystr);
            const fname = TransformCPPNameManager.generateNameForUnionMember(opt.tkeystr);
            return `    ${ftype} ${fname};`;
        });
        const ucons = uoptions.map((opt) => {
            const argtype = this.typeInfoManager.emitTypeAsParameter(opt.tkeystr, false);
            const umember = TransformCPPNameManager.generateNameForUnionMember(opt.tkeystr);
            return `    constexpr ${uctname}(const ${argtype}& v) : ${umember}(v) { }`;
        });

        const declunion = `union ${ctname}${"ᐤ"}Union {\n` +
        `${uopts.join("\n")}\n` +
        `    constexpr ${uctname}() {};\n` +
        `    constexpr ${uctname}(const ${uctname}& other) = default;\n` +
        `${ucons.join("\n")}\n` +
        `};`;

        const ccons = uoptions.map((opt) => {
            const argtype = this.typeInfoManager.emitTypeAsParameter(opt.tkeystr, false);
            const typeinfo = TransformCPPNameManager.generateTypeInfoNameForTypeKey(opt.tkeystr);
            return `    constexpr ${ctname}(const ${argtype}& v) : uval(${RUNTIME_NAMESPACE}::BoxedUnion<${uctname}>(&${typeinfo}, ${uctname}(v))) { }`;
        });

        const declconcept = `class ${ctname} {\n` +
        `public:\n` +
        `    ${RUNTIME_NAMESPACE}::BoxedUnion<${uctname}> uval;\n\n` +
        `    constexpr ${ctname}() = default;\n` +
        `    constexpr ${ctname}(const ${ctname}& other) = default;\n\n` +
        '    template<typename T, size_t idx> inline T accessfield() const { return this->uval.accessfield<T, idx>(); }\n' +
        '    //TODO: implement access field truly virtual -- with dynamic field offset lookup \n\n' +
        `${ccons.join("\n")}\n` +
        `};`;
        const decltypeinfo = this.emitConceptTypeInfoDecl(tdecl);
        const declbsqparse = `std::optional<${ctname}> BSQ_parse${ctname}();`;
        const declbsqemit = `void BSQ_emit${ctname}(const ${ctname}& vv);`;

        const parseops = uoptions.map((opt, ii) => {
            const fttname = TransformCPPNameManager.convertTypeKey(opt.tkeystr);
            const ftvar = this.typeInfoManager.emitTypeAsStd(opt.tkeystr);
            const testop = `ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.testType("${opt.tkeystr}")`;
            const baseop = `{ std::optional<${ftvar}> vv = BSQ_parse${fttname}(); if(!vv.has_value()) { return std::nullopt; } else { return ${ctname}(vv.value()); } }`;
            return `    ${ii !== 0 ? "else " : ""}if(${testop}) ${baseop}`;
        });

        const defbsqparse = `std::optional<${ctname}> BSQ_parse${ctname}() {\n` +
        parseops.join("\n") +
        `\n    else { return std::nullopt; }\n` +
        `}`;
        
        const emitops = uoptions.map((opt) => {
            const optypeinfo = this.typeInfoManager.getTypeInfo(opt.tkeystr);
            const fttname = TransformCPPNameManager.convertTypeKey(opt.tkeystr);
            const umember = TransformCPPNameManager.generateNameForUnionMember(opt.tkeystr);
            return `    case ${optypeinfo.bsqtypeid}: BSQ_emit${fttname}(vv.uval.data.${umember}); break;`;
        });

        const defbsqemit = `void BSQ_emit${ctname}(const ${ctname}& vv) {\n` +
        `    switch(vv.uval.typeinfo->bsqtypeid) {\n` +
        `${emitops.join("\n")}\n` +
        `    }\n` +
        `}`;
        
        return [
            [declunion, declconcept, decltypeinfo, declbsqparse, declbsqemit].join("\n"),
            [defbsqparse, defbsqemit].join("\n")
        ];
    }

    private emitFormatTypeInfo(tdecl: IRFormatTypeSignature): [string, string] {
        //just a using decl for now -- eventually we will need to support parsing and emitting of format types as well
        const ctname = TransformCPPNameManager.convertTypeKey(tdecl.tkeystr);

        let declusing = "";
        if(tdecl instanceof IRFormatCStringTypeSignature) {
            declusing = `using ${ctname} = ${RUNTIME_NAMESPACE}::XFCString;`;
        }
        else if(tdecl instanceof IRFormatStringTypeSignature) {
            declusing = `using ${ctname} = ${RUNTIME_NAMESPACE}::XFString;`;
        }
        else {
            assert(false, "CPPEmitter: unknown format type signature emission for key " + tdecl.tkeystr);
        }
        
        return [declusing, "//TODO: need to implement format type info emission"];
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

        const [redecls, redefs] = this.emitRegexInfos(this.irasm.cregexps, this.irasm.uregexps);
        
        const enumdd = this.irasm.enums.map((eden) => this.emitEnumTypeDeclInfo(eden));

        const gtddd = this.irasm.typedecls.map((tgtd) =>  this.emitGeneralTypeDeclInfo(tgtd, undefined));
        const cstringdd = this.irasm.cstringoftypedecls.map((tcstr) => this.emitCStringTypeDeclInfo(tcstr));
        const stringdd = this.irasm.stringoftypedecls.map((tstr) => this.emitStringTypeDeclInfo(tstr));

        const fcstringdd = this.emitFCStringDefInfo(this.irasm.formatcstrings);
        const fstringdd = this.emitFStringDefInfo(this.irasm.formatstrings);

        const decltdd = this.irasm.typedeporder
        .filter((ttd) => {
            if(!(ttd instanceof IRNominalTypeSignature)) {
                return true;
            }
            else {
                const ctd = this.irasm.alltypes.get((ttd as IRNominalTypeSignature).tkeystr) as IRAbstractNominalTypeDecl;
                return !((ctd instanceof IRPrimitiveEntityTypeDecl) || (ctd instanceof IREnumTypeDecl) || (ctd instanceof IRTypedeclTypeDecl) || (ctd instanceof IRTypedeclCStringDecl) || (ctd instanceof IRTypedeclStringDecl));
            }
        })
        .map((ttd) => {
            if(!(ttd instanceof IRNominalTypeSignature)) {
                assert(!(ttd instanceof IRVoidTypeSignature), "Don't think we should ever be doing this...");

                if(ttd instanceof IREListTypeSignature) {
                    assert(false, `CPPEmitter: need to implement EList type signature emission for key ${ttd.tkeystr}`);
                }
                else if(ttd instanceof IRDashResultTypeSignature) {
                    assert(false, `CPPEmitter: need to implement DashResult type signature emission for key ${ttd.tkeystr}`);
                }
                else if(ttd instanceof IRFormatTypeSignature) {
                    return this.emitFormatTypeInfo(ttd);
                }
                else if(ttd instanceof IRLambdaParameterPackTypeSignature) {
                    assert(false, `CPPEmitter: need to implement lambda parameter pack type signature emission for key ${ttd.tkeystr}`);
                }
                else {
                    assert(false, "CPPEmitter: unknown typedeporder (TYPESIG) type decl emission -- " + ttd.tkeystr);
                }    
            }
            else {
                const ctd = this.irasm.alltypes.get(ttd.tkeystr) as IRAbstractNominalTypeDecl;
                if (ctd instanceof IRConstructableTypeDecl) {
                    if (ctd instanceof IRSomeTypeDecl) {
                        return this.emitSomeTypeInfo(ctd);
                    }
                    else if (ctd instanceof IROkTypeDecl) {
                        return this.emitOkTypeInfo(ctd);
                    }
                    else if (ctd instanceof IRFailTypeDecl) {
                        return this.emitFailTypeInfo(ctd);
                    }
                    else if (ctd instanceof IRMapEntryTypeDecl) {
                        assert(false, "CPPEmitter: need to implement map entry type decl emission");
                    }
                    else {
                        assert(false, "CPPEmitter: unknown constructable type decl emission");
                    }
                }
                else if(ctd instanceof IRAbstractCollectionTypeDecl) {
                    if(ctd instanceof IRListTypeDecl) {
                        return this.emitListTypeInfo(ctd);
                    }
                    else if(ctd instanceof IRMapTypeDecl) {
                        assert(false, "CPPEmitter: need to implement map type decl emission");
                    }
                    else {
                        assert(false, "CPPEmitter: unknown abstract collection type decl emission");
                    }
                }
                else if(ctd instanceof IREntityTypeDecl) {
                    return this.emitStdEntityTypeInfo(ctd);
                }
                else if (ctd instanceof IRInternalConceptTypeDecl) {
                    if (ctd instanceof IROptionTypeDecl) {
                        return this.emitOptionTypeInfo(ctd);
                    }
                    else if (ctd instanceof IRResultTypeDecl) {
                        return this.emitResultTypeInfo(ctd);
                    }
                    else {
                        assert(false, "CPPEmitter: unknown primitive concept type decl emission");
                    }
                }
                else if(ctd instanceof IRConceptTypeDecl) {
                    return this.emitConceptTypeInfo(ctd);
                }
                else {
                    assert(false, "CPPEmitter: unknown typedeporder (NOMINAL) type decl emission -- " + ttd.tkeystr);
                }
            }
        });

        return [
            [pdecls, redecls, ...enumdd.map((tt) => tt[0]), ...gtddd.map((tt) => tt[0]), ...cstringdd.map((tt) => tt[0]), ...stringdd.map((tt) => tt[0]), ...decltdd.map((tt) => tt[0])].join("\n\n"),
            [pdefs, redefs, ...enumdd.map((tt) => tt[1]), ...gtddd.map((tt) => tt[1]), ...cstringdd.map((tt) => tt[1]), ...stringdd.map((tt) => tt[1]), fcstringdd, fstringdd, ...decltdd.map((tt) => tt[1])].join("\n\n")
        ];
    }

    private emitAllInvokeInfo(): [string, string] {
        assert(this.irasm.predicates.length === 0, "CPPEmitter: need to implement predicate decl emission");
        const idecls = this.irasm.invokes.map((invk) => this.emitIRInvokeDeclInfo(invk));
        assert(this.irasm.taskactions.length === 0, "CPPEmitter: need to implement ADT decl emission");

        const constdecls = this.irasm.constants.map((c) => this.emitConstantDeclInfo(c));

        return [
            [...idecls.map((idecl) => idecl[0]), ...constdecls.map((cdecl) => cdecl[0])].join("\n\n"),
            [...idecls.map((idecl) => idecl[1]), ...constdecls.map((cdecl) => cdecl[1])].join("\n\n")
        ];
    }

    private generateHeaderSetup(): string {
        return [
            '#include "./runcpp/common.h"',
            '#include "./runcpp/core/bsqtype.h"',
            '#include "./runcpp/core/boxed.h"',
            '#include "./runcpp/core/bools.h"',
            '#include "./runcpp/core/integrals.h"',
            '#include "./runcpp/core/strings.h"',
            '#include "./runcpp/core/list_t.h"',
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

    ////
    //Emit command line main support
    private emitParseArgsMain(idecl: IRInvokeDecl): string {
        if(idecl.params.length === 0) {
            return '    //No args';
        }
        else {
            const initforparse = 
            '    auto iobb = ᐸRuntimeᐳ::g_alloc_info.io_buffer_alloc();\n' + 
            '    size_t ibytes = std::strlen(argv[1]);\n' +
            '    std::copy(argv[1], argv[1] + ibytes, iobb);\n\n' +
            '    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.initialize({iobb}, ibytes);\n' +
            '    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.setSloppyStringParsing(true);\n';

            const pargs = idecl.params.map((p) => {
                const vname = TransformCPPNameManager.convertIdentifier(p.name);
                const parsekey = TransformCPPNameManager.convertTypeKey(p.type.tkeystr);

                return `    auto ${vname} = BSQ_parse${parsekey}(); if(!${vname}.has_value()) { printf("Error parsing input\\n"); exit(1); }\n`;
            }).join("\n") + "\n";

            const finalizeparse = 
            '    if(!ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.allInputConsumed()) { printf("Error parsing input -- invaliad data in tail of input\\n"); exit(1); }\n' +
            '    ᐸRuntimeᐳ::tl_bosque_info.current_task->bsqparser.release();\n';

            return [initforparse, pargs, finalizeparse].join("\n");
        }
    }

    private emitMMain(idecl: IRInvokeDecl): string {
        const parse = this.emitParseArgsMain(idecl);

        const invokeargs = idecl.params.map((p) => TransformCPPNameManager.convertIdentifier(p.name) + ".value()").join(", ");
        const invoke = '    if (setjmp(ᐸRuntimeᐳ::tl_bosque_info.current_task->error_handler) > 0) {\n' +
            '        auto perr = ᐸRuntimeᐳ::tl_bosque_info.current_task->pending_error.value();\n' +
            '        auto pfile = std::string(perr.file);\n' +
            '        auto pbfile = std::string(pfile.cbegin() + pfile.find_last_of("/") + 1, pfile.cend());\n' +
            '        printf("Error on line %d in file %s\\n", perr.line, pbfile.c_str());\n' +
            '        if(perr.message != nullptr) { printf("  with message: %s\\n", perr.message); }\n' +
            '        exit(1);\n' +
            '    }\n\n' +
            `    auto result = ${TransformCPPNameManager.convertInvokeKey(idecl.ikey)}(${invokeargs});\n`;

        const print = '    size_t obytes = 0;\n' +
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

        return `void mmain(int argc, char** argv)\n` +
        `{\n` +
        parse + "\n" +
        invoke + "\n" +
        print + "\n" +
        `}`;
    }

    private emitCommandLineMain(ikey: string): string {
        const idecl = this.irasm.invokes.find((v) => v.ikey === ikey) as IRInvokeDecl;

        const mmain = this.emitMMain(idecl);

        const sallocs = [
            ...(this.irasm.primitives.map((pdcl) => this.typeInfoManager.generateAllocatorNameForTypeKeySpecialMapEntry(pdcl.tkey)).filter((aa) => aa !== undefined) as string[][]),
            ...(this.irasm.collections.map((cdcl) => this.typeInfoManager.generateAllocatorNameForTypeKeySpecialMapEntry(cdcl.tkey)).filter((aa) => aa !== undefined) as string[][]),
            ...(this.irasm.eventlists.map((ccdl) => this.typeInfoManager.generateAllocatorNameForTypeKeySpecialMapEntry(ccdl.tkey)).filter((aa) => aa !== undefined) as string[][]),
        ].flat();

        const allocs = [
            ...(this.irasm.entities.map((edcl) => this.typeInfoManager.generateAllocatorNameForTypeKeyGeneralMapEntry(edcl.tkey)).filter((aa) => aa !== undefined) as string[]),
            ...(this.irasm.datamembers.map((cdcl) => this.typeInfoManager.generateAllocatorNameForTypeKeyGeneralMapEntry(cdcl.tkey)).filter((aa) => aa !== undefined) as string[])
        ];

        const initializegc = '{\n' +
        '        //always thread safe on this initialization phase since we have not started any other threads yet\n' +
        '        register void** rbp asm("rbp");\n' +
        `        ᐸRuntimeᐳ::tl_alloc_info.initialize(rbp, ᐸRuntimeᐳ::collect, {${[...sallocs, ...allocs].join(', ')}});\n` +
        '    }\n';

        const notes = "//TODO ---- need to dispatch on things and handle useage + agents.md";

        return mmain + "\n\n" +
               'int main(int argc, char** argv) {\n' +
               '    ᐸRuntimeᐳ::TaskInfoRepr<StdEnvUnion> maintask;\n' +
               '    ᐸRuntimeᐳ::tl_bosque_info.current_task = &maintask;\n\n' +
               `    ${initializegc}\n` +
               `    ${notes}\n` +
               `    mmain(argc, argv);\n` +
               '\n' +
               `    ᐸRuntimeᐳ::tl_alloc_info.cleanup();\n` +
               `    return 0;\n` +
               '}\n';
    }

    emitInvokeForKey(ikey: string): string {
        const invk = this.irasm.invokes.find((v) => v.ikey === ikey);

        return this.emitIRInvokeDeclInfo(invk as IRInvokeDecl)[1];
    }

    public emitForCommandLine(ikey: string): [string, string] {
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

    static createEmitter(irasm: IRAssembly): CPPEmitter {
        const tmgr = TypeInfoManager.generateTypeInfos(irasm);
        const ee = new CPPEmitter(irasm, tmgr);

        return ee;
    }
}

export {
    CPPEmitter
};
