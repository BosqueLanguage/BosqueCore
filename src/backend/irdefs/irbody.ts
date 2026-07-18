import { IRSourceInfo } from "./irsupport.js";
import { IREListTypeSignature, IRLambdaParameterPackTypeSignature, IRNominalTypeSignature, IRTypeSignature } from "./irtype.js";

import { BAPILexer, BAPITokenKind } from "./irlexer.js";

import assert from "node:assert";

enum IRExpressionTag {
    IRLiteralNoneExpression = "IRLiteralNoneExpression",
    IRLiteralBoolExpression = "IRLiteralBoolExpression",
    
    IRLiteralNatExpression = "IRLiteralNatExpression",
    IRLiteralIntExpression = "IRLiteralIntExpression",
    IRLiteralChkNatExpression = "IRLiteralChkNatExpression",
    IRLiteralChkIntExpression = "IRLiteralChkIntExpression",
    IRLiteralRationalExpression = "IRLiteralRationalExpression",
    IRLiteralFloatExpression = "IRLiteralFloatExpression",
    IRLiteralDecimalExpression = "IRLiteralDecimalExpression",
    IRLiteralDecimalDegreeExpression = "IRLiteralDecimalDegreeExpression",
    IRLiteralLatLongCoordinateExpression = "IRLiteralLatLongCoordinateExpression",
    IRLiteralComplexExpression = "IRLiteralComplexExpression",

    IRLiteralByteBufferExpression = "IRLiteralByteBufferExpression",
    IRLiteralUUIDv4Expression = "IRLiteralUUIDv4Expression",
    IRLiteralUUIDv7Expression = "IRLiteralUUIDv7Expression",
    IRLiteralSHAContentHashExpression = "IRLiteralSHAContentHashExpression",

    IRLiteralTZDateTimeExpression = "IRLiteralTZDateTimeExpression",
    IRLiteralTAITimeExpression = "IRLiteralTAITimeExpression",
    IRLiteralPlainDateExpression = "IRLiteralPlainDateExpression",
    IRLiteralPlainTimeExpression = "IRLiteralPlainTimeExpression",
    IRLiteralLogicalTimeExpression = "IRLiteralLogicalTimeExpression",
    IRLiteralISOTimeStampExpression = "IRLiteralISOTimeStampExpression",
    IRLiteralDeltaDateTimeExpression = "IRLiteralDeltaDateTimeExpression",
    IRLiteralDeltaISOTimeStampExpression = "IRLiteralDeltaISOTimeStampExpression",
    IRLiteralDeltaSecondsExpression = "IRLiteralDeltaSecondsExpression",
    IRLiteralDeltaLogicalTimeExpression = "IRLiteralDeltaLogicalTimeExpression",

    IRLiteralUnicodeRegexExpression = "IRLiteralUnicodeRegexExpression",
    IRLiteralCRegexExpression = "IRLiteralCRegexExpression",

    IRLiteralByteExpression = "IRLiteralByteExpression",
    IRLiteralCCharExpression = "IRLiteralCCharExpression",
    IRLiteralUnicodeCharExpression = "IRLiteralUnicodeCharExpression",

    IRLiteralCStringExpression = "IRLiteralCStringExpression",
    IRLiteralStringExpression = "IRLiteralStringExpression",

    IRLiteralFormatStringExpression = "IRLiteralFormatStringExpression",
    IRLiteralFormatCStringExpression = "IRLiteralFormatCStringExpression",

    //TODO: path literal options here

    //TODO: path literal -format- options here

    IRLiteralTypedExpression = "IRLiteralTypedExpression",
    IRLiteralTypedStringExpression = "IRLiteralTypedStringExpression",
    IRLiteralTypedCStringExpression = "IRLiteralTypedCStringExpression",

    //TODO: path typed literal and -format- options here

    IRAccessEnvHasExpression = "IRAccessEnvHasExpression",
    IRAccessEnvGetExpression = "IRAccessEnvGetExpression",
    IRAccessEnvTryGetExpression = "IRAccessEnvTryGetExpression",

    IRTaskAccessIDExpression = "IRTaskAccessIDExpression",
    IRTaskAccessParentIDExpression = "IRTaskAccessParentIDExpression",

    IRAccessConstantExpression = "IRAccessConstantExpression",
    IRAccessEnumExpression = "IRAccessEnumExpression",

    IRAccessParameterVariableExpression = "IRAccessParameterVariableExpression",
    IRAccessLocalVariableExpression = "IRAccessLocalVariableExpression",
    IRAccessCapturedVariableExpression = "IRAccessCapturedVariableExpression",
    IRAccessTempVariableExpression = "IRAccessTempVariableExpression",

    IRAccessTypeDeclValueExpression = "IRAccessTypeDeclValueExpression",
    IRConstructSafeTypeDeclExpression = "IRConstructSafeTypeDeclExpression",
    
    IRConstructorSomeTypeExpression = "IRConstructorSomeTypeExpression",
    IRConstructorOkTypeExpression = "IRConstructorOkTypeExpression",
    IRConstructorFailTypeExpression = "IRConstructorFailTypeExpression",
    IRConstructorMapEntryTypeExpression = "IRConstructorMapEntryTypeExpression",

    IRConstructorStandardEntityExpression = "IRConstructorStandardEntityExpression",
    IRConstructorLambdaExpression = "IRConstructorLambdaExpression",
    IRConstructorEListExpression = "IRConstructorEListExpression",

    IRConstructorListEmptyExpression = "IRConstructorListEmptyExpression",
    IRConstructorListSingletonsExpression = "IRConstructorListSingletonsExpression",

    IRConstructorMapEmptyExpression = "IRConstructorMapEmptyExpression",
    IRConstructorMapSingletonsExpression = "IRConstructorMapSingletonsExpression",

    IRAccessFieldSpecialExpression = "IRAccessFieldSpecialExpression",
    IRAccessFieldDirectExpression = "IRAccessFieldDirectExpression",
    IRAccessFieldVirtualExpression = "IRAccessFieldVirtualExpression",

    IRAccessEListIndexExpression = "IRAccessEListIndexExpression",

    IRInvokeSimpleExpression = "IRInvokeSimpleExpression",
    IRInvokeSimpleWithImplicitsExpression = "IRInvokeSimpleWithImplicitsExpression",
    IRInvokeVirtualSimpleExpression = "IRInvokeVirtualSimpleExpression",
    IRInvokeVirtualWithImplicitsExpression = "IRInvokeVirtualWithImplicitsExpression",

    IRInterpolateFormatCStringExpression = "IRInterpolateFormatCStringExpression",
    IRInterpolateFormatStringExpression = "IRInterpolateFormatStringExpression",

    IRPrefixNotOpExpression = "IRPrefixNotOpExpression",
    IRPrefixNegateOpExpression = "IRPrefixNegateOrPlusOpExpression",
    IRPrefixPlusOpExpression = "IRPrefixPlusOpExpression",

    IRBinAddExpression = "IRBinAddExpression",
    IRBinSubExpression = "IRBinSubExpression",
    IRBinMultExpression = "IRBinMultExpression",
    IRBinDivExpression = "IRBinDivExpression",

    IRNumericEqExpression = "IRNumericEqExpression",
    IRNumericNeqExpression = "IRNumericNeqExpression",
    IRNumericLessExpression = "IRNumericLessExpression",
    IRNumericLessEqExpression = "IRNumericLessEqExpression",
    IRNumericGreaterExpression = "IRNumericGreaterExpression",
    IRNumericGreaterEqExpression = "IRNumericGreaterEqExpression",

    IRIsNoneOptionExpression = "IRIsNoneOptionExpression",
    IRIsNotNoneOptionExpression = "IRIsNotNoneOptionExpression",
    IRIsOptionEqValueExpression = "IRIsOptionEqValueExpression",
    IRIsOptionNeqValueExpression = "IRIsOptionNeqValueExpression",
    IRIsSomeEqValueExpression = "IRIsSomeEqValueExpression",
    IRIsSomeNeqValueExpression = "IRIsSomeNeqValueExpression",

    IRBinKeyEqDirectExpression = "IRBinKeyEqDirectExpression",
    IRBinKeyNeqDirectExpression = "IRBinKeyNeqDirectExpression",
    IRBinKeyLessDirectExpression = "IRBinKeyLessDirectExpression",

    IRLogicAndExpression = "IRLogicAndExpression",
    IRLogicOrExpression = "IRLogicOrExpression",

    IRLogicSimpleConditionalExpression = "IRLogicSimpleConditionalExpression",

    IRLiteralOptionOfNoneExpression = "IRLiteralOptionOfNoneExpression",
    IRConstructOptionFromSomeExpression = "IRConstructOptionFromSomeExpression",
    IRExtractSomeFromOptionExpression = "IRExtractSomeFromOptionExpression",
    IRExtractSomeValueFromOptionExpression = "IRExtractSomeValueFromOptionExpression",

    IRConstructResultFromOkExpression = "IRConstructResultFromOkExpression",
    IRConstructResultFromFailExpression = "IRConstructResultFromFailExpression",
    IRExtractOkFromResultExpression = "IRExtractOkFromResultExpression",
    IRExtractOkValueFromResultExpression = "IRExtractOkValueFromResultExpression",
    IRExtractFailFromResultExpression = "IRExtractFailFromResultExpression",
    IRExtractFailValueFromResultExpression = "IRExtractFailValueFromResultExpression",

    IRIsConceptRepresentationOfTypeExpression = "IRIsConceptRepresentationOfTypeExpression",
    IRIsNotConceptRepresentationOfTypeExpression = "IRIsNotConceptRepresentationOfTypeExpression",
    IRIsConceptRepresentationSubtypeOfTypeExpression = "IRIsConceptRepresentationSubtypeOfTypeExpression",
    IRIsNotConceptRepresentationSubtypeOfTypeExpression = "IRIsNotConceptRepresentationSubtypeOfTypeExpression",

    IRStaticIsTypeSubtypeOfExpression = "IRStaticIsTypeSubtypeOfExpression",

    IRBoxEntityToConceptRepresentationExpression = "IRBoxEntityToConceptRepresentationExpression",
    IRUnboxEntityFromConceptRepresentationExpression = "IRUnboxEntityFromConceptRepresentationExpression",
    IRConvertConceptRepresentationExpression = "IRConvertConceptRepresentationExpression"
}

abstract class IRExpression {
    readonly tag: IRExpressionTag;

    constructor(tag: IRExpressionTag) {
        this.tag = tag;
    }

    abstract isSimpleExpression(): boolean;

    abstract toBAPI(): string;

    static parseBAPI(lexer: BAPILexer): IRExpression {
        xxxx;
    }
}

/* This class represents expressions that are invocations (function/method/virtual calls) */
abstract class IRInvokeExpression extends IRExpression {
    readonly ikey: string;
    readonly args: IRSimpleExpression[];

    constructor(tag: IRExpressionTag, ikey: string, args: IRSimpleExpression[]) {
        super(tag);
        this.ikey = ikey;
        this.args = args;
    }

    override isSimpleExpression(): boolean {
        return false;
    }

    toBAPI_IRInvokeExpression(): string {
        assert(false, "IRInvokeExpression.toBAPI__IRInvokeExpression not implemented");
    }

    static parseBAPI_IRInvokeExpression(lexer: BAPILexer): {ikey: string, args: IRSimpleExpression[]} {
        assert(false, "IRInvokeExpression.parseBAPI_IRInvokeExpression not implemented");
    }

    static parseBAPIAsIRInvokeExpression(lexer: BAPILexer): IRInvokeExpression {
        return IRExpression.parseBAPI(lexer) as IRInvokeExpression;
    }
}

/* This class represents expressions that have a single return value */
abstract class IRInvokeDirectExpression extends IRInvokeExpression {
    constructor(tag: IRExpressionTag, ikey: string, args: IRSimpleExpression[]) {
        super(tag, ikey, args);
    }
}

/* This class represents expressions that have implicit return values */
abstract class IRInvokeImplicitsExpression extends IRInvokeExpression {
    readonly implicitidx: number;
    readonly ivar: string; //the implicit variable to assign the returned ref/out/out?/inout parameter
    readonly ivartype: IRTypeSignature;
    readonly passkind : "ref" | "out" | "out?" | "inout";

    constructor(tag: IRExpressionTag, ikey: string, args: IRSimpleExpression[], implicitidx: number, ivar: string, ivartype: IRTypeSignature, passkind: "ref" | "out" | "out?" | "inout") {
        super(tag, ikey, args);
        this.implicitidx = implicitidx;
        this.ivar = ivar;
        this.ivartype = ivartype;
        this.passkind = passkind;
    }
}

/* This class represents expressions that construct composite (maybe allocating) values -- can only OOM (otherwise semantically safe) but we want to keep them ordered strongly */
abstract class IRConstructExpression extends IRExpression {
    readonly constype: IRNominalTypeSignature;

    constructor(tag: IRExpressionTag, constype: IRNominalTypeSignature) {
        super(tag);
        this.constype = constype;
    }

    override isSimpleExpression(): boolean {
        return true;
    }

    toBAPI_IRConstructExpression(): string {
        assert(false, "IRConstructExpression.toBAPI__IRConstructExpression not implemented");
    }

    static parseBAPI_IRConstructExpression(lexer: BAPILexer): {constype: IRNominalTypeSignature} {
        assert(false, "IRConstructExpression.parseBAPI_IRConstructExpression not implemented");
    }

    static parseBAPIAsIRConstructExpression(lexer: BAPILexer): IRConstructExpression {
        return IRExpression.parseBAPI(lexer) as IRConstructExpression;
    }
}

/* This class represents expressions that are simple and side-effect free (i.e., immediate expressions plus simple operations that we can put into expression trees) */
abstract class IRSimpleExpression extends IRExpression {
    constructor(tag: IRExpressionTag) {
        super(tag);
    }

    override isSimpleExpression(): boolean {
        return true;
    }

    static parseBAPIAsIRSimpleExpression(lexer: BAPILexer): IRSimpleExpression {
        return IRExpression.parseBAPI(lexer) as IRSimpleExpression;
    }
}

/* This class represents expressions that are guaranteed to be immediate values (i.e., vars, literals, constants) */
abstract class IRImmediateExpression extends IRSimpleExpression {
    constructor(tag: IRExpressionTag) {
        super(tag);
    }

    static parseBAPIAsIRImmediateExpression(lexer: BAPILexer): IRImmediateExpression {
        return IRExpression.parseBAPI(lexer) as IRImmediateExpression;
    }
}

/* This class represents expressions that are guaranteed to be immediate values (i.e., constants, typdecl literals) */
abstract class IRLiteralExpression extends IRImmediateExpression {
    constructor(tag: IRExpressionTag) {
        super(tag);
    }

    static parseBAPIAsIRLiteralExpression(lexer: BAPILexer): IRLiteralExpression {
        return IRExpression.parseBAPI(lexer) as IRLiteralExpression;
    }
}

/* This class represents expressions that access field values */
abstract class IRAccessFieldExpression extends IRSimpleExpression {
    readonly eexptype: IRNominalTypeSignature;
    readonly eexp: IRSimpleExpression;
    readonly intype: IRNominalTypeSignature;
    readonly fieldname: string;
    readonly fieldtype: IRTypeSignature;

    constructor(tag: IRExpressionTag, eexptype: IRNominalTypeSignature, eexp: IRSimpleExpression, intype: IRNominalTypeSignature, fieldname: string, fieldtype: IRTypeSignature) {
        super(tag);
        this.eexptype = eexptype;
        this.eexp = eexp;
        this.intype = intype;
        this.fieldname = fieldname;
        this.fieldtype = fieldtype;
    }

    toBAPI_IRAccessFieldExpression(): string {
        assert(false, "IRAccessFieldExpression.toBAPI__IRAccessFieldExpression not implemented");
    }

    static parseBAPI_IRAccessFieldExpression(lexer: BAPILexer): {eexptype: IRNominalTypeSignature, eexp: IRSimpleExpression, intype: IRNominalTypeSignature, fieldname: string, fieldtype: IRTypeSignature} {
        assert(false, "IRAccessFieldExpression.parseBAPI_IRAccessFieldExpression not implemented");
    }
}

enum IRStatementTag {
    IRNopStatement = "IRNopStatement",

    IRTempAssignExpressionStatement = "IRTempAssignExpressionStatement",
    IRTempAssignStdInvokeStatement = "IRTempAssignStdInvokeStatement",
    IRTempAssignRefInvokeStatement = "IRTempAssignRefInvokeStatement",
    IRTempAssignDirectConstructorStatement = "IRTempAssignDirectConstructorStatement",

    IRVariableDeclarationStatement = "IRVariableDeclarationStatement",

    IRVariableInitializationStatement = "IRVariableInitializationStatement",
    IRVariableInitializationDirectInvokeStatement = "IRVariableInitializationDirectInvokeStatement",
    IRVariableInitializationDirectInvokeWithImplicitStatement = "IRVariableInitializationDirectInvokeWithImplicitStatement",
    IRVariableInitializationDirectConstructorStatement = "IRVariableInitializationDirectConstructorStatement",
    IRVariableInitializationDirectConstructorWithBoxStatement = "IRVariableInitializationDirectConstructorWithBoxStatement",

    IRVariableAssignmentStatement = "IRVariableAssignmentStatement",
    IRVariableAssignmentDirectInvokeStatement = "IRVariableAssignmentDirectInvokeStatement",
    IRVariableAssignmentDirectInvokeWithImplicitStatement = "IRVariableAssignmentDirectInvokeWithImplicitStatement",
    IRVariableAssignmentDirectConstructorStatement = "IRVariableAssignmentDirectConstructorStatement",
    IRVariableAssignmentDirectConstructorWithBoxStatement = "IRVariableAssignmentDirectConstructorWithBoxStatement",

    IRUpdateLocalDirectStatement = "IRUpdateLocalDirectStatement",
    IRUpdateParamDirectStatement = "IRUpdateParamDirectStatement",

    IRReturnVoidSimpleStatement = "IRReturnVoidSimpleStatement",
    IRReturnValueSimpleStatement = "IRReturnValueSimpleStatement",
    IRReturnDirectInvokeStatement = "IRReturnDirectInvokeStatement",
    IRReturnDirectConstructStatement = "IRReturnDirectConstructStatement",
    IRReturnDirectConstructWithBoxStatement = "IRReturnDirectConstructWithBoxStatement",

    IRReturnVoidImplicitStatement = "IRReturnVoidImplicitStatement",
    IRReturnValueImplicitStatement = "IRReturnValueImplicitStatement",
    IRReturnDirectInvokeImplicitStatement = "IRReturnDirectInvokeImplicitStatement",
    IRReturnDirectInvokeImplicitPassThroughStatement = "IRReturnDirectInvokeImplicitPassThroughStatement",
    IRReturnDirectConstructImplicitStatement = "IRReturnDirectConstructImplicitStatement",
    IRReturnDirectConstructWithBoxImplicitStatement = "IRReturnDirectConstructWithBoxImplicitStatement",

    IRVoidInvokeStatement = "IRVoidInvokeStatement",

    IRChkLogicImpliesShortCircuitStatement = "IRChkLogicImpliesShortCircuitStatement",

    IRLogicConditionalStatement = "IRLogicConditionalStatement",

    IRSimpleIfStatement = "IRSimpleIfStatement",
    IRSimpleIfElseStatement = "IRSimpleIfElseStatement",

    IRMatchExactStatement = "IRMatchExactStatement",
    IRMatchGeneralStatement = "IRMatchGeneralStatement",

    IRBlockStatement = "IRBlockStatement",

    IRErrorAdditionBoundsCheckStatement = "IRErrorAdditionBoundsCheckStatement",
    IRErrorSubtractionBoundsCheckStatement = "IRErrorSubtractionBoundsCheckStatement",
    IRErrorMultiplicationBoundsCheckStatement = "IRErrorMultiplicationBoundsCheckStatement",
    IRErrorDivisionByZeroCheckStatement = "IRErrorDivisionByZeroCheckStatement",
    IRErrorTypeAssertionCheckStatement = "IRErrorTypeAssertionCheckStatement",

    IRErrorExhaustiveStatement = "IRErrorExhaustiveStatement",

    IRTypeDeclSizeRangeCheckCStringStatement = "IRTypeDeclSizeRangeCheckCStringStatement",
    IRTypeDeclSizeRangeCheckUnicodeStringStatement = "IRTypeDeclSizeRangeCheckUnicodeStringStatement",
    IRTypeDeclNumericRangeCheckStatement = "IRTypeDeclNumericRangeCheckStatement",
    IRTypeDeclFormatCheckCStringStatement = "IRTypeDeclFormatCheckCStringStatement",
    IRTypeDeclFormatCheckUnicodeStringStatement = "IRTypeDeclFormatCheckUnicodeStringStatement",

    IRTypeDeclInvariantCheckStatement = "IRTypeDeclInvariantCheckStatement",
    IREntityInvariantCheckStatement = "IREntityInvariantCheckStatement",
    IRPreconditionCheckStatement = "IRPreconditionCheckStatement",
    IRPostconditionCheckStatement = "IRPostconditionCheckStatement",

    IRAbortStatement = "IRAbortStatement",
    IRAssertStatement = "IRAssertStatement",
    IRAssumeStatement = "IRAssumeStatement",
    IRValidateStatement = "IRValidateStatement",
    IRDebugStatement = "IRDebugStatement"
}

abstract class IRStatement {
    readonly tag: IRStatementTag;

    constructor(tag: IRStatementTag) {
        this.tag = tag;
    }

    isTerminalStatement(): boolean { return false; }

    abstract isSimpleStatement(): boolean;

    abstract toBAPI(): string;

    static parseBAPI(lexer: BAPILexer): IRStatement {
        xxxx;
    }
}

/* This class represents statements that are atomic (line statements) and don't have control flow or sub blocks */
abstract class IRAtomicStatement extends IRStatement {
    constructor(tag: IRStatementTag) {
        super(tag);
    }

    static parseBAPIAsIRAtomicStatement(lexer: BAPILexer): IRAtomicStatement {
        return IRStatement.parseBAPI(lexer) as IRAtomicStatement;
    }
}

/* Represent temporary variable assignment statements */
abstract class IRTempAssignStatement extends IRAtomicStatement {
    readonly ttype: IRTypeSignature;
    readonly tname: string;

    constructor(tag: IRStatementTag, tname: string, ttype: IRTypeSignature) {
        super(tag);
        this.tname = tname;
        this.ttype = ttype;
    }

    override isSimpleStatement(): boolean { 
        return true; 
    }

    toBAPI_IRTempAssignStatement(): string {
        assert(false, "IRTempAssignStatement.toBAPI__IRTempAssignStatement not implemented");
    }

    static parseBAPI_IRTempAssignStatement(lexer: BAPILexer): {tname: string, ttype: IRTypeSignature} {
        assert(false, "IRTempAssignStatement.parseBAPI_IRTempAssignStatement not implemented");
    }

    static parseBAPIAsIRTempAssignStatement(lexer: BAPILexer): IRTempAssignStatement {
        return IRStatement.parseBAPI(lexer) as IRTempAssignStatement;
    }
}

/* Represent return statement that do not involve any ref/out/out?/inout parameters */
abstract class IRReturnSimpleStatement extends IRAtomicStatement {
    constructor(tag: IRStatementTag) {
        super(tag);
    }

    override isTerminalStatement(): boolean { 
        return true; 
    }

    override isSimpleStatement(): boolean { 
        return true;  
    }
}

/* Represent return statement that involve ref/out/out?/inout parameters and thus have an implicit variable to hold the returned value */
abstract class IRReturnWithImplicitStatement extends IRAtomicStatement {
    readonly implicitvar: string;

    constructor(tag: IRStatementTag, implicitvar: string) {
        super(tag);
        this.implicitvar = implicitvar;
    }

    override isTerminalStatement(): boolean { 
        return true; 
    }

    override isSimpleStatement(): boolean {
        return false;
    }
}

/* Explicit error condition checks -- all possible error conditions must be made explicit during flattening */
abstract class IRErrorCheckStatement extends IRAtomicStatement {
    readonly file: string;
    readonly sinfo: IRSourceInfo;

    readonly diagnosticTag: string | undefined;
    readonly checkID: number;

    static assumeCheckID: number = -11;

    constructor(tag: IRStatementTag, file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number) {
        super(tag);
        this.file = file;
        this.sinfo = sinfo;
        this.diagnosticTag = diagnosticTag;
        this.checkID = checkID;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    toBAPI_IRErrorCheckStatement(): string {
        assert(false, "IRErrorCheckStatement.toBAPI__IRErrorCheckStatement not implemented");
    }

    static parseBAPI_IRErrorCheckStatement(lexer: BAPILexer): {file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number} {
        assert(false, "IRErrorCheckStatement.parseBAPI_IRErrorCheckStatement not implemented");
    }
}

abstract class IRErrorBinArithCheckStatement extends IRErrorCheckStatement {
    readonly left: IRImmediateExpression;
    readonly right: IRImmediateExpression;

    readonly optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float";

    constructor(tag: IRStatementTag, file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, left: IRImmediateExpression, right: IRImmediateExpression, optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float") {
        super(tag, file, sinfo, diagnosticTag, checkID);
        this.left = left;
        this.right = right;
        this.optypechk = optypechk;
    }

    toBAPI_IRErrorBinArithCheckStatement(): string {
        assert(false, "IRErrorBinArithCheckStatement.toBAPI__IRErrorBinArithCheckStatement not implemented");
    }

    static parseBAPI_IRErrorBinArithCheckStatement(lexer: BAPILexer): {file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, left: IRImmediateExpression, right: IRImmediateExpression, optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float"} {
        assert(false, "IRErrorBinArithCheckStatement.parseBAPI_IRErrorBinArithCheckStatement not implemented");
    }
}

abstract class IRErrorTypedStringCheckStatement extends IRErrorCheckStatement {
    readonly strexp: IRImmediateExpression;
    
    constructor(tag: IRStatementTag, file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, strexp: IRImmediateExpression) {
        super(tag, file, sinfo, diagnosticTag, checkID);
        this.strexp = strexp;
    }

    toBAPI_IRErrorTypedStringCheckStatement(): string {
        assert(false, "IRErrorTypedStringCheckStatement.toBAPI__IRErrorTypedStringCheckStatement not implemented");
    }

    static parseBAPI_IRErrorTypedStringCheckStatement(lexer: BAPILexer): {file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, strexp: IRImmediateExpression} {
        assert(false, "IRErrorTypedStringCheckStatement.parseBAPI_IRErrorTypedStringCheckStatement not implemented");
    }
}

////////////////////////////////////////
//Our literal expressions are all very safe and will never fail to construct -- if there are possible issues the flattening phase should have emitted and explicit check

class IRLiteralNoneExpression extends IRLiteralExpression {
    constructor() {
        super(IRExpressionTag.IRLiteralNoneExpression);
    }

    override toBAPI(): string {
        xxxx;
        return `none`;
    }

    static parseBAPIAsIRLiteralNoneExpression(lexer: BAPILexer): IRLiteralNoneExpression {
        xxxx;
        lexer.ensureAndConsumeToken(BAPITokenKind.NoneLiteral);
        return new IRLiteralNoneExpression();
    }
}

class IRLiteralBoolExpression extends IRLiteralExpression {
    readonly value: boolean;

    constructor(value: boolean) {
        super(IRExpressionTag.IRLiteralBoolExpression);
        this.value = value;
    }

    override toBAPI(): string {
        xxxx;
        return this.value ? `true` : `false`;
    }

    static parseBAPIAsIRLiteralBoolExpression(lexer: BAPILexer): IRLiteralBoolExpression {
        xxxx;
        if (lexer.ensureAndConsumeToken(BAPITokenKind.TrueLiteral)) {
            return new IRLiteralBoolExpression(true);
        } else if (lexer.ensureAndConsumeToken(BAPITokenKind.FalseLiteral)) {
            return new IRLiteralBoolExpression(false);
        } else {
            throw new Error(`Expected 'true' or 'false' literal`);
        }
    }
}
    
abstract class IRLiteralIntegralNumberExpression extends IRLiteralExpression {
    readonly value: string;

    constructor(tag: IRExpressionTag, value: string) {
        super(tag);
        this.value = value;
    }
}

class IRLiteralNatExpression extends IRLiteralIntegralNumberExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralNatExpression, value);
    }

    override toBAPI(): string {
        xxxx;
        return this.value;
    }
    
    static parseBAPIAsIRLiteralNatExpression(lexer: BAPILexer): IRLiteralNatExpression {
        xxxx;
        const value = lexer.ensureAndConsumeToken(BAPITokenKind.NatLiteral);
        return new IRLiteralNatExpression(value);
    }
}

class IRLiteralIntExpression extends IRLiteralIntegralNumberExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralIntExpression, value);
    }

    override toBAPI(): string {
        xxxx;
        return this.value;
    }
    
    static parseBAPIAsIRLiteralIntExpression(lexer: BAPILexer): IRLiteralIntExpression {
        xxxx;
        const value = lexer.ensureAndConsumeToken(BAPITokenKind.IntLiteral);
        return new IRLiteralIntExpression(value);
    }
}

class IRLiteralChkNatExpression extends IRLiteralIntegralNumberExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralChkNatExpression, value);
    }

    override toBAPI(): string {
        xxxx;
        return this.value;
    }

    static parseBAPIAsIRLiteralChkNatExpression(lexer: BAPILexer): IRLiteralChkNatExpression {
        xxxx;
        const value = lexer.ensureAndConsumeToken(BAPITokenKind.ChkNatLiteral);
        return new IRLiteralChkNatExpression(value);
    }
}

class IRLiteralChkIntExpression extends IRLiteralIntegralNumberExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralChkIntExpression, value);
    }

    override toBAPI(): string {
        xxxx;
        return this.value;
    }

    static parseBAPIAsIRLiteralChkIntExpression(lexer: BAPILexer): IRLiteralChkIntExpression {
        xxxx;
        const value = lexer.ensureAndConsumeToken(BAPITokenKind.ChkIntLiteral);
        return new IRLiteralChkIntExpression(value);
    }
}

class IRLiteralRationalExpression extends IRLiteralExpression {
    readonly numerator: string;
    readonly denominator: string;

    constructor(numerator: string, denominator: string) {
        super(IRExpressionTag.IRLiteralRationalExpression);
        this.numerator = numerator;
        this.denominator = denominator;
    }

    override toBAPI(): string {
        xxxx;
        return `${this.numerator}/${this.denominator}R`;
    }

    static parseBAPIAsIRLiteralRationalExpression(lexer: BAPILexer): IRLiteralRationalExpression {
        xxxx;
        const rlit = lexer.ensureAndConsumeToken(BAPITokenKind.RationalLiteral);
        if(!rlit.includes("/")) {
            const numerator = rlit.slice(0, -1);
            return new IRLiteralRationalExpression(numerator, "1");
        }
        else {
            const [numerator, denominator] = rlit.slice(0, -1).split("/");
            return new IRLiteralRationalExpression(numerator, denominator);
        }
    }
}

abstract class IRLiteralFloatingPointExpression extends IRLiteralExpression {
    readonly value: string;

    constructor(tag: IRExpressionTag, value: string) {
        super(tag);
        this.value = value;
    }
}

class IRLiteralFloatExpression extends IRLiteralFloatingPointExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralFloatExpression, value);
    }

    override toBAPI(): string {
        xxxx;
        return this.value;
    }

    static parseBAPIAsIRLiteralFloatExpression(lexer: BAPILexer): IRLiteralFloatExpression {
        xxxx;
        const value = lexer.ensureAndConsumeToken(BAPITokenKind.FloatLiteral);
        return new IRLiteralFloatExpression(value);
    }
}

class IRLiteralDecimalExpression extends IRLiteralFloatingPointExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralDecimalExpression, value);
    }

    override toBAPI(): string {
        return this.value;
    }

    static parseBAPIAsIRLiteralDecimalExpression(lexer: BAPILexer): IRLiteralDecimalExpression {
        const value = lexer.ensureAndConsumeToken(BAPITokenKind.DecimalLiteral);
        return new IRLiteralDecimalExpression(value);
    }
}

class IRLiteralDecimalDegreeExpression extends IRLiteralFloatingPointExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralDecimalDegreeExpression, value);
    }

    override toBAPI(): string {
        assert(false, "IRLiteralDecimalDegreeExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralDecimalDegreeExpression(lexer: BAPILexer): IRLiteralDecimalDegreeExpression {
        assert(false, "IRLiteralDecimalDegreeExpression.parseBAPI not implemented");
    }
}

class IRLiteralLatLongCoordinateExpression extends IRLiteralExpression {
    readonly latitude: string;
    readonly longitude: string;

    constructor(latitude: string, longitude: string) {
        super(IRExpressionTag.IRLiteralLatLongCoordinateExpression);
        this.latitude = latitude;
        this.longitude = longitude;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralLatLongCoordinateExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralLatLongCoordinateExpression(lexer: BAPILexer): IRLiteralLatLongCoordinateExpression {
        assert(false, "IRLiteralLatLongCoordinateExpression.parseBAPI not implemented");
    }
}

class IRLiteralComplexExpression extends IRLiteralExpression {
    readonly real: string;
    readonly imaginary: string;

    constructor(real: string, imaginary: string) {
        super(IRExpressionTag.IRLiteralComplexExpression);
        this.real = real;
        this.imaginary = imaginary;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralComplexExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralComplexExpression(lexer: BAPILexer): IRLiteralComplexExpression {
        assert(false, "IRLiteralComplexExpression.parseBAPI not implemented");
    }
}

class IRLiteralByteBufferExpression extends IRLiteralExpression {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralByteBufferExpression);
        this.bytes = bytes;
    }

    override toBAPI(): string {
        xxxx;
    }

    static parseBAPIAsIRLiteralByteBufferExpression(lexer: BAPILexer): IRLiteralByteBufferExpression {
        xxxx;
    }
}

class IRLiteralUUIDv4Expression extends IRLiteralExpression {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralUUIDv4Expression);
        this.bytes = bytes;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralUUIDv4Expression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralUUIDv4Expression(lexer: BAPILexer): IRLiteralUUIDv4Expression {
        assert(false, "IRLiteralUUIDv4Expression.parseBAPI not implemented");
    }
}

class IRLiteralUUIDv7Expression extends IRLiteralExpression {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralUUIDv7Expression);
        this.bytes = bytes;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralUUIDv7Expression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralUUIDv7Expression(lexer: BAPILexer): IRLiteralUUIDv7Expression {
        assert(false, "IRLiteralUUIDv7Expression.parseBAPI not implemented");
    }
}

class IRLiteralSHAContentHashExpression extends IRLiteralExpression {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralSHAContentHashExpression);
        this.bytes = bytes;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralSHAContentHashExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralSHAContentHashExpression(lexer: BAPILexer): IRLiteralSHAContentHashExpression {
        assert(false, "IRLiteralSHAContentHashExpression.parseBAPI not implemented");
    }
}

class IRDateRepresentation {
    readonly year: number; //1900 to 2299
    readonly month: number;
    readonly day: number;

    constructor(year: number, month: number, day: number) {
        this.year = year;
        this.month = month;
        this.day = day;
    }

    toBAPI(): string {
        assert(false, "IRDateRepresentation.toBAPI not implemented");
    }

    static parseBAPI(lexer: BAPILexer): IRDateRepresentation {
        assert(false, "IRDateRepresentation.parseBAPI not implemented");
    }
}

class IRTimeRepresentation {
    readonly hour: number;
    readonly minute: number;
    readonly second: number;

    constructor(hour: number, minute: number, second: number) {
        this.hour = hour;
        this.minute = minute;
        this.second = second;
    }

    toBAPI(): string {
        assert(false, "IRTimeRepresentation.toBAPI not implemented");
    }

    static parseBAPI(lexer: BAPILexer): IRTimeRepresentation {
        assert(false, "IRTimeRepresentation.parseBAPI not implemented");
    }
}

class IRLiteralTZDateTimeExpression extends IRLiteralExpression {
    readonly date: IRDateRepresentation;
    readonly time: IRTimeRepresentation;
    readonly timezone: string; //IANA timezone as well as freeform with printable ascii
    
    constructor(date: IRDateRepresentation, time: IRTimeRepresentation, timezone: string) {
        super(IRExpressionTag.IRLiteralTZDateTimeExpression);
        this.date = date;
        this.time = time;
        this.timezone = timezone;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralTZDateTimeExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralTZDateTimeExpression(lexer: BAPILexer): IRLiteralTZDateTimeExpression {
        assert(false, "IRLiteralTZDateTimeExpression.parseBAPI not implemented");
    }
}

class IRLiteralTAITimeExpression extends IRLiteralExpression {
    readonly date: IRDateRepresentation;
    readonly time: IRTimeRepresentation;

    constructor(date: IRDateRepresentation, time: IRTimeRepresentation) {
        super(IRExpressionTag.IRLiteralTAITimeExpression);
        this.date = date;
        this.time = time;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralTAITimeExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralTAITimeExpression(lexer: BAPILexer): IRLiteralTAITimeExpression {
        assert(false, "IRLiteralTAITimeExpression.parseBAPI not implemented");
    }
}

class IRLiteralPlainDateExpression extends IRLiteralExpression {
    readonly date: IRDateRepresentation;

    constructor(date: IRDateRepresentation) {
        super(IRExpressionTag.IRLiteralPlainDateExpression);
        this.date = date;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralPlainDateExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralPlainDateExpression(lexer: BAPILexer): IRLiteralPlainDateExpression {
        assert(false, "IRLiteralPlainDateExpression.parseBAPI not implemented");
    }
}

class IRLiteralPlainTimeExpression extends IRLiteralExpression {
    readonly time: IRTimeRepresentation;

    constructor(time: IRTimeRepresentation) {
        super(IRExpressionTag.IRLiteralPlainTimeExpression);
        this.time = time;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralPlainTimeExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralPlainTimeExpression(lexer: BAPILexer): IRLiteralPlainTimeExpression {
        assert(false, "IRLiteralPlainTimeExpression.parseBAPI not implemented");
    }
}

class IRLiteralLogicalTimeExpression extends IRLiteralExpression {
    readonly ticks: string;
    
    constructor(ticks: string) {
        super(IRExpressionTag.IRLiteralLogicalTimeExpression);
        this.ticks = ticks;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralLogicalTimeExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralLogicalTimeExpression(lexer: BAPILexer): IRLiteralLogicalTimeExpression {
        assert(false, "IRLiteralLogicalTimeExpression.parseBAPI not implemented");
    }
}

class IRLiteralISOTimeStampExpression extends IRLiteralExpression {
    readonly date: IRDateRepresentation;
    readonly time: IRTimeRepresentation;
    readonly milliseconds: number;

    constructor(date: IRDateRepresentation, time: IRTimeRepresentation, milliseconds: number) {
        super(IRExpressionTag.IRLiteralISOTimeStampExpression);
        this.date = date;
        this.time = time;
        this.milliseconds = milliseconds;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralISOTimeStampExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralISOTimeStampExpression(lexer: BAPILexer): IRLiteralISOTimeStampExpression {
        assert(false, "IRLiteralISOTimeStampExpression.parseBAPI not implemented");
    }
}

class IRDeltaDateRepresentation {
    readonly years: number;
    readonly months: number;
    readonly days: number;

    constructor(years: number, months: number, days: number) {
        this.years = years;
        this.months = months;
        this.days = days;
    }

    toBAPI(): string {
        assert(false, "IRDeltaDateRepresentation.toBAPI not implemented");
    }

    static parseBAPI(lexer: BAPILexer): IRDeltaDateRepresentation {
        assert(false, "IRDeltaDateRepresentation.parseBAPI not implemented");
    }
}

class IRDeltaTimeRepresentation {
    readonly hours: number;
    readonly minutes: number;
    readonly seconds: number;

    constructor(hours: number, minutes: number, seconds: number) {
        this.hours = hours;
        this.minutes = minutes;
        this.seconds = seconds;
    }

    toBAPI(): string {
        assert(false, "IRDeltaTimeRepresentation.toBAPI not implemented");
    }

    static parseBAPI(lexer: BAPILexer): IRDeltaTimeRepresentation {
        assert(false, "IRDeltaTimeRepresentation.parseBAPI not implemented");
    }
}

class IRLiteralDeltaDateTimeExpression extends IRLiteralExpression {
    readonly sign: "+" | "-";
    readonly deltadate: IRDeltaDateRepresentation;
    readonly deltatime: IRDeltaTimeRepresentation;

    constructor(sign: "+" | "-", deltadate: IRDeltaDateRepresentation, deltatime: IRDeltaTimeRepresentation) {
        super(IRExpressionTag.IRLiteralDeltaDateTimeExpression);
        this.sign = sign;
        this.deltadate = deltadate;
        this.deltatime = deltatime;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralDeltaDateTimeExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralDeltaDateTimeExpression(lexer: BAPILexer): IRLiteralDeltaDateTimeExpression {
        assert(false, "IRLiteralDeltaDateTimeExpression.parseBAPI not implemented");
    }
}
 
class IRLiteralDeltaISOTimeStampExpression extends IRLiteralExpression {
    readonly sign: "+" | "-";
    readonly deltadate: IRDeltaDateRepresentation;
    readonly deltatime: IRDeltaTimeRepresentation;
    readonly deltamilliseconds: BigInt;

    constructor(sign: "+" | "-", deltadate: IRDeltaDateRepresentation, deltatime: IRDeltaTimeRepresentation, deltamilliseconds: BigInt) {
        super(IRExpressionTag.IRLiteralDeltaISOTimeStampExpression);
        this.sign = sign;
        this.deltadate = deltadate;
        this.deltatime = deltatime;
        this.deltamilliseconds = deltamilliseconds;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralDeltaISOTimeStampExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralDeltaISOTimeStampExpression(lexer: BAPILexer): IRLiteralDeltaISOTimeStampExpression {
        assert(false, "IRLiteralDeltaISOTimeStampExpression.parseBAPI not implemented");
    }
} 

class IRLiteralDeltaSecondsExpression extends IRLiteralExpression {
    readonly sign: "+" | "-";
    readonly seconds: string;

    constructor(sign: "+" | "-", seconds: string) {
        super(IRExpressionTag.IRLiteralDeltaSecondsExpression);
        this.sign = sign;
        this.seconds = seconds;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralDeltaSecondsExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralDeltaSecondsExpression(lexer: BAPILexer): IRLiteralDeltaSecondsExpression {
        assert(false, "IRLiteralDeltaSecondsExpression.parseBAPI not implemented");
    }
}

class IRLiteralDeltaLogicalTimeExpression extends IRLiteralExpression {
    readonly sign: "+" | "-";
    readonly ticks: string;

    constructor(sign: "+" | "-", ticks: string) {
        super(IRExpressionTag.IRLiteralDeltaLogicalTimeExpression);
        this.sign = sign;
        this.ticks = ticks;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralDeltaLogicalTimeExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralDeltaLogicalTimeExpression(lexer: BAPILexer): IRLiteralDeltaLogicalTimeExpression {
        assert(false, "IRLiteralDeltaLogicalTimeExpression.parseBAPI not implemented");
    }
}

class IRLiteralUnicodeRegexExpression extends IRLiteralExpression {
    readonly regexID: number
    
    constructor(regexID: number) {
        super(IRExpressionTag.IRLiteralUnicodeRegexExpression);
        this.regexID = regexID;
    }

    override toBAPI(): string {
        xxxx;
    }

    static parseBAPIAsIRLiteralUnicodeRegexExpression(lexer: BAPILexer): IRLiteralUnicodeRegexExpression {
        xxxx;
    }
}

class IRLiteralCRegexExpression extends IRLiteralExpression {
    readonly regexID: number
    
    constructor(regexID: number) {
        super(IRExpressionTag.IRLiteralCRegexExpression);
        this.regexID = regexID;
    }

    override toBAPI(): string {
        xxxx;
    }

    static parseBAPIAsIRLiteralCRegexExpression(lexer: BAPILexer): IRLiteralCRegexExpression {
        xxxx;
    }
}

class IRLiteralByteExpression extends IRLiteralExpression {
    readonly value: number;

    constructor(value: number) {
        super(IRExpressionTag.IRLiteralByteExpression);
        this.value = value;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralByteExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralByteExpression(lexer: BAPILexer): IRLiteralByteExpression {
        assert(false, "IRLiteralByteExpression.parseBAPI not implemented");
    }
}

class IRLiteralCCharExpression extends IRLiteralExpression {
    readonly value: number;

    constructor(value: number) {
        super(IRExpressionTag.IRLiteralCCharExpression);
        this.value = value;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralCCharExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralCCharExpression(lexer: BAPILexer): IRLiteralCCharExpression {
        assert(false, "IRLiteralCCharExpression.parseBAPI not implemented");
    }
}

class IRLiteralUnicodeCharExpression extends IRLiteralExpression {
    readonly value: number;

    constructor(value: number) {
        super(IRExpressionTag.IRLiteralUnicodeCharExpression);
        this.value = value;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralUnicodeCharExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralUnicodeCharExpression(lexer: BAPILexer): IRLiteralUnicodeCharExpression {
        assert(false, "IRLiteralUnicodeCharExpression.parseBAPI not implemented");
    }
}

class IRLiteralCStringExpression extends IRLiteralExpression {
    readonly bytes: number[]; //char bytes

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralCStringExpression);
        this.bytes = bytes;
    }

    override toBAPI(): string {
        xxxx;
    }

    static parseBAPIAsIRLiteralCStringExpression(lexer: BAPILexer): IRLiteralCStringExpression {
        xxxx;
    }
}

class IRLiteralStringExpression extends IRLiteralExpression {
    readonly bytes: number[]; //utf8 bytes

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralStringExpression);
        this.bytes = bytes;
    }

    override toBAPI(): string {
        xxxx;
    }

    static parseBAPIAsIRLiteralStringExpression(lexer: BAPILexer): IRLiteralStringExpression {
        xxxx;
    }
}

abstract class IRFormatStringComponent {
    abstract toBAPI(): string;

    static parseBAPI(lexer: BAPILexer): IRFormatStringComponent {
        assert(false, "IRFormatStringComponent.parseBAPI not implemented");
    }
}

class IRFormatStringTextComponent extends IRFormatStringComponent {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super();
        this.bytes = bytes;
    }

    override toBAPI(): string {
        assert(false, "IRFormatStringTextComponent.toBAPI not implemented");
    }

    static parseBAPIAsIRFormatStringTextComponent(lexer: BAPILexer): IRFormatStringTextComponent {
        assert(false, "IRFormatStringTextComponent.parseBAPI not implemented");
    }
}

class IRFormatStringArgComponent extends IRFormatStringComponent {
    readonly aidx: number;
    readonly atype: IRTypeSignature;

    constructor(aidx: number, atype: IRTypeSignature) {
        super();
        this.aidx = aidx;
        this.atype = atype;
    }

    override toBAPI(): string {
        assert(false, "IRFormatStringArgComponent.toBAPI not implemented");
    }

    static parseBAPIAsIRFormatStringArgComponent(lexer: BAPILexer): IRFormatStringArgComponent {
        assert(false, "IRFormatStringArgComponent.parseBAPI not implemented");
    }
}

class IRLiteralFormatStringExpression extends IRLiteralExpression {
    readonly fmtid: number; //the format string ID assigned during flattening
    readonly fmts: IRFormatStringComponent[];

    constructor(fmtid: number, fmts: IRFormatStringComponent[]) {
        super(IRExpressionTag.IRLiteralFormatStringExpression);
        this.fmtid = fmtid;
        this.fmts = fmts;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralFormatStringExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralFormatStringExpression(lexer: BAPILexer): IRLiteralFormatStringExpression {
        assert(false, "IRLiteralFormatStringExpression.parseBAPI not implemented");
    }
}

class IRLiteralFormatCStringExpression extends IRLiteralExpression {
    readonly fmtid: number; //the format string ID assigned during flattening
    readonly fmts: IRFormatStringComponent[];

    constructor(fmtid: number, fmts: IRFormatStringComponent[]) {
        super(IRExpressionTag.IRLiteralFormatCStringExpression);
        this.fmtid = fmtid;
        this.fmts = fmts;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralFormatCStringExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralFormatCStringExpression(lexer: BAPILexer): IRLiteralFormatCStringExpression {
        assert(false, "IRLiteralFormatCStringExpression.parseBAPI not implemented");
    }
}

//
//TODO: Path literal expressions here
//

class IRLiteralTypedExpression extends IRLiteralExpression {
    readonly value: IRLiteralExpression;
    readonly constype: IRTypeSignature;

    constructor(value: IRLiteralExpression, constype: IRTypeSignature) {
        super(IRExpressionTag.IRLiteralTypedExpression);
        this.value = value;
        this.constype = constype;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralTypedExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralTypedExpression(lexer: BAPILexer): IRLiteralTypedExpression {
        assert(false, "IRLiteralTypedExpression.parseBAPI not implemented");
    }
}

class IRLiteralTypedStringExpression extends IRLiteralExpression {
    readonly bytes: number[];
    readonly constype: IRTypeSignature;

    constructor(bytes: number[], constype: IRTypeSignature) {
        super(IRExpressionTag.IRLiteralTypedStringExpression);
        this.bytes = bytes;
        this.constype = constype;
    }
    override toBAPI(): string {
        assert(false, "IRLiteralTypedStringExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralTypedStringExpression(lexer: BAPILexer): IRLiteralTypedStringExpression {
        assert(false, "IRLiteralTypedStringExpression.parseBAPI not implemented");
    }
}

class IRLiteralTypedCStringExpression extends IRLiteralExpression {
    readonly bytes: number[];
    readonly constype: IRTypeSignature;

    constructor(bytes: number[], constype: IRTypeSignature) {
        super(IRExpressionTag.IRLiteralTypedCStringExpression);
        this.bytes = bytes;
        this.constype = constype;
    }

    override toBAPI(): string {
        assert(false, "IRLiteralTypedCStringExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRLiteralTypedCStringExpression(lexer: BAPILexer): IRLiteralTypedCStringExpression {
        assert(false, "IRLiteralTypedCStringExpression.parseBAPI not implemented");
    }
}

class IRAccessEnvHasExpression extends IRExpression {
    readonly keybytes: number[];

    constructor(keybytes: number[]) {
        super(IRExpressionTag.IRAccessEnvHasExpression);
        this.keybytes = keybytes;
    }

    override isSimpleExpression(): boolean {
        return false;
    }

    override toBAPI(): string {
        assert(false, "IRAccessEnvHasExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRAccessEnvHasExpression(lexer: BAPILexer): IRAccessEnvHasExpression {
        assert(false, "IRAccessEnvHasExpression.parseBAPI not implemented");
    }
}

class IRAccessEnvGetExpression extends IRExpression {
    readonly keybytes: number[];
    readonly oftype: IRTypeSignature;

    constructor(keybytes: number[], oftype: IRTypeSignature) {
        super(IRExpressionTag.IRAccessEnvGetExpression);
        this.keybytes = keybytes;
        this.oftype = oftype;
    }

    override isSimpleExpression(): boolean {
        return false;
    }

    override toBAPI(): string {
        assert(false, "IRAccessEnvGetExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRAccessEnvGetExpression(lexer: BAPILexer): IRAccessEnvGetExpression {
        assert(false, "IRAccessEnvGetExpression.parseBAPI not implemented");
    }
}

class IRAccessEnvTryGetExpression extends IRExpression {
    readonly keybytes: number[];
    readonly oftype: IRTypeSignature;
    readonly optiontype: IRTypeSignature;

    constructor(keybytes: number[], oftype: IRTypeSignature, optiontype: IRTypeSignature) {
        super(IRExpressionTag.IRAccessEnvTryGetExpression);
        this.keybytes = keybytes;
        this.oftype = oftype;
        this.optiontype = optiontype;
    }

    override isSimpleExpression(): boolean {
        return false;
    }

    override toBAPI(): string {
        assert(false, "IRAccessEnvTryGetExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRAccessEnvTryGetExpression(lexer: BAPILexer): IRAccessEnvTryGetExpression {
        assert(false, "IRAccessEnvTryGetExpression.parseBAPI not implemented");
    }
}

class IRTaskAccessIDExpression extends IRExpression {
    constructor() {
        super(IRExpressionTag.IRTaskAccessIDExpression);
    }

    override isSimpleExpression(): boolean {
        return false;
    }

    override toBAPI(): string {
        assert(false, "IRTaskAccessIDExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRTaskAccessIDExpression(lexer: BAPILexer): IRTaskAccessIDExpression {
        assert(false, "IRTaskAccessIDExpression.parseBAPI not implemented");
    }
}

class IRTaskAccessParentIDExpression extends IRExpression {
    constructor() {
        super(IRExpressionTag.IRTaskAccessParentIDExpression);
    }

    override isSimpleExpression(): boolean {
        return false;
    }

    override toBAPI(): string {
        assert(false, "IRTaskAccessParentIDExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRTaskAccessParentIDExpression(lexer: BAPILexer): IRTaskAccessParentIDExpression {
        assert(false, "IRTaskAccessParentIDExpression.parseBAPI not implemented");
    }
}

class IRAccessConstantExpression extends IRImmediateExpression {
    readonly constkey: string; //flattened identifer names
    
    constructor(constkey: string) {
        super(IRExpressionTag.IRAccessConstantExpression);
        this.constkey = constkey;
    }

    override toBAPI(): string {
        xxxx;
    }

    static parseBAPIAsIRAccessConstantExpression(lexer: BAPILexer): IRAccessConstantExpression {
        xxxx;
    }
}

class IRAccessEnumExpression extends IRImmediateExpression {
    readonly tkey: string;
    readonly membername: string;

    constructor(tkey: string, membername: string) {
        super(IRExpressionTag.IRAccessEnumExpression);
        this.tkey = tkey;
        this.membername = membername;
    }

    override toBAPI(): string {
        assert(false, "IRAccessEnumExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRAccessEnumExpression(lexer: BAPILexer): IRAccessEnumExpression {
        assert(false, "IRAccessEnumExpression.parseBAPI not implemented");
    }
}

class IRAccessParameterVariableExpression extends IRImmediateExpression {
    readonly pname: string;

    constructor(pname: string) {
        super(IRExpressionTag.IRAccessParameterVariableExpression);
        this.pname = pname;
    }

    override toBAPI(): string {
        assert(false, "IRAccessParameterVariableExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRAccessParameterVariableExpression(lexer: BAPILexer): IRAccessParameterVariableExpression {
        assert(false, "IRAccessParameterVariableExpression.parseBAPI not implemented");
    }
}

class IRAccessLocalVariableExpression extends IRImmediateExpression {
    readonly vname: string;

    constructor(vname: string) {
        super(IRExpressionTag.IRAccessLocalVariableExpression);
        this.vname = vname;
    }

    override toBAPI(): string {
        assert(false, "IRAccessLocalVariableExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRAccessLocalVariableExpression(lexer: BAPILexer): IRAccessLocalVariableExpression {
        assert(false, "IRAccessLocalVariableExpression.parseBAPI not implemented");
    }
}

class IRAccessCapturedVariableExpression extends IRImmediateExpression {
    readonly vname: string;

    constructor(vname: string) {
        super(IRExpressionTag.IRAccessCapturedVariableExpression);
        this.vname = vname;
    }

    override toBAPI(): string {
        assert(false, "IRAccessCapturedVariableExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRAccessCapturedVariableExpression(lexer: BAPILexer): IRAccessCapturedVariableExpression {
        assert(false, "IRAccessCapturedVariableExpression.parseBAPI not implemented");
    }
}

class IRAccessTempVariableExpression extends IRImmediateExpression {
    readonly vname: string;

    constructor(vname: string) {
        super(IRExpressionTag.IRAccessTempVariableExpression);
        this.vname = vname;
    }

    override toBAPI(): string {
        assert(false, "IRAccessTempVariableExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRAccessTempVariableExpression(lexer: BAPILexer): IRAccessTempVariableExpression {
        assert(false, "IRAccessTempVariableExpression.parseBAPI not implemented");
    }
}

class IRAccessTypeDeclValueExpression extends IRSimpleExpression {
    readonly accesstype: IRNominalTypeSignature;
    readonly exp: IRSimpleExpression;

    constructor(accesstype: IRNominalTypeSignature, exp: IRSimpleExpression) {
        super(IRExpressionTag.IRAccessTypeDeclValueExpression);
        this.accesstype = accesstype;
        this.exp = exp;
    }

    override toBAPI(): string {
        assert(false, "IRAccessTypeDeclValueExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRAccessTypeDeclValueExpression(lexer: BAPILexer): IRAccessTypeDeclValueExpression {
        assert(false, "IRAccessTypeDeclValueExpression.parseBAPI not implemented");
    }
}

class IRConstructSafeTypeDeclExpression extends IRSimpleExpression {
    readonly constype: IRNominalTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(constype: IRNominalTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructSafeTypeDeclExpression);
        this.constype = constype;
        this.value = value;
    }

    override toBAPI(): string {
        assert(false, "IRConstructSafeTypeDeclExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRConstructSafeTypeDeclExpression(lexer: BAPILexer): IRConstructSafeTypeDeclExpression {
        assert(false, "IRConstructSafeTypeDeclExpression.parseBAPI not implemented");
    }
}

class IRConstructorSomeTypeExpression extends IRSimpleExpression {
    readonly oftype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(oftype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructorSomeTypeExpression);
        this.oftype = oftype;
        this.value = value;
    }

    override toBAPI(): string {
        assert(false, "IRConstructorSomeTypeExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRConstructorSomeTypeExpression(lexer: BAPILexer): IRConstructorSomeTypeExpression {
        assert(false, "IRConstructorSomeTypeExpression.parseBAPI not implemented");
    }
}

class IRConstructorOkTypeExpression extends IRSimpleExpression {
    readonly oftype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(oftype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructorOkTypeExpression);
        this.oftype = oftype;
        this.value = value;
    }

    override toBAPI(): string {
        assert(false, "IRConstructorOkTypeExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRConstructorOkTypeExpression(lexer: BAPILexer): IRConstructorOkTypeExpression {
        assert(false, "IRConstructorOkTypeExpression.parseBAPI not implemented");
    }
}

class IRConstructorFailTypeExpression extends IRSimpleExpression {
    readonly oftype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(oftype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructorFailTypeExpression);
        this.oftype = oftype;
        this.value = value;
    }

    override toBAPI(): string {
        assert(false, "IRConstructorFailTypeExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRConstructorFailTypeExpression(lexer: BAPILexer): IRConstructorFailTypeExpression {
        assert(false, "IRConstructorFailTypeExpression.parseBAPI not implemented");
    }
}

class IRConstructorMapEntryTypeExpression extends IRSimpleExpression {
    readonly oftype: IRTypeSignature;
    readonly key: IRSimpleExpression;
    readonly value: IRSimpleExpression;

    constructor(oftype: IRTypeSignature, key: IRSimpleExpression, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructorMapEntryTypeExpression);
        this.oftype = oftype;
        this.key = key;
        this.value = value;
    }

    override toBAPI(): string {
        assert(false, "IRConstructorMapEntryTypeExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRConstructorMapEntryTypeExpression(lexer: BAPILexer): IRConstructorMapEntryTypeExpression {
        assert(false, "IRConstructorMapEntryTypeExpression.parseBAPI not implemented");
    }
}

//TODO: maybe add a specialized version of this that does boxing to a concept as well
class IRConstructorStandardEntityExpression extends IRConstructExpression {
    readonly values: IRSimpleExpression[];

    constructor(entitytype: IRNominalTypeSignature, values: IRSimpleExpression[]) {
        super(IRExpressionTag.IRConstructorStandardEntityExpression, entitytype);
        this.values = values;
    }

    override toBAPI(): string {
        assert(false, "IRConstructorStandardEntityExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRConstructorStandardEntityExpression(lexer: BAPILexer): IRConstructorStandardEntityExpression {
        assert(false, "IRConstructorStandardEntityExpression.parseBAPI not implemented");
    }
}

//TODO: maybe add a specialized version of this that does boxing to a concept as well
class IRConstructorLambdaExpression extends IRImmediateExpression {
    readonly ltype: IRLambdaParameterPackTypeSignature;
    readonly values: IRImmediateExpression[];
    
    constructor(entitytype: IRLambdaParameterPackTypeSignature, values: IRImmediateExpression[]) {
        super(IRExpressionTag.IRConstructorLambdaExpression);
        this.ltype = entitytype;
        this.values = values;
    }

    override toBAPI(): string {
        assert(false, "IRConstructorLambdaExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRConstructorLambdaExpression(lexer: BAPILexer): IRConstructorLambdaExpression {
        assert(false, "IRConstructorLambdaExpression.parseBAPI not implemented");
    }
}

class IRConstructorEListExpression extends IRSimpleExpression {
    readonly eltype: IREListTypeSignature;
    readonly values: IRSimpleExpression[];

    constructor(eltype: IREListTypeSignature, values: IRSimpleExpression[]) {
        super(IRExpressionTag.IRConstructorEListExpression);
        this.eltype = eltype;
        this.values = values;
    }

    override toBAPI(): string {
        assert(false, "IRConstructorEListExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRConstructorEListExpression(lexer: BAPILexer): IRConstructorEListExpression {
        assert(false, "IRConstructorEListExpression.parseBAPI not implemented");
    }
}

/* NOTE -- the empty constructor is a simple expression (as it is really a constant) we can place anywhere safely */
class IRConstructorListEmptyExpression extends IRConstructExpression {
    
    constructor(ctype: IRNominalTypeSignature) {
        super(IRExpressionTag.IRConstructorListEmptyExpression, ctype);
    }

    override toBAPI(): string {
        assert(false, "IRConstructorListEmptyExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRConstructorListEmptyExpression(lexer: BAPILexer): IRConstructorListEmptyExpression {
        assert(false, "IRConstructorListEmptyExpression.parseBAPI not implemented");
    }
}

class IRConstructorListSingletonsExpression extends IRConstructExpression {
    readonly elements: IRSimpleExpression[];

    constructor(ctype: IRNominalTypeSignature, elements: IRSimpleExpression[]) {
        super(IRExpressionTag.IRConstructorListSingletonsExpression, ctype);
        this.elements = elements;
    }

    override toBAPI(): string {
        assert(false, "IRConstructorListSingletonsExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRConstructorListSingletonsExpression(lexer: BAPILexer): IRConstructorListSingletonsExpression {
        assert(false, "IRConstructorListSingletonsExpression.parseBAPI not implemented");
    }
}

/* NOTE -- the empty constructor is a simple expression (as it is really a constant) we can place anywhere safely */
class IRConstructorMapEmptyExpression extends IRConstructExpression {
    
    constructor(ctype: IRNominalTypeSignature) {
        super(IRExpressionTag.IRConstructorMapEmptyExpression, ctype);
    }

    override toBAPI(): string {
        assert(false, "IRConstructorMapEmptyExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRConstructorMapEmptyExpression(lexer: BAPILexer): IRConstructorMapEmptyExpression {
        assert(false, "IRConstructorMapEmptyExpression.parseBAPI not implemented");
    }
}

class IRConstructorMapSingletonsExpression extends IRConstructExpression {
    readonly elements: IRSimpleExpression[];

    constructor(ctype: IRNominalTypeSignature, elements: IRSimpleExpression[]) {
        super(IRExpressionTag.IRConstructorMapSingletonsExpression, ctype);
        this.elements = elements;
    }
    override toBAPI(): string {
        assert(false, "IRConstructorMapSingletonsExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRConstructorMapSingletonsExpression(lexer: BAPILexer): IRConstructorMapSingletonsExpression {
        assert(false, "IRConstructorMapSingletonsExpression.parseBAPI not implemented");
    }
}

//
//TODO: lots more expression types here
//

class IRAccessFieldSpecialExpression extends IRAccessFieldExpression {
    constructor(eexptype: IRNominalTypeSignature, eexp: IRSimpleExpression, intype: IRNominalTypeSignature, fieldname: string, fieldtype: IRTypeSignature) {
        super(IRExpressionTag.IRAccessFieldSpecialExpression, eexptype, eexp, intype, fieldname, fieldtype);
    }

    override toBAPI(): string {
        assert(false, "IRAccessFieldSpecialExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRAccessFieldSpecialExpression(lexer: BAPILexer): IRAccessFieldSpecialExpression {
        assert(false, "IRAccessFieldSpecialExpression.parseBAPI not implemented");
    }
}

class IRAccessFieldDirectExpression extends IRAccessFieldExpression {
    constructor(eexptype: IRNominalTypeSignature, eexp: IRSimpleExpression, intype: IRNominalTypeSignature, fieldname: string, fieldtype: IRTypeSignature) {
        super(IRExpressionTag.IRAccessFieldDirectExpression, eexptype, eexp, intype, fieldname, fieldtype);
    }

    override toBAPI(): string {
        assert(false, "IRAccessFieldDirectExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRAccessFieldDirectExpression(lexer: BAPILexer): IRAccessFieldDirectExpression {
        assert(false, "IRAccessFieldDirectExpression.parseBAPI not implemented");
    }
}

class IRAccessFieldVirtualExpression extends IRAccessFieldExpression {
    constructor(eexptype: IRNominalTypeSignature, eexp: IRSimpleExpression, intype: IRNominalTypeSignature, fieldname: string, fieldtype: IRTypeSignature) {
        super(IRExpressionTag.IRAccessFieldVirtualExpression, eexptype, eexp, intype, fieldname, fieldtype);
    }

    override toBAPI(): string {
        assert(false, "IRAccessFieldVirtualExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRAccessFieldVirtualExpression(lexer: BAPILexer): IRAccessFieldVirtualExpression {
        assert(false, "IRAccessFieldVirtualExpression.parseBAPI not implemented");
    }
}

class IRAccessEListIndexExpression extends IRSimpleExpression {
    readonly eltype: IREListTypeSignature;
    readonly eexp: IRSimpleExpression;
    readonly idx: number;

    constructor(eltype: IREListTypeSignature, eexp: IRSimpleExpression, idx: number) {
        super(IRExpressionTag.IRAccessEListIndexExpression);
        this.eltype = eltype;
        this.eexp = eexp;
        this.idx = idx;
    }

    override toBAPI(): string {
        assert(false, "IRAccessEListIndexExpression.toBAPI not implemented");
    }

    static parseBAPIAsIRAccessEListIndexExpression(lexer: BAPILexer): IRAccessEListIndexExpression {
        assert(false, "IRAccessEListIndexExpression.parseBAPI not implemented");
    }
}

/** Simple invocations functions/methods/lambdas that do not have any special parameters **/
class IRInvokeSimpleExpression extends IRInvokeDirectExpression {
    constructor(ikey: string, args: IRSimpleExpression[]) {
        super(IRExpressionTag.IRInvokeSimpleExpression, ikey, args);
    }
}

/** Simple invocations functions/methods/lambdas that have any special ref/out/out?/inout parameters **/
class IRInvokeSimpleWithImplicitsExpression extends IRInvokeImplicitsExpression {
    constructor(ikey: string, args: IRSimpleExpression[], implicitidx: number, ivar: string, ivartype: IRTypeSignature, passkind: "ref" | "out" | "out?" | "inout") {
        super(IRExpressionTag.IRInvokeSimpleWithImplicitsExpression, ikey, args, implicitidx, ivar, ivartype, passkind);
    }
}

/** Virtual invocations functions/methods/lambdas that do not have any special parameters (arg0 is the receiver) **/
class IRInvokeVirtualSimpleExpression extends IRInvokeDirectExpression {
    readonly rcvr: IRImmediateExpression;

    constructor(ikey: string, rcvr: IRImmediateExpression, args: IRSimpleExpression[]) {
        super(IRExpressionTag.IRInvokeVirtualSimpleExpression, ikey, args);
        this.rcvr = rcvr;
    }
}

/** Virtual invocations functions/methods/lambdas that have any special ref/out/out?/inout parameters (arg0 is the receiver) **/
class IRInvokeVirtualWithImplicitsExpression extends IRInvokeImplicitsExpression {
    readonly rcvr: IRImmediateExpression;

    constructor(ikey: string, rcvr: IRImmediateExpression, args: IRSimpleExpression[], implicitidx: number, ivar: string, ivartype: IRTypeSignature, passkind: "ref" | "out" | "out?" | "inout") {
        super(IRExpressionTag.IRInvokeVirtualWithImplicitsExpression, ikey, args, implicitidx, ivar, ivartype, passkind);
        this.rcvr = rcvr;
    }
}

class IRInterpolateFormatCStringExpression extends IRConstructExpression {
    readonly fmtString: IRSimpleExpression;
    readonly args: IRSimpleExpression[];
    
    constructor(fmtString: IRSimpleExpression, args: IRSimpleExpression[]) {
        super(IRExpressionTag.IRInterpolateFormatCStringExpression, new IRNominalTypeSignature("CString"));
        this.fmtString = fmtString;
        this.args = args;
    }
}

class IRInterpolateFormatStringExpression extends IRConstructExpression {
    readonly fmtString: IRSimpleExpression;
    readonly args: IRSimpleExpression[];
    
    constructor(fmtString: IRSimpleExpression, args: IRSimpleExpression[]) {
        super(IRExpressionTag.IRInterpolateFormatCStringExpression, new IRNominalTypeSignature("String"));
        this.fmtString = fmtString;
        this.args = args;
    }
}

abstract class IRUnaryOpExpression extends IRSimpleExpression {
    readonly exp: IRSimpleExpression;
    readonly opertype: IRTypeSignature;

    constructor(tag: IRExpressionTag, exp: IRSimpleExpression, opertype: IRTypeSignature) {
        super(tag);
        this.exp = exp;
        this.opertype = opertype;
    }
}

class IRPrefixNotOpExpression extends IRUnaryOpExpression {
    constructor(exp: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRPrefixNotOpExpression, exp, opertype);
    }
}

class IRPrefixNegateOpExpression extends IRUnaryOpExpression {
    constructor(exp: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRPrefixNegateOpExpression, exp, opertype);
    }
}

class IRPrefixPlusOpExpression extends IRUnaryOpExpression {
    constructor(exp: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRPrefixPlusOpExpression, exp, opertype);
    }
}

abstract class IRBinOpExpression extends IRSimpleExpression {
    readonly left: IRSimpleExpression;
    readonly right: IRSimpleExpression;
    readonly opertype: IRTypeSignature;

    constructor(tag: IRExpressionTag, left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(tag);
        this.left = left;
        this.right = right;
        this.opertype = opertype;
    }
}

class IRBinAddExpression extends IRBinOpExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRBinAddExpression, left, right, opertype);
    }
}

class IRBinSubExpression extends IRBinOpExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRBinSubExpression, left, right, opertype);
    }
}

class IRBinMultExpression extends IRBinOpExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRBinMultExpression, left, right, opertype);
    }
}

class IRBinDivExpression extends IRBinOpExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRBinDivExpression, left, right, opertype);
    }
}

abstract class IRNumericComparisonExpression extends IRSimpleExpression {
    readonly left: IRSimpleExpression;
    readonly right: IRSimpleExpression;
    readonly opertype: IRTypeSignature;

    constructor(tag: IRExpressionTag, left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(tag);
        this.left = left;
        this.right = right;
        this.opertype = opertype;
    }
}

class IRNumericEqExpression extends IRNumericComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRNumericEqExpression, left, right, opertype);
    }
}

class IRNumericNeqExpression extends IRNumericComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRNumericNeqExpression, left, right, opertype);
    }
}

class IRNumericLessExpression extends IRNumericComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRNumericLessExpression, left, right, opertype);
    }
}

class IRNumericLessEqExpression extends IRNumericComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRNumericLessEqExpression, left, right, opertype);
    }
}

class IRNumericGreaterExpression extends IRNumericComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRNumericGreaterExpression, left, right, opertype);
    }
}

class IRNumericGreaterEqExpression extends IRNumericComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRNumericGreaterEqExpression, left, right, opertype);
    }
}

class IRIsNoneOptionExpression extends IRSimpleExpression {
    readonly exp: IRSimpleExpression;
    readonly opttype: IRTypeSignature;

    constructor(exp: IRSimpleExpression, opttype: IRTypeSignature) {
        super(IRExpressionTag.IRIsNoneOptionExpression);
        this.exp = exp;
        this.opttype = opttype;
    }
}

class IRIsNotNoneOptionExpression extends IRSimpleExpression {
    readonly exp: IRSimpleExpression;
    readonly opttype: IRTypeSignature;

    constructor(exp: IRSimpleExpression, opttype: IRTypeSignature) {
        super(IRExpressionTag.IRIsNotNoneOptionExpression);
        this.exp = exp;
        this.opttype = opttype;
    }
}

class IRIsOptionEqValueExpression extends IRSimpleExpression {
    readonly optexp: IRSimpleExpression;
    readonly opttype: IRTypeSignature;

    readonly valexp: IRSimpleExpression;
    readonly valtype: IRTypeSignature;

    constructor(optexp: IRSimpleExpression, opttype: IRTypeSignature, valexp: IRSimpleExpression, valtype: IRTypeSignature) {
        super(IRExpressionTag.IRIsOptionEqValueExpression);
        this.optexp = optexp;
        this.opttype = opttype;
        this.valexp = valexp;
        this.valtype = valtype;
    }
}

class IRIsOptionNeqValueExpression extends IRSimpleExpression {
    readonly optexp: IRSimpleExpression;
    readonly opttype: IRTypeSignature;

    readonly valexp: IRSimpleExpression;
    readonly valtype: IRTypeSignature;

    constructor(optexp: IRSimpleExpression, opttype: IRTypeSignature, valexp: IRSimpleExpression, valtype: IRTypeSignature) {
        super(IRExpressionTag.IRIsOptionNeqValueExpression);
        this.optexp = optexp;
        this.opttype = opttype;
        this.valexp = valexp;
        this.valtype = valtype;
    }
}

class IRIsSomeEqValueExpression extends IRSimpleExpression {
    readonly someexp: IRSimpleExpression;
    readonly sometype: IRTypeSignature;

    readonly valexp: IRSimpleExpression;
    readonly valtype: IRTypeSignature;

    constructor(someexp: IRSimpleExpression, sometype: IRTypeSignature, valexp: IRSimpleExpression, valtype: IRTypeSignature) {
        super(IRExpressionTag.IRIsSomeEqValueExpression);
        this.someexp = someexp;
        this.sometype = sometype;
        this.valexp = valexp;
        this.valtype = valtype;
    }
}

class IRIsSomeNeqValueExpression extends IRSimpleExpression {
    readonly someexp: IRSimpleExpression;
    readonly sometype: IRTypeSignature;

    readonly valexp: IRSimpleExpression;
    readonly valtype: IRTypeSignature;

    constructor(someexp: IRSimpleExpression, sometype: IRTypeSignature, valexp: IRSimpleExpression, valtype: IRTypeSignature) {
        super(IRExpressionTag.IRIsSomeNeqValueExpression);
        this.someexp = someexp;
        this.sometype = sometype;
        this.valexp = valexp;
        this.valtype = valtype;
    }
}

abstract class IRKeyComparisonExpression extends IRSimpleExpression {
    readonly left: IRSimpleExpression;
    readonly right: IRSimpleExpression;
    readonly opertype: IRTypeSignature;

    constructor(tag: IRExpressionTag, left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(tag);
        this.left = left;
        this.right = right;
        this.opertype = opertype;
    }
}

class IRBinKeyEqDirectExpression extends IRKeyComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRBinKeyEqDirectExpression, left, right, opertype);
    }
}

class IRBinKeyNeqDirectExpression extends IRKeyComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRBinKeyNeqDirectExpression, left, right, opertype);
    }
}

class IRBinKeyLessDirectExpression extends IRKeyComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRBinKeyLessDirectExpression, left, right, opertype);
    }
}

abstract class IRLogicOpExpression extends IRSimpleExpression {
    readonly args: IRSimpleExpression[];

    constructor(tag: IRExpressionTag, args: IRSimpleExpression[]) {
        super(tag);
        this.args = args;
    }
}

class IRLogicAndExpression extends IRLogicOpExpression {
    constructor(args: IRSimpleExpression[]) {
        super(IRExpressionTag.IRLogicAndExpression, args);
    }
}

class IRLogicOrExpression extends IRLogicOpExpression {
    constructor(args: IRSimpleExpression[]) {
        super(IRExpressionTag.IRLogicOrExpression, args);
    }
}

class IRLogicSimpleConditionalExpression extends IRSimpleExpression {
    readonly condition: IRSimpleExpression;
    readonly trueexp: IRSimpleExpression;
    readonly falseexp: IRSimpleExpression;

    constructor(condition: IRSimpleExpression, trueexp: IRSimpleExpression, falseexp: IRSimpleExpression) {
        super(IRExpressionTag.IRLogicSimpleConditionalExpression);
        this.condition = condition;
        this.trueexp = trueexp;
        this.falseexp = falseexp;
    }
}

class IRLiteralOptionOfNoneExpression extends IRLiteralExpression {
    readonly opttype: IRTypeSignature;

    constructor(opttype: IRTypeSignature) {
        super(IRExpressionTag.IRLiteralOptionOfNoneExpression);
        this.opttype = opttype;
    }
}

class IRConstructOptionFromSomeExpression extends IRSimpleExpression {
    readonly opttype: IRTypeSignature;
    readonly sometype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(opttype: IRTypeSignature, sometype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructOptionFromSomeExpression);
        this.opttype = opttype;
        this.sometype = sometype;
        this.value = value;
    }
}

class IRExtractSomeFromOptionExpression extends IRSimpleExpression {
    readonly opttype: IRTypeSignature;
    readonly sometype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(opttype: IRTypeSignature, sometype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRExtractSomeFromOptionExpression);
        this.opttype = opttype;
        this.sometype = sometype;
        this.value = value;
    }
}

class IRExtractSomeValueFromOptionExpression extends IRSimpleExpression {
    readonly opttype: IRTypeSignature;
    readonly sometype: IRTypeSignature;
    readonly ttype : IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(opttype: IRTypeSignature, sometype: IRTypeSignature, ttype : IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRExtractSomeValueFromOptionExpression);
        this.opttype = opttype;
        this.sometype = sometype;
        this.ttype = ttype;
        this.value = value;
    }
}

class IRConstructResultFromOkExpression extends IRSimpleExpression {
    readonly rtype: IRTypeSignature;
    readonly oktype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(rtype: IRTypeSignature, oktype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructResultFromOkExpression);
        this.rtype = rtype;
        this.oktype = oktype;
        this.value = value;
    }
}

class IRConstructResultFromFailExpression extends IRSimpleExpression {
    readonly rtype: IRTypeSignature;
    readonly failtype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(rtype: IRTypeSignature, failtype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructResultFromFailExpression);
        this.rtype = rtype;
        this.failtype = failtype;
        this.value = value;
    }
}

class IRExtractOkFromResultExpression extends IRSimpleExpression {
    readonly rtype: IRTypeSignature;
    readonly oktype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(rtype: IRTypeSignature, oktype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRExtractOkFromResultExpression);
        this.rtype = rtype;
        this.oktype = oktype;
        this.value = value;
    }
}

class IRExtractOkValueFromResultExpression extends IRSimpleExpression {
    readonly rtype: IRTypeSignature;
    readonly oktype: IRTypeSignature;
    readonly ttype : IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(rtype: IRTypeSignature, oktype: IRTypeSignature, ttype : IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRExtractOkValueFromResultExpression);
        this.rtype = rtype;
        this.oktype = oktype;
        this.ttype = ttype;
        this.value = value;
    }
}

class IRExtractFailFromResultExpression extends IRSimpleExpression {
    readonly rtype: IRTypeSignature;
    readonly failtype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(rtype: IRTypeSignature, failtype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRExtractFailFromResultExpression);
        this.rtype = rtype;
        this.failtype = failtype;
        this.value = value;
    }
}

class IRExtractFailValueFromResultExpression extends IRSimpleExpression {
    readonly rtype: IRTypeSignature;
    readonly failtype: IRTypeSignature;
    readonly etype : IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(rtype: IRTypeSignature, failtype: IRTypeSignature, etype : IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRExtractFailValueFromResultExpression);
        this.rtype = rtype;
        this.failtype = failtype;
        this.etype = etype;
        this.value = value;
    }
}

abstract class IRConceptRepresentationOfTypeExpression extends IRSimpleExpression {
    readonly exp: IRSimpleExpression;
    readonly exptype: IRTypeSignature;
    readonly targettype: IRTypeSignature;

    constructor(tag: IRExpressionTag, exp: IRSimpleExpression, exptype: IRTypeSignature, targettype: IRTypeSignature) {
        super(tag);
        this.exp = exp;
        this.exptype = exptype;
        this.targettype = targettype;
    }
}

class IRIsConceptRepresentationOfTypeExpression extends IRConceptRepresentationOfTypeExpression {
    constructor(exp: IRSimpleExpression, exptype: IRTypeSignature, targettype: IRTypeSignature) {
        super(IRExpressionTag.IRIsConceptRepresentationOfTypeExpression, exp, exptype, targettype);
    }
}

class IRIsNotConceptRepresentationOfTypeExpression extends IRConceptRepresentationOfTypeExpression {
    constructor(exp: IRSimpleExpression, exptype: IRTypeSignature, targettype: IRTypeSignature) {
        super(IRExpressionTag.IRIsNotConceptRepresentationOfTypeExpression, exp, exptype, targettype);
    }
}

class IRIsConceptRepresentationSubtypeOfTypeExpression extends IRConceptRepresentationOfTypeExpression {
    constructor(exp: IRSimpleExpression, exptype: IRTypeSignature, targettype: IRTypeSignature) {
        super(IRExpressionTag.IRIsConceptRepresentationSubtypeOfTypeExpression, exp, exptype, targettype);
    }
}

class IRIsNotConceptRepresentationSubtypeOfTypeExpression extends IRConceptRepresentationOfTypeExpression {
    constructor(exp: IRSimpleExpression, exptype: IRTypeSignature, targettype: IRTypeSignature) {
        super(IRExpressionTag.IRIsNotConceptRepresentationSubtypeOfTypeExpression, exp, exptype, targettype);
    }
}

class IRStaticIsTypeSubtypeOfExpression extends IRSimpleExpression {
    readonly isnot: boolean; //true if this check is negated

    readonly exptype: IRTypeSignature;
    readonly targettype: IRTypeSignature;

    constructor(exptype: IRTypeSignature, targettype: IRTypeSignature, isnot: boolean) {
        super(IRExpressionTag.IRStaticIsTypeSubtypeOfExpression);
        this.exptype = exptype;
        this.targettype = targettype;
        this.isnot = isnot;
    }
}

class IRBoxEntityToConceptRepresentationExpression extends IRSimpleExpression {
    readonly totype: IRTypeSignature;
    readonly fromtype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(totype: IRTypeSignature, fromtype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRBoxEntityToConceptRepresentationExpression);
        this.totype = totype;
        this.fromtype = fromtype;
        this.value = value;
    }
}

class IRUnboxEntityFromConceptRepresentationExpression extends IRSimpleExpression {
    readonly fromtype: IRTypeSignature;
    readonly totype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(fromtype: IRTypeSignature, totype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRUnboxEntityFromConceptRepresentationExpression);
        this.fromtype = fromtype;
        this.totype = totype;
        this.value = value;
    }
}

class IRConvertConceptRepresentationExpression extends IRSimpleExpression {
    readonly fromtype: IRTypeSignature;
    readonly totype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(fromtype: IRTypeSignature, totype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConvertConceptRepresentationExpression);
        this.fromtype = fromtype;
        this.totype = totype;
        this.value = value;
    }
}

////////////////////////////////////////
//Basic Line statements

class IRNopStatement extends IRAtomicStatement {
    constructor() {
        super(IRStatementTag.IRNopStatement);
    }

    override isSimpleStatement(): boolean {
        return true;
    }
}

class IRTempAssignExpressionStatement extends IRTempAssignStatement {
    readonly rhs: IRExpression;

    constructor(tname: string, rhs: IRExpression, ttype: IRTypeSignature) {
        super(IRStatementTag.IRTempAssignExpressionStatement, tname, ttype);
        this.rhs = rhs;
    }
}

class IRTempAssignStdInvokeStatement extends IRTempAssignStatement {
    readonly rhs: IRInvokeSimpleExpression;

    constructor(tname: string, rhs: IRInvokeSimpleExpression, ttype: IRTypeSignature) {
        super(IRStatementTag.IRTempAssignStdInvokeStatement, tname, ttype);
        this.rhs = rhs;
    }
}

//We definitely need to have the var type include the ref/out/intout.. placeholder info AND may need to check error results on this in smt
class IRTempAssignRefInvokeStatement extends IRTempAssignStatement {
    readonly ivar: string; //the implicit variable to assign the returned ref/out/out?/inout parameter
    readonly ivartype: IRTypeSignature;
    readonly passkind : "ref" | "out" | "out?" | "inout";
    readonly rhs: IRInvokeImplicitsExpression;

    constructor(tname: string, ttype: IRTypeSignature, ivar: string, ivartype: IRTypeSignature, passkind: "ref" | "out" | "out?" | "inout", rhs: IRInvokeImplicitsExpression) {
        super(IRStatementTag.IRTempAssignRefInvokeStatement, tname, ttype);
        this.ivar = ivar;
        this.ivartype = ivartype;
        this.passkind = passkind;
        this.rhs = rhs;
    }
}

class IRTempAssignDirectConstructorStatement extends IRTempAssignStatement {
    readonly rhs: IRConstructExpression;

    constructor(tname: string, ttype: IRTypeSignature, rhs: IRConstructExpression) {
        super(IRStatementTag.IRTempAssignDirectConstructorStatement, tname, ttype);
        this.rhs = rhs;
    }
}

class IRVariableDeclarationStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;

    constructor(vname: string, vtype: IRTypeSignature) {
        super(IRStatementTag.IRVariableDeclarationStatement);
        this.vname = vname;
        this.vtype = vtype;
    }

    override isSimpleStatement(): boolean {
        return true;
    }
}

class IRVariableInitializationStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly initexp: IRSimpleExpression;
    readonly isconst: boolean;

    constructor(vname: string, vtype: IRTypeSignature, initexp: IRSimpleExpression, isconst: boolean) {
        super(IRStatementTag.IRVariableInitializationStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.initexp = initexp;
        this.isconst = isconst;
    }

    override isSimpleStatement(): boolean {
        return true;
    }
}

class IRVariableInitializationDirectInvokeStatement extends IRAtomicStatement {
    readonly scratchname: string; //a scratch temp variable to hold the direct invoke result if needed -- e.g. in SMT place result here, check for errors, then extract to vname
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly initexp: IRInvokeDirectExpression;
    readonly isconst: boolean;

    constructor(scratch: string, vname: string, vtype: IRTypeSignature, initexp: IRInvokeDirectExpression, isconst: boolean) {
        super(IRStatementTag.IRVariableInitializationDirectInvokeStatement);
        this.scratchname = scratch;
        this.vname = vname;
        this.vtype = vtype;
        this.initexp = initexp;
        this.isconst = isconst;
    }

    override isSimpleStatement(): boolean {
        return false;
    }
}

class IRVariableInitializationDirectInvokeWithImplicitStatement extends IRAtomicStatement {
    readonly scratchname: string; //a scratch temp variable to hold the direct invoke result if needed -- e.g. in SMT place result here, check for errors, then extract to vname
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly initexp: IRInvokeImplicitsExpression;
    readonly isconst: boolean;

    constructor(scratch: string, vname: string, vtype: IRTypeSignature, initexp: IRInvokeImplicitsExpression, isconst: boolean) {
        super(IRStatementTag.IRVariableInitializationDirectInvokeWithImplicitStatement);
        this.scratchname = scratch;
        this.vname = vname;
        this.vtype = vtype;
        this.initexp = initexp;
        this.isconst = isconst;
    }

    override isSimpleStatement(): boolean {
        return false;
    }
}

class IRVariableInitializationDirectConstructorStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly initexp: IRConstructExpression;
    readonly isconst: boolean;

    constructor(vname: string, vtype: IRTypeSignature, initexp: IRConstructExpression, isconst: boolean) {
        super(IRStatementTag.IRVariableInitializationDirectConstructorStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.initexp = initexp;
        this.isconst = isconst;
    }

    override isSimpleStatement(): boolean {
        return true;
    }
}

class IRVariableInitializationDirectConstructorWithBoxStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly fromtype: IRTypeSignature;
    readonly initexp: IRConstructExpression;
    readonly isconst: boolean;

    constructor(vname: string, vtype: IRTypeSignature, fromtype: IRTypeSignature, initexp: IRConstructExpression, isconst: boolean) {
        super(IRStatementTag.IRVariableInitializationDirectConstructorWithBoxStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.fromtype = fromtype;
        this.initexp = initexp;
        this.isconst = isconst;
    }

    override isSimpleStatement(): boolean {
        return true;
    }
}

class IRVariableAssignmentStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly aexp: IRSimpleExpression;

    constructor(vname: string, vtype: IRTypeSignature, aexp: IRSimpleExpression) {
        super(IRStatementTag.IRVariableAssignmentStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.aexp = aexp;
    }

    override isSimpleStatement(): boolean {
        return true;
    }
}

class IRVariableAssignmentDirectInvokeStatement extends IRAtomicStatement {
    readonly scratchname: string; //a scratch temp variable to hold the direct invoke result if needed -- e.g. in SMT place result here, check for errors, then extract to vname
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly aexp: IRInvokeDirectExpression;

    constructor(scratch: string, vname: string, vtype: IRTypeSignature, aexp: IRInvokeDirectExpression) {
        super(IRStatementTag.IRVariableAssignmentDirectInvokeStatement);
        this.scratchname = scratch;
        this.vname = vname;
        this.vtype = vtype;
        this.aexp = aexp;
    }

    override isSimpleStatement(): boolean {
        return false;
    }
}

class IRVariableAssignmentDirectInvokeWithImplicitStatement extends IRAtomicStatement {
    readonly scratchname: string; //a scratch temp variable to hold the direct invoke result if needed -- e.g. in SMT place result here, check for errors, then extract to vname
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly aexp: IRInvokeImplicitsExpression;

    constructor(scratch: string, vname: string, vtype: IRTypeSignature, aexp: IRInvokeImplicitsExpression) {
        super(IRStatementTag.IRVariableAssignmentDirectInvokeWithImplicitStatement);
        this.scratchname = scratch;
        this.vname = vname;
        this.vtype = vtype;
        this.aexp = aexp;
    }

    override isSimpleStatement(): boolean {
        return false;
    }
}

class IRVariableAssignmentDirectConstructorStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly aexp: IRConstructExpression;

    constructor(vname: string, vtype: IRTypeSignature, aexp: IRConstructExpression) {
        super(IRStatementTag.IRVariableAssignmentDirectConstructorStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.aexp = aexp;
    }

    override isSimpleStatement(): boolean {
        return true;
    }
}

class IRVariableAssignmentDirectConstructorWithBoxStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly fromtype: IRTypeSignature;
    readonly aexp: IRConstructExpression;

    constructor(vname: string, vtype: IRTypeSignature, fromtype: IRTypeSignature, aexp: IRConstructExpression) {
        super(IRStatementTag.IRVariableAssignmentDirectConstructorWithBoxStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.fromtype = fromtype;
        this.aexp = aexp;
    }

    override isSimpleStatement(): boolean {
        return true;
    }
}

class IRUpdateLocalDirectStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature
    readonly aargs: IRSimpleExpression[];

    constructor(vname: string, vtype: IRTypeSignature, aargs: IRSimpleExpression[]) {
        super(IRStatementTag.IRUpdateLocalDirectStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.aargs = aargs;
    }

    override isSimpleStatement(): boolean {
        return true;
    }
}

class IRUpdateParamDirectStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly aargs: IRSimpleExpression[];

    constructor(vname: string, vtype: IRTypeSignature, aargs: IRSimpleExpression[]) {
        super(IRStatementTag.IRUpdateParamDirectStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.aargs = aargs;
    }

    override isSimpleStatement(): boolean {
        return true;
    }
}

//
//TODO: lots more statement types here
//

class IRReturnVoidSimpleStatement extends IRReturnSimpleStatement {
    constructor() {
        super(IRStatementTag.IRReturnVoidSimpleStatement);
    }
}

class IRReturnValueSimpleStatement extends IRReturnSimpleStatement {
    readonly retexp: IRSimpleExpression;

    constructor(retexp: IRSimpleExpression) {
        super(IRStatementTag.IRReturnValueSimpleStatement);
        this.retexp = retexp;
    }
}

class IRReturnDirectInvokeStatement extends IRReturnSimpleStatement {
    readonly retexp: IRInvokeDirectExpression;

    constructor(retexp: IRInvokeDirectExpression) {
        super(IRStatementTag.IRReturnDirectInvokeStatement);
        this.retexp = retexp;
    }
}

class IRReturnDirectConstructStatement extends IRReturnSimpleStatement {
    readonly retexp: IRConstructExpression;

    constructor(retexp: IRConstructExpression) {
        super(IRStatementTag.IRReturnDirectConstructStatement);
        this.retexp = retexp;
    }
}

class IRReturnDirectConstructWithBoxStatement extends IRReturnSimpleStatement {
    readonly retexp: IRConstructExpression;
    readonly fromtype: IRTypeSignature;
    readonly totype: IRTypeSignature;

    constructor(retexp: IRConstructExpression, fromtype: IRTypeSignature, totype: IRTypeSignature) {
        super(IRStatementTag.IRReturnDirectConstructWithBoxStatement);
        this.retexp = retexp;
        this.fromtype = fromtype;
        this.totype = totype;
    }
}

class IRReturnVoidWithImplicitStatement extends IRReturnWithImplicitStatement {
    constructor(implicitvar: string) {
        super(IRStatementTag.IRReturnVoidImplicitStatement, implicitvar);
    }
}

class IRReturnValueImplicitStatement extends IRReturnWithImplicitStatement {
    readonly retexp: IRSimpleExpression;

    constructor(retexp: IRSimpleExpression, implicitvar: string) {
        super(IRStatementTag.IRReturnValueImplicitStatement, implicitvar);
        this.retexp = retexp;
    }
}

class IRReturnDirectInvokeImplicitStatement extends IRReturnWithImplicitStatement {
    readonly retexp: IRInvokeDirectExpression;

    constructor(retexp: IRInvokeDirectExpression, implicitvar: string) {
        super(IRStatementTag.IRReturnDirectInvokeImplicitStatement, implicitvar);
        this.retexp = retexp;
    }
}

class IRReturnDirectInvokeImplicitPassThroughStatement extends IRReturnWithImplicitStatement {
    readonly retexp: IRInvokeImplicitsExpression;

    constructor(retexp: IRInvokeImplicitsExpression, implicitvar: string) {
        super(IRStatementTag.IRReturnDirectInvokeImplicitPassThroughStatement, implicitvar);
        this.retexp = retexp;
    }
}

class IRReturnDirectConstructImplicitStatement extends IRReturnWithImplicitStatement {
    readonly retexp: IRConstructExpression;

    constructor(retexp: IRConstructExpression, implicitvar: string) {
        super(IRStatementTag.IRReturnDirectConstructImplicitStatement, implicitvar);
        this.retexp = retexp;
    }
}

class IRReturnDirectConstructWithBoxImplicitStatement extends IRReturnWithImplicitStatement {
    readonly retexp: IRConstructExpression;
    readonly fromtype: IRTypeSignature;
    readonly totype: IRTypeSignature;

    constructor(retexp: IRConstructExpression, fromtype: IRTypeSignature, totype: IRTypeSignature, implicitvar: string) {
        super(IRStatementTag.IRReturnDirectConstructWithBoxImplicitStatement, implicitvar);
        this.retexp = retexp;
        this.fromtype = fromtype;
        this.totype = totype;
    }
}

class IRVoidInvokeStatement extends IRAtomicStatement {
    readonly scratchname: string; //a scratch temp variable to hold the direct invoke result if needed -- e.g. in SMT place result here, check for errors, then extract to vname
    readonly aexp: IRInvokeImplicitsExpression;

    constructor(scratch: string, aexp: IRInvokeImplicitsExpression) {
        super(IRStatementTag.IRVoidInvokeStatement);
        this.scratchname = scratch;
        this.aexp = aexp;
    }

    override isSimpleStatement(): boolean {
        return false;
    }
}

class IRChkLogicImpliesShortCircuitStatement extends IRStatement {
    readonly tvar: string; //the temp variable to hold the result
    readonly lhs: IRSimpleExpression;
    readonly rstmts: IRStatement[];
    readonly rexp: IRSimpleExpression;

    constructor(tvar: string, lhs: IRSimpleExpression, rstmts: IRStatement[], rexp: IRSimpleExpression) {
        super(IRStatementTag.IRChkLogicImpliesShortCircuitStatement);
        this.tvar = tvar;
        this.lhs = lhs;
        this.rstmts = rstmts;
        this.rexp = rexp;
    }

    override isSimpleStatement(): boolean {
        return this.lhs.isSimpleExpression() && this.rstmts.every(s => s.isSimpleStatement()) && this.rexp.isSimpleExpression();
    }
}

class IRLogicConditionalStatement extends IRStatement {
    readonly tvar: string; //the temp variable to hold the result
    readonly ttype: IRTypeSignature;
    readonly condition: IRSimpleExpression;
    readonly truestmt: IRStatement[];
    readonly trueexp: IRSimpleExpression;
    readonly falsestmt: IRStatement[];
    readonly falseexp: IRSimpleExpression;

    constructor(tvar: string, ttype: IRTypeSignature, condition: IRSimpleExpression, truestmt: IRStatement[], trueexp: IRSimpleExpression, falsestmt: IRStatement[], falseexp: IRSimpleExpression) {
        super(IRStatementTag.IRLogicConditionalStatement);
        this.tvar = tvar;
        this.ttype = ttype;
        this.condition = condition;
        this.truestmt = truestmt;
        this.trueexp = trueexp;
        this.falsestmt = falsestmt;
        this.falseexp = falseexp;
    }

    override isSimpleStatement(): boolean {
        return this.condition.isSimpleExpression() && this.truestmt.every(s => s.isSimpleStatement()) && this.trueexp.isSimpleExpression() && this.falsestmt.every(s => s.isSimpleStatement()) && this.falseexp.isSimpleExpression();
    }
}

class IRSimpleIfStatement extends IRStatement {
    readonly cond: IRSimpleExpression;
    readonly tblock: IRBlockStatement;

    constructor(cond: IRSimpleExpression, tblock: IRBlockStatement) {
        super(IRStatementTag.IRSimpleIfStatement);
        this.cond = cond;
        this.tblock = tblock;
    }

    override isSimpleStatement(): boolean {
        return this.cond.isSimpleExpression() && this.tblock.isSimpleStatement();
    }
}

class IRSimpleIfElseStatement extends IRStatement {
    readonly cond: IRSimpleExpression;
    readonly tblock: IRBlockStatement;
    readonly eblock: IRBlockStatement;

    constructor(cond: IRSimpleExpression, tblock: IRBlockStatement, eblock: IRBlockStatement) {
        super(IRStatementTag.IRSimpleIfElseStatement);
        this.cond = cond;
        this.tblock = tblock;
        this.eblock = eblock;
    }

    override isTerminalStatement(): boolean { 
        return this.tblock.isTerminalStatement() && this.eblock.isTerminalStatement(); 
    }

    override isSimpleStatement(): boolean {
        return this.cond.isSimpleExpression() && this.tblock.isSimpleStatement() && this.eblock.isSimpleStatement();
    }
}

class IRMatchExactStatement extends IRStatement {
    readonly sval: IRImmediateExpression;
    readonly svaltype: IRTypeSignature;
    readonly bindervar: string;
    readonly matchflow: {mtype: IRTypeSignature | undefined, value: IRBlockStatement}[];
    implicitFinalType: IRTypeSignature;

    constructor(sval: IRImmediateExpression, svaltype: IRTypeSignature, bindername: string, flow: {mtype: IRTypeSignature | undefined, value: IRBlockStatement}[], implicitFinalType: IRTypeSignature) {
        super(IRStatementTag.IRMatchExactStatement);
        this.sval = sval;
        this.svaltype = svaltype;
        this.bindervar = bindername;
        this.matchflow = flow;
        this.implicitFinalType = implicitFinalType;
    }

    override isTerminalStatement(): boolean { 
        return this.matchflow.every(f => f.value.isTerminalStatement()); 
    }

    override isSimpleStatement(): boolean {
        return this.sval.isSimpleExpression() && this.matchflow.every(f => f.value.isSimpleStatement());
    }
}

class IRMatchGeneralStatement extends IRStatement {
    readonly sval: IRImmediateExpression;
    readonly svaltype: IRTypeSignature;
    readonly bindervar: string;
    readonly matchflow: {mtype: IRTypeSignature | undefined, value: IRBlockStatement}[];
    implicitFinalType: IRTypeSignature;

    constructor(sval: IRImmediateExpression, svaltype: IRTypeSignature, bindername: string, flow: {mtype: IRTypeSignature | undefined, value: IRBlockStatement}[], implicitFinalType: IRTypeSignature) {
        super(IRStatementTag.IRMatchGeneralStatement);
        this.sval = sval;
        this.svaltype = svaltype;
        this.bindervar = bindername;
        this.matchflow = flow;
        this.implicitFinalType = implicitFinalType;
    }

    override isTerminalStatement(): boolean { 
        return this.matchflow.every(f => f.value.isTerminalStatement()); 
    }

    override isSimpleStatement(): boolean {
        return this.sval.isSimpleExpression() && this.matchflow.every(f => f.value.isSimpleStatement());
    }
}

class IRErrorAdditionBoundsCheckStatement extends IRErrorBinArithCheckStatement {
    constructor(file: string, sinfo: IRSourceInfo, checkID: number, left: IRImmediateExpression, right: IRImmediateExpression, optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float") {
        super(IRStatementTag.IRErrorAdditionBoundsCheckStatement, file, sinfo, undefined, checkID, left, right, optypechk);
    }
}

class IRErrorSubtractionBoundsCheckStatement extends IRErrorBinArithCheckStatement {
    constructor(file: string, sinfo: IRSourceInfo, checkID: number, left: IRImmediateExpression, right: IRImmediateExpression, optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float") {
        super(IRStatementTag.IRErrorSubtractionBoundsCheckStatement, file, sinfo, undefined, checkID, left, right, optypechk);
    }
}

class IRErrorMultiplicationBoundsCheckStatement extends IRErrorBinArithCheckStatement {
    constructor(file: string, sinfo: IRSourceInfo, checkID: number, left: IRImmediateExpression, right: IRImmediateExpression, optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float") {
        super(IRStatementTag.IRErrorMultiplicationBoundsCheckStatement, file, sinfo, undefined, checkID, left, right, optypechk);
    }
}

class IRErrorDivisionByZeroCheckStatement extends IRErrorBinArithCheckStatement {
    constructor(file: string, sinfo: IRSourceInfo, checkID: number, left: IRImmediateExpression, right: IRImmediateExpression, optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float") {
        super(IRStatementTag.IRErrorDivisionByZeroCheckStatement, file, sinfo, undefined, checkID, left, right, optypechk);
    }
}

class IRErrorTypeAssertionCheckStatement extends IRErrorCheckStatement {
    readonly typeok: IRSimpleExpression;

    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, typeok: IRSimpleExpression) {
        super(IRStatementTag.IRErrorTypeAssertionCheckStatement, file, sinfo, diagnosticTag, checkID);
        this.typeok = typeok;
    }
}

class IRErrorExhaustiveStatement extends IRErrorCheckStatement {
    constructor(file: string, sinfo: IRSourceInfo, checkID: number) {
        super(IRStatementTag.IRErrorExhaustiveStatement, file, sinfo, undefined, checkID);
    }

    override isTerminalStatement(): boolean { return true; }
}

class IRTypeDeclSizeRangeCheckCStringStatement extends IRErrorTypedStringCheckStatement {
    readonly min: string | undefined;
    readonly max: string | undefined;

    constructor(file: string, sinfo: IRSourceInfo, checkID: number, min: string | undefined, max: string | undefined, strexp: IRImmediateExpression) {
        super(IRStatementTag.IRTypeDeclSizeRangeCheckCStringStatement, file, sinfo, undefined, checkID, strexp);
        this.min = min;
        this.max = max;
    }
}

class IRTypeDeclSizeRangeCheckUnicodeStringStatement extends IRErrorTypedStringCheckStatement {
    readonly min: string | undefined;
    readonly max: string | undefined;

    constructor(file: string, sinfo: IRSourceInfo, checkID: number, min: string | undefined, max: string | undefined, strexp: IRImmediateExpression) {
        super(IRStatementTag.IRTypeDeclSizeRangeCheckUnicodeStringStatement, file, sinfo, undefined, checkID, strexp);
        this.min = min;
        this.max = max;
    }
}

class IRTypeDeclNumericRangeCheckStatement extends IRErrorCheckStatement {
    readonly min: string | undefined;
    readonly max: string | undefined;
    readonly numexp: IRImmediateExpression;

    constructor(file: string, sinfo: IRSourceInfo, checkID: number, min: string | undefined, max: string | undefined, numexp: IRImmediateExpression) {
        super(IRStatementTag.IRTypeDeclNumericRangeCheckStatement, file, sinfo, undefined, checkID);
        this.min = min;
        this.max = max;
        this.numexp = numexp;
    }
}

class IRTypeDeclFormatCheckCStringStatement extends IRErrorTypedStringCheckStatement {
    readonly re: IRLiteralCRegexExpression;

    constructor(file: string, sinfo: IRSourceInfo, checkID: number, re: IRLiteralCRegexExpression, strexp: IRImmediateExpression) {
        super(IRStatementTag.IRTypeDeclFormatCheckCStringStatement, file, sinfo, undefined, checkID, strexp);
        this.re = re;
    }
}

class IRTypeDeclFormatCheckUnicodeStringStatement extends IRErrorTypedStringCheckStatement {
    readonly re: IRLiteralUnicodeRegexExpression;

    constructor(file: string, sinfo: IRSourceInfo, checkID: number, re: IRLiteralUnicodeRegexExpression, strexp: IRImmediateExpression) {
        super(IRStatementTag.IRTypeDeclFormatCheckUnicodeStringStatement, file, sinfo, undefined, checkID, strexp);
        this.re = re;
    }
}

/* This calls the defined invariant check function for the target type decl on the provided value -- errors are reported from there */
class IRTypeDeclInvariantCheckStatement extends IRErrorCheckStatement {
    readonly tkey: string;
    readonly invariantidx: number;
    readonly targetValue: IRImmediateExpression;

    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, tkey: string, invariantidx: number, targetValue: IRImmediateExpression) {
        super(IRStatementTag.IRTypeDeclInvariantCheckStatement, file, sinfo, diagnosticTag, checkID);
        this.tkey = tkey;
        this.invariantidx = invariantidx;
        this.targetValue = targetValue;
    }
}

class IREntityInvariantCheckStatement extends IRErrorCheckStatement {
    readonly tkey: string
    readonly invariantidx: number;
    readonly args: IRImmediateExpression[];

    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, tkey: string, invariantidx: number, args: IRImmediateExpression[]) {
        super(IRStatementTag.IREntityInvariantCheckStatement, file, sinfo, diagnosticTag, checkID);
        this.tkey = tkey;
        this.invariantidx = invariantidx;
        this.args = args;
    }
}

/* This asserts that the given precondition expression is true */
class IRPreconditionCheckStatement extends IRErrorCheckStatement {
    readonly ikey: string;
    readonly requiresidx: number;
    readonly args: IRImmediateExpression[];

    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, ikey: string, requiresidx: number, args: IRImmediateExpression[]) {
        super(IRStatementTag.IRPreconditionCheckStatement, file, sinfo, diagnosticTag, checkID);
        this.ikey = ikey;
        this.requiresidx = requiresidx;
        this.args = args;
    }
}

/* This asserts that the given postcondition expresssion is true */
class IRPostconditionCheckStatement extends IRErrorCheckStatement {
    readonly ikey: string;
    readonly ensuresidx: number;
    readonly args: IRImmediateExpression[];

    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, ikey: string, ensuresidx: number, args: IRImmediateExpression[]) {
        super(IRStatementTag.IRPostconditionCheckStatement, file, sinfo, diagnosticTag, checkID);
        this.ikey = ikey;
        this.ensuresidx = ensuresidx;
        this.args = args;
    }
}

class IRAbortStatement extends IRErrorCheckStatement {
    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number) {
        super(IRStatementTag.IRAbortStatement, file, sinfo, diagnosticTag, checkID);
    }

    override isTerminalStatement(): boolean { return true; }
}

class IRAssertStatement extends IRErrorCheckStatement {
    readonly cond: IRSimpleExpression;

    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, cond: IRSimpleExpression) {
        super(IRStatementTag.IRAssertStatement, file, sinfo, diagnosticTag, checkID);
        this.cond = cond;
    }
}

class IRAssumeStatement extends IRErrorCheckStatement {
    readonly cond: IRSimpleExpression;

    constructor(file: string, sinfo: IRSourceInfo, cond: IRSimpleExpression) {
        super(IRStatementTag.IRAssumeStatement, file, sinfo, undefined, IRErrorCheckStatement.assumeCheckID);
        this.cond = cond;
    }
}

class IRValidateStatement extends IRErrorCheckStatement {
    readonly cond: IRSimpleExpression;

    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, cond: IRSimpleExpression) {
        super(IRStatementTag.IRValidateStatement, file, sinfo, diagnosticTag, checkID);
        this.cond = cond;
    }
}

class IRDebugStatement extends IRAtomicStatement {
    readonly oftype: IRTypeSignature;
    readonly dbgexp: IRSimpleExpression;

    readonly file: string;
    readonly line: number;

    constructor(oftype: IRTypeSignature, dbgexp: IRSimpleExpression, file: string, sinfo: IRSourceInfo) {
        super(IRStatementTag.IRDebugStatement);
        this.oftype = oftype;
        this.dbgexp = dbgexp;

        this.file = file;
        this.line = sinfo.line;
    }

    override isSimpleStatement(): boolean {
        return this.dbgexp.isSimpleExpression();
    }
}

class IRBlockStatement extends IRStatement {
    readonly statements: IRStatement[];

    constructor(statements: IRStatement[]) {
        super(IRStatementTag.IRBlockStatement);
        this.statements = statements;
    }

    override isTerminalStatement(): boolean { 
        return this.statements.length > 0 && this.statements[this.statements.length - 1].isTerminalStatement(); 
    }

    override isSimpleStatement(): boolean {
        return this.statements.every(s => s.isSimpleStatement());
    }
}

abstract class IRBody {
    constructor() {
    }

    abstract isSimpleBody(): boolean;
}

class IRBuiltinBody extends IRBody {
    readonly builtin: string;
    readonly biterms: [string, IRTypeSignature][];

    constructor(builtin: string, biterms: [string, IRTypeSignature][]) {
        super();
        this.builtin = builtin;
        this.biterms = biterms;
    }

    override isSimpleBody(): boolean {
        return false;
    }
}

class IRHoleBody extends IRBody {
    readonly hname: string | undefined;
    readonly doccomment: string | undefined;
    readonly samplesfile: string | undefined;
    
    constructor(hname: string | undefined, doccomment: string | undefined, samplesfile: string | undefined) {
        super();
        this.hname = hname;
        this.doccomment = doccomment;
        this.samplesfile = samplesfile;
    }

    override isSimpleBody(): boolean {
        return false;
    }
}

class IRStandardBody extends IRBody {
    readonly statements: IRStatement[];

    constructor(statements: IRStatement[]) {
        super();
        this.statements = statements;
    }

    override isSimpleBody(): boolean {
        return this.statements.every(s => s.isSimpleStatement());
    }
}

export {
    IRExpressionTag, IRExpression, IRLiteralExpression, IRImmediateExpression, IRSimpleExpression,
    
    IRLiteralNoneExpression, IRLiteralBoolExpression,
    IRLiteralIntegralNumberExpression, IRLiteralNatExpression, IRLiteralIntExpression, IRLiteralChkNatExpression, IRLiteralChkIntExpression,
    IRLiteralRationalExpression, IRLiteralFloatingPointExpression, IRLiteralFloatExpression, IRLiteralDecimalExpression,
    IRLiteralDecimalDegreeExpression, IRLiteralLatLongCoordinateExpression, IRLiteralComplexExpression,
    IRLiteralByteBufferExpression, 
    IRLiteralUUIDv4Expression, IRLiteralUUIDv7Expression, IRLiteralSHAContentHashExpression,
    IRDateRepresentation, IRTimeRepresentation, IRLiteralTZDateTimeExpression, IRLiteralTAITimeExpression, IRLiteralPlainDateExpression, IRLiteralPlainTimeExpression, IRLiteralLogicalTimeExpression, IRLiteralISOTimeStampExpression,
    IRDeltaDateRepresentation, IRDeltaTimeRepresentation, IRLiteralDeltaDateTimeExpression, IRLiteralDeltaISOTimeStampExpression, IRLiteralDeltaSecondsExpression, IRLiteralDeltaLogicalTimeExpression,
    IRLiteralUnicodeRegexExpression, IRLiteralCRegexExpression,
    IRLiteralByteExpression, IRLiteralCCharExpression, IRLiteralUnicodeCharExpression,
    IRLiteralCStringExpression, IRLiteralStringExpression,

    IRFormatStringComponent, IRFormatStringTextComponent, IRFormatStringArgComponent,
    IRLiteralFormatStringExpression, IRLiteralFormatCStringExpression,
    IRLiteralTypedExpression, IRLiteralTypedStringExpression, IRLiteralTypedCStringExpression,

    IRAccessEnvHasExpression, IRAccessEnvGetExpression, IRAccessEnvTryGetExpression,
    IRTaskAccessIDExpression, IRTaskAccessParentIDExpression,

    IRAccessConstantExpression, IRAccessEnumExpression,
    IRAccessParameterVariableExpression, IRAccessLocalVariableExpression, IRAccessCapturedVariableExpression, IRAccessTempVariableExpression,
    
    IRAccessTypeDeclValueExpression, IRConstructSafeTypeDeclExpression,

    IRConstructorSomeTypeExpression, IRConstructorOkTypeExpression, IRConstructorFailTypeExpression, IRConstructorMapEntryTypeExpression,

    IRConstructExpression,

    IRConstructorStandardEntityExpression,
    IRConstructorLambdaExpression,
    IRConstructorEListExpression,
    IRConstructorListEmptyExpression, IRConstructorListSingletonsExpression,
    IRConstructorMapEmptyExpression, IRConstructorMapSingletonsExpression,

    IRAccessFieldExpression, IRAccessFieldSpecialExpression, IRAccessFieldDirectExpression, IRAccessFieldVirtualExpression, IRAccessEListIndexExpression,

    IRInvokeExpression, IRInvokeDirectExpression, IRInvokeImplicitsExpression, IRInvokeSimpleExpression, IRInvokeSimpleWithImplicitsExpression, IRInvokeVirtualSimpleExpression, IRInvokeVirtualWithImplicitsExpression,

    IRInterpolateFormatCStringExpression, IRInterpolateFormatStringExpression,

    IRUnaryOpExpression, IRPrefixNotOpExpression, IRPrefixNegateOpExpression, IRPrefixPlusOpExpression,
    IRBinOpExpression, IRBinAddExpression, IRBinSubExpression, IRBinMultExpression, IRBinDivExpression,
    IRNumericComparisonExpression, IRNumericEqExpression, IRNumericNeqExpression, IRNumericLessExpression, IRNumericLessEqExpression, IRNumericGreaterExpression, IRNumericGreaterEqExpression,
    IRIsNoneOptionExpression, IRIsNotNoneOptionExpression, IRIsOptionEqValueExpression, IRIsOptionNeqValueExpression, IRIsSomeEqValueExpression, IRIsSomeNeqValueExpression,
    IRKeyComparisonExpression, IRBinKeyEqDirectExpression, IRBinKeyNeqDirectExpression, IRBinKeyLessDirectExpression,
    IRLogicOpExpression, IRLogicAndExpression, IRLogicOrExpression,

    IRLogicSimpleConditionalExpression,

    IRLiteralOptionOfNoneExpression, IRConstructOptionFromSomeExpression, IRExtractSomeFromOptionExpression, IRExtractSomeValueFromOptionExpression,
    IRConstructResultFromOkExpression, IRConstructResultFromFailExpression, IRExtractOkFromResultExpression, IRExtractOkValueFromResultExpression, IRExtractFailFromResultExpression, IRExtractFailValueFromResultExpression,
    IRConceptRepresentationOfTypeExpression, IRIsConceptRepresentationOfTypeExpression, IRIsNotConceptRepresentationOfTypeExpression, IRIsConceptRepresentationSubtypeOfTypeExpression, IRIsNotConceptRepresentationSubtypeOfTypeExpression, IRStaticIsTypeSubtypeOfExpression,
    IRBoxEntityToConceptRepresentationExpression, IRUnboxEntityFromConceptRepresentationExpression, IRConvertConceptRepresentationExpression,

    IRStatementTag, IRStatement, IRAtomicStatement, IRReturnSimpleStatement, IRReturnWithImplicitStatement,
    IRErrorCheckStatement, IRErrorBinArithCheckStatement,

    IRNopStatement,
    IRTempAssignExpressionStatement, IRTempAssignStdInvokeStatement, IRTempAssignRefInvokeStatement, IRTempAssignDirectConstructorStatement,

    IRVariableDeclarationStatement, 
    IRVariableInitializationStatement, IRVariableInitializationDirectInvokeStatement, IRVariableInitializationDirectInvokeWithImplicitStatement, IRVariableInitializationDirectConstructorStatement, IRVariableInitializationDirectConstructorWithBoxStatement,
    IRVariableAssignmentStatement, IRVariableAssignmentDirectInvokeStatement, IRVariableAssignmentDirectInvokeWithImplicitStatement, IRVariableAssignmentDirectConstructorStatement, IRVariableAssignmentDirectConstructorWithBoxStatement,
    
    IRUpdateLocalDirectStatement, IRUpdateParamDirectStatement,

    IRReturnVoidSimpleStatement, IRReturnValueSimpleStatement, IRReturnDirectInvokeStatement, IRReturnDirectConstructStatement, IRReturnDirectConstructWithBoxStatement,
    IRReturnVoidWithImplicitStatement, IRReturnValueImplicitStatement, IRReturnDirectInvokeImplicitStatement, IRReturnDirectInvokeImplicitPassThroughStatement, IRReturnDirectConstructImplicitStatement, IRReturnDirectConstructWithBoxImplicitStatement,
    
    IRVoidInvokeStatement,

    IRChkLogicImpliesShortCircuitStatement,
    IRLogicConditionalStatement,

    IRSimpleIfStatement, IRSimpleIfElseStatement,
    IRMatchExactStatement, IRMatchGeneralStatement,

    IRErrorAdditionBoundsCheckStatement, IRErrorSubtractionBoundsCheckStatement, IRErrorMultiplicationBoundsCheckStatement, IRErrorDivisionByZeroCheckStatement,
    IRErrorTypeAssertionCheckStatement, IRErrorExhaustiveStatement,
    IRErrorTypedStringCheckStatement, IRTypeDeclSizeRangeCheckCStringStatement, IRTypeDeclSizeRangeCheckUnicodeStringStatement, IRTypeDeclNumericRangeCheckStatement, IRTypeDeclFormatCheckCStringStatement, IRTypeDeclFormatCheckUnicodeStringStatement,

    IRTypeDeclInvariantCheckStatement, IREntityInvariantCheckStatement,
    IRPreconditionCheckStatement, IRPostconditionCheckStatement,
    IRAbortStatement, IRAssertStatement, IRAssumeStatement, IRValidateStatement, IRDebugStatement,

    IRBlockStatement,
    IRBody, IRBuiltinBody, IRHoleBody, IRStandardBody
};
