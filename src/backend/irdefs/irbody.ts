import { SourceInfo } from "./irsupport";
import { IRNominalTypeSignature, IRTypeSignature } from "./irtype";

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

    IRLiteralTypedFormatStringExpression = "IRLiteralTypedFormatStringExpression",
    IRLiteralTypedFormatCStringExpression = "IRLiteralTypedFormatCStringExpression",

    //TODO: path typed literal and -format- options here

    IRAccessEnvHasExpression = "IRAccessEnvHasExpression",
    IRAccessEnvGetExpression = "IRAccessEnvGetExpression",
    IRAccessEnvTryGetExpression = "IRAccessEnvTryGetExpression",

    IRTaskAccessIDExpression = "IRTaskAccessIDExpression",
    IRTaskAccessParentIDExpression = "IRTaskAccessParentIDExpression",

    IRAccessNamespaceConstantExpression = "IRAccessNamespaceConstantExpression",
    IRAccessStaticFieldExpression = "IRAccessStaticFieldExpression",
    IRAccessEnumExpression = "IRAccessEnumExpression",

    IRAccessParameterVariableExpression = "IRAccessParameterVariableExpression",
    IRAccessLocalVariableExpression = "IRAccessLocalVariableExpression",
    IRAccessCapturedVariableExpression = "IRAccessCapturedVariableExpression",
    IRAccessTempVariableExpression = "IRAccessTempVariableExpression",

    IRAccessTypeDeclValueExpression = "IRAccessTypeDeclValueExpression",
    IRConstructSafeTypeDeclExpression = "IRConstructSafeTypeDeclExpression",
    
    //
    //TODO: lots more expression types here
    //

    IRPrefixNotOpExpression = "IRPrefixNotOpExpression",
    IRPrefixNegateOpExpression = "IRPrefixNegateOrPlusOpExpression",
    IRPrefixPlusOpExpression = "IRPrefixPlusOpExpression",

    IRBinAddExpression = "IRBinAddExpression",
    IRBinSubExpression = "IRBinSubExpression",
    IRBinMultExpression = "IRBinMultExpression",
    IRBinDivExpression = "IRBinDivExpression",

    //
    //TODO: lots more expression types here
    //

    IRNumericEqExpression = "IRNumericEqExpression",
    IRNumericNeqExpression = "IRNumericNeqExpression",
    IRNumericLessExpression = "IRNumericLessExpression",
    IRNumericLessEqExpression = "IRNumericLessEqExpression",
    IRNumericGreaterExpression = "IRNumericGreaterExpression",
    IRNumericGreaterEqExpression = "IRNumericGreaterEqExpression",

    IRLogicAndExpression = "IRLogicAndExpression",
    IRLogicOrExpression = "IRLogicOrExpression",

    //
    //TODO: lots more expression types here
    //
}

abstract class IRExpression {
    readonly tag: IRExpressionTag;

    constructor(tag: IRExpressionTag) {
        this.tag = tag;
    }
}

/* This class represents expressions that are simple and side-effect free (i.e., immediate expressions plus simple operations that we can put into expression trees) */
abstract class IRSimpleExpression extends IRExpression {
    constructor(tag: IRExpressionTag) {
        super(tag);
    }
}

/* This class represents expressions that are guaranteed to be immediate values (i.e., vars, literals, constants) */
abstract class IRImmediateExpression extends IRSimpleExpression {
    constructor(tag: IRExpressionTag) {
        super(tag);
    }
}

/* This class represents expressions that are guaranteed to be immediate values (i.e., constants, typdecl literals) */
abstract class IRLiteralExpression extends IRImmediateExpression {
    constructor(tag: IRExpressionTag) {
        super(tag);
    }
}

enum IRStatementTag {
    IRNopStatement = "IRNopStatement",

    IRTempAssignExpressionStatement = "IRTempAssignExpressionStatement",
    IRTempAssignStdInvokeStatement = "IRTempAssignStdInvokeStatement",
    IRTempAssignRefInvokeStatement = "IRTempAssignRefInvokeStatement",
    IRTempAssignConditionalStatement = "IRTempAssignConditionalStatement",

    IRVariableDeclarationStatement = "IRVariableDeclarationStatement",
    IRVariableInitializationStatement = "IRVariableInitializationStatement",

    //TODO: add initialization for ref/condition expression where the rhs is a temp variable

    IRReturnVoidSimpleStatement = "IRReturnVoidSimpleStatement",
    IRReturnValueSimpleStatement = "IRReturnValueSimpleStatement",

    IRChkLogicImpliesShortCircuitStatement = "IRChkLogicImpliesShortCircuitStatement",

    //TODO: lots more statement types here

    IRErrorAdditionBoundsCheckStatement = "IRErrorAdditionBoundsCheckStatement",
    IRErrorSubtractionBoundsCheckStatement = "IRErrorSubtractionBoundsCheckStatement",
    IRErrorMultiplicationBoundsCheckStatement = "IRErrorMultiplicationBoundsCheckStatement",
    IRErrorDivisionByZeroCheckStatement = "IRErrorDivisionByZeroCheckStatement",

    IRTypeDeclInvariantCheckStatement = "IRTypeDeclInvariantCheckStatement",
    IRPreconditionCheckStatement = "IRPreconditionCheckStatement",
    IRPostconditionCheckStatement = "IRPostconditionCheckStatement",

    IRAbortStatement = "IRAbortStatement",
    IRDebugStatement = "IRDebugStatement"
}

abstract class IRStatement {
    readonly tag: IRStatementTag;

    constructor(tag: IRStatementTag) {
        this.tag = tag;
    }
}

/* This class represents statements that are atomic (line statements) and don't have control flow or sub blocks */
abstract class IRAtomicStatement extends IRStatement {
    constructor(tag: IRStatementTag) {
        super(tag);
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
}

/* Represent return statement that do not involve any ref/out/out?/inout parameters */
abstract class IRReturnSimpleStatement extends IRAtomicStatement {
    constructor(tag: IRStatementTag) {
        super(tag);
    }
}

/* Represent return statement that involve ref/out/out?/inout parameters and thus have an implicit variable to hold the returned value */
abstract class IRReturnWithImplicitStatement extends IRAtomicStatement {
    readonly implicitvar: string;

    constructor(tag: IRStatementTag, implicitvar: string) {
        super(tag);
        this.implicitvar = implicitvar;
    }
}

/* Explicit error condition checks -- all possible error conditions must be made explicit during flattening */
abstract class IRErrorCheckStatement extends IRAtomicStatement {
    readonly file: string;
    readonly sinfo: SourceInfo;

    readonly diagnosticTag: string | undefined;
    readonly checkID: number;

    constructor(tag: IRStatementTag, file: string, sinfo: SourceInfo, diagnosticTag: string | undefined, checkID: number) {
        super(tag);
        this.file = file;
        this.sinfo = sinfo;
        this.diagnosticTag = diagnosticTag;
        this.checkID = checkID;
    }
}

abstract class IRErrorBinArithCheckStatement extends IRErrorCheckStatement {
    readonly left: IRImmediateExpression;
    readonly right: IRImmediateExpression;

    readonly optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt";

    constructor(tag: IRStatementTag, file: string, sinfo: SourceInfo, diagnosticTag: string | undefined, checkID: number, left: IRImmediateExpression, right: IRImmediateExpression, optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt") {
        super(tag, file, sinfo, diagnosticTag, checkID);
        this.left = left;
        this.right = right;
        this.optypechk = optypechk;
    }
}

////////////////////////////////////////
//Our literal expressions are all very safe and will never fail to construct -- if there are possible issues the flattening phase should have emitted and explicit check

class IRLiteralNoneExpression extends IRLiteralExpression {
    constructor() {
        super(IRExpressionTag.IRLiteralNoneExpression);
    }
}

class IRLiteralBoolExpression extends IRLiteralExpression {
    readonly value: boolean;

    constructor(value: boolean) {
        super(IRExpressionTag.IRLiteralBoolExpression);
        this.value = value;
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
}

class IRLiteralIntExpression extends IRLiteralIntegralNumberExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralIntExpression, value);
    }
}

class IRLiteralChkNatExpression extends IRLiteralIntegralNumberExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralChkNatExpression, value);
    }
}

class IRLiteralChkIntExpression extends IRLiteralIntegralNumberExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralChkIntExpression, value);
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
}
class IRLiteralDecimalExpression extends IRLiteralFloatingPointExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralDecimalExpression, value);
    }
}

class IRLiteralDecimalDegreeExpression extends IRLiteralFloatingPointExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralDecimalDegreeExpression, value);
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
}

class IRLiteralComplexExpression extends IRLiteralExpression {
    readonly real: string;
    readonly imaginary: string;

    constructor(real: string, imaginary: string) {
        super(IRExpressionTag.IRLiteralComplexExpression);
        this.real = real;
        this.imaginary = imaginary;
    }
}

class IRLiteralByteBufferExpression extends IRLiteralExpression {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralByteBufferExpression);
        this.bytes = bytes;
    }
}

class IRLiteralUUIDv4Expression extends IRLiteralExpression {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralUUIDv4Expression);
        this.bytes = bytes;
    }
}

class IRLiteralUUIDv7Expression extends IRLiteralExpression {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralUUIDv7Expression);
        this.bytes = bytes;
    }
}

class IRLiteralSHAContentHashExpression extends IRLiteralExpression {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralSHAContentHashExpression);
        this.bytes = bytes;
    }
}

class DateRepresentation {
    readonly year: number; //1900 to 2299
    readonly month: number;
    readonly day: number;

    constructor(year: number, month: number, day: number) {
        this.year = year;
        this.month = month;
        this.day = day;
    }
}

class TimeRepresentation {
    readonly hour: number;
    readonly minute: number;
    readonly second: number;

    constructor(hour: number, minute: number, second: number) {
        this.hour = hour;
        this.minute = minute;
        this.second = second;
    }
}

class IRLiteralTZDateTimeExpression extends IRLiteralExpression {
    readonly date: DateRepresentation;
    readonly time: TimeRepresentation;
    readonly timezone: string; //IANA timezone as well as freeform with printable ascii
    
    constructor(date: DateRepresentation, time: TimeRepresentation, timezone: string) {
        super(IRExpressionTag.IRLiteralTZDateTimeExpression);
        this.date = date;
        this.time = time;
        this.timezone = timezone;
    }
}

class IRLiteralTAITimeExpression extends IRLiteralExpression {
    readonly date: DateRepresentation;
    readonly time: TimeRepresentation;

    constructor(date: DateRepresentation, time: TimeRepresentation) {
        super(IRExpressionTag.IRLiteralTAITimeExpression);
        this.date = date;
        this.time = time;
    }
}

class IRLiteralPlainDateExpression extends IRLiteralExpression {
    readonly date: DateRepresentation;

    constructor(date: DateRepresentation) {
        super(IRExpressionTag.IRLiteralPlainDateExpression);
        this.date = date;
    }
}

class IRLiteralPlainTimeExpression extends IRLiteralExpression {
    readonly time: TimeRepresentation;

    constructor(time: TimeRepresentation) {
        super(IRExpressionTag.IRLiteralPlainTimeExpression);
        this.time = time;
    }
}

class IRLiteralLogicalTimeExpression extends IRLiteralExpression {
    readonly ticks: string;
    
    constructor(ticks: string) {
        super(IRExpressionTag.IRLiteralLogicalTimeExpression);
        this.ticks = ticks;
    }
}

class IRLiteralISOTimeStampExpression extends IRLiteralExpression {
    readonly date: DateRepresentation;
    readonly time: TimeRepresentation;
    readonly milliseconds: number;

    constructor(date: DateRepresentation, time: TimeRepresentation, milliseconds: number) {
        super(IRExpressionTag.IRLiteralISOTimeStampExpression);
        this.date = date;
        this.time = time;
        this.milliseconds = milliseconds;
    }
}

class DeltaDateRepresentation {
    readonly years: number;
    readonly months: number;
    readonly days: number;

    constructor(years: number, months: number, days: number) {
        this.years = years;
        this.months = months;
        this.days = days;
    }
}

class DeltaTimeRepresentation {
    readonly hours: number;
    readonly minutes: number;
    readonly seconds: number;

    constructor(hours: number, minutes: number, seconds: number) {
        this.hours = hours;
        this.minutes = minutes;
        this.seconds = seconds;
    }
}

class IRLiteralDeltaDateTimeExpression extends IRLiteralExpression {
    readonly sign: "+" | "-";
    readonly deltadate: DeltaDateRepresentation;
    readonly deltatime: DeltaTimeRepresentation;

    constructor(sign: "+" | "-", deltadate: DeltaDateRepresentation, deltatime: DeltaTimeRepresentation) {
        super(IRExpressionTag.IRLiteralDeltaDateTimeExpression);
        this.sign = sign;
        this.deltadate = deltadate;
        this.deltatime = deltatime;
    }
}
 
class IRLiteralDeltaISOTimeStampExpression extends IRLiteralExpression {
    readonly sign: "+" | "-";
    readonly deltadate: DeltaDateRepresentation;
    readonly deltatime: DeltaTimeRepresentation;
    readonly deltamilliseconds: BigInt;

    constructor(sign: "+" | "-", deltadate: DeltaDateRepresentation, deltatime: DeltaTimeRepresentation, deltamilliseconds: BigInt) {
        super(IRExpressionTag.IRLiteralDeltaISOTimeStampExpression);
        this.sign = sign;
        this.deltadate = deltadate;
        this.deltatime = deltatime;
        this.deltamilliseconds = deltamilliseconds;
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
}

class IRLiteralDeltaLogicalTimeExpression extends IRLiteralExpression {
    readonly sign: "+" | "-";
    readonly ticks: string;

    constructor(sign: "+" | "-", ticks: string) {
        super(IRExpressionTag.IRLiteralDeltaLogicalTimeExpression);
        this.sign = sign;
        this.ticks = ticks;
    }
}

class IRLiteralUnicodeRegexExpression extends IRLiteralExpression {
    readonly regexID: number
    readonly value: string;

    constructor(regexID: number, value: string) {
        super(IRExpressionTag.IRLiteralUnicodeRegexExpression);
        this.regexID = regexID;
        this.value = value;
    }
}

class IRLiteralCRegexExpression extends IRLiteralExpression {
    readonly regexID: number
    readonly value: string;

    constructor(regexID: number, value: string) {
        super(IRExpressionTag.IRLiteralCRegexExpression);
        this.regexID = regexID;
        this.value = value;
    }
}

class IRLiteralByteExpression extends IRLiteralExpression {
    readonly value: number;

    constructor(value: number) {
        super(IRExpressionTag.IRLiteralByteExpression);
        this.value = value;
    }
}

class IRLiteralCCharExpression extends IRLiteralExpression {
    readonly value: number;

    constructor(value: number) {
        super(IRExpressionTag.IRLiteralCCharExpression);
        this.value = value;
    }
}

class IRLiteralUnicodeCharExpression extends IRLiteralExpression {
    readonly value: number;

    constructor(value: number) {
        super(IRExpressionTag.IRLiteralUnicodeCharExpression);
        this.value = value;
    }
}

class IRLiteralCStringExpression extends IRLiteralExpression {
    readonly bytes: number[]; //char bytes

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralCStringExpression);
        this.bytes = bytes;
    }
}

class IRLiteralStringExpression extends IRLiteralExpression {
    readonly bytes: number[]; //utf8 bytes

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralStringExpression);
        this.bytes = bytes;
    }
}

abstract class IRFormatStringComponent {
}

class IRFormatStringTextComponent extends IRFormatStringComponent {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super();
        this.bytes = bytes;
    }
}

class IRFormatStringArgComponent extends IRFormatStringComponent {
    readonly argName: string;
    readonly argType: IRTypeSignature;

    constructor(argName: string, argType: IRTypeSignature) {
        super();
        this.argName = argName;
        this.argType = argType;
    }
}

class IRLiteralFormatStringExpression extends IRLiteralExpression {
    readonly fmts: IRFormatStringComponent[];

    constructor(fmts: IRFormatStringComponent[]) {
        super(IRExpressionTag.IRLiteralFormatStringExpression);
        this.fmts = fmts;
    }
}

class IRLiteralFormatCStringExpression extends IRLiteralExpression {
    readonly fmts: IRFormatStringComponent[];

    constructor(fmts: IRFormatStringComponent[]) {
        super(IRExpressionTag.IRLiteralFormatCStringExpression);
        this.fmts = fmts;
    }
}

//
//TODO: Path literal expressions here
//

//
//TODO: Path literal -format- expressions here
//

class IRLiteralTypedExpression extends IRLiteralExpression {
    readonly value: IRLiteralExpression;
    readonly constype: IRTypeSignature;

    constructor(value: IRLiteralExpression, constype: IRTypeSignature) {
        super(IRExpressionTag.IRLiteralTypedExpression);
        this.value = value;
        this.constype = constype;
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
}

class IRLiteralTypedCStringExpression extends IRLiteralExpression {
    readonly bytes: number[];
    readonly constype: IRTypeSignature;

    constructor(bytes: number[], constype: IRTypeSignature) {
        super(IRExpressionTag.IRLiteralTypedCStringExpression);
        this.bytes = bytes;
        this.constype = constype;
    }
}

class IRLiteralTypedFormatStringExpression extends IRLiteralExpression {
    readonly oftype: IRTypeSignature;
    readonly fmts: IRFormatStringComponent[];

    constructor(oftype: IRTypeSignature, fmts: IRFormatStringComponent[]) {
        super(IRExpressionTag.IRLiteralTypedFormatStringExpression);
        this.oftype = oftype;
        this.fmts = fmts;
    }
}

class IRLiteralTypedFormatCStringExpression extends IRLiteralExpression {
    readonly oftype: IRTypeSignature;
    readonly fmts: IRFormatStringComponent[];

    constructor(oftype: IRTypeSignature, fmts: IRFormatStringComponent[]) {
        super(IRExpressionTag.IRLiteralTypedFormatCStringExpression);
        this.oftype = oftype;
        this.fmts = fmts;
    }
}


//
//TODO: Path typed literal and -format- expressions here
//

class IRAccessEnvHasExpression extends IRExpression {
    readonly keybytes: number[];

    constructor(keybytes: number[]) {
        super(IRExpressionTag.IRAccessEnvHasExpression);
        this.keybytes = keybytes;
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
}

class IRTaskAccessIDExpression extends IRExpression {
    constructor() {
        super(IRExpressionTag.IRTaskAccessIDExpression);
    }
}

class IRTaskAccessParentIDExpression extends IRExpression {
    constructor() {
        super(IRExpressionTag.IRTaskAccessParentIDExpression);
    }
}

class IRAccessNamespaceConstantExpression extends IRImmediateExpression {
    readonly constkey: string; //flattened identifer names
    
    constructor(constkey: string) {
        super(IRExpressionTag.IRAccessNamespaceConstantExpression);
        this.constkey = constkey;
    }
}

class IRAccessStaticFieldExpression extends IRImmediateExpression {
    readonly constkey: string; //flattened identifer names

    constructor(constkey: string) {
        super(IRExpressionTag.IRAccessStaticFieldExpression);
        this.constkey = constkey;
    }
}

class IRAccessEnumExpression extends IRImmediateExpression {
    readonly enumkey: string; //flattened identifer names

    constructor(enumkey: string) {
        super(IRExpressionTag.IRAccessEnumExpression);
        this.enumkey = enumkey;
    }
}

class IRAccessParameterVariableExpression extends IRImmediateExpression {
    readonly pname: string;

    constructor(pname: string) {
        super(IRExpressionTag.IRAccessParameterVariableExpression);
        this.pname = pname;
    }
}

class IRAccessLocalVariableExpression extends IRImmediateExpression {
    readonly vname: string;

    constructor(vname: string) {
        super(IRExpressionTag.IRAccessLocalVariableExpression);
        this.vname = vname;
    }
}

class IRAccessCapturedVariableExpression extends IRImmediateExpression {
    readonly scope: number;
    readonly vname: string;

    constructor(scope: number, vname: string) {
        super(IRExpressionTag.IRAccessCapturedVariableExpression);
        this.scope = scope;
        this.vname = vname;
    }
}

class IRAccessTempVariableExpression extends IRImmediateExpression {
    readonly vname: string;

    constructor(vname: string) {
        super(IRExpressionTag.IRAccessTempVariableExpression);
        this.vname = vname;
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
}

class IRConstructSafeTypeDeclExpression extends IRSimpleExpression {
    readonly constype: IRNominalTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(constype: IRNominalTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRAccessTypeDeclValueExpression);
        this.constype = constype;
        this.value = value;
    }
}

//
//TODO: lots more expression types here
//

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

//
//TODO: lots more expression types here
//

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

//
//TODO: lots more expression types here
//

////////////////////////////////////////
//Basic Line statements

class IRNopStatement extends IRAtomicStatement {
    constructor() {
        super(IRStatementTag.IRNopStatement);
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
}

class IRTempAssignRefInvokeStatement extends IRTempAssignStatement {
}

class IRTempAssignConditionalStatement extends IRTempAssignStatement {
}

class IRVariableDeclarationStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;

    constructor(vname: string, vtype: IRTypeSignature) {
        super(IRStatementTag.IRVariableDeclarationStatement);
        this.vname = vname;
        this.vtype = vtype;
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

class IRChkLogicImpliesShortCircuitStatement extends IRStatement {
    readonly tvar: string; //the temp variable to hold the result
    readonly lhs: IRSimpleExpression;
    readonly rhs: IRBlockStatement;

    constructor(tvar: string, lhs: IRSimpleExpression, rhs: IRBlockStatement) {
        super(IRStatementTag.IRChkLogicImpliesShortCircuitStatement);
        this.tvar = tvar;
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class IRErrorAdditionBoundsCheckStatement extends IRErrorBinArithCheckStatement {
    constructor(file: string, sinfo: SourceInfo, checkID: number, left: IRImmediateExpression, right: IRImmediateExpression, optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt") {
        super(IRStatementTag.IRErrorAdditionBoundsCheckStatement, file, sinfo, undefined, checkID, left, right, optypechk);
    }
}

class IRErrorSubtractionBoundsCheckStatement extends IRErrorBinArithCheckStatement {
    constructor(file: string, sinfo: SourceInfo, checkID: number, left: IRImmediateExpression, right: IRImmediateExpression, optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt") {
        super(IRStatementTag.IRErrorSubtractionBoundsCheckStatement, file, sinfo, undefined, checkID, left, right, optypechk);
    }
}

class IRErrorMultiplicationBoundsCheckStatement extends IRErrorBinArithCheckStatement {
    constructor(file: string, sinfo: SourceInfo, checkID: number, left: IRImmediateExpression, right: IRImmediateExpression, optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt") {
        super(IRStatementTag.IRErrorMultiplicationBoundsCheckStatement, file, sinfo, undefined, checkID, left, right, optypechk);
    }
}

class IRErrorDivisionByZeroCheckStatement extends IRErrorBinArithCheckStatement {
    constructor(file: string, sinfo: SourceInfo, checkID: number, left: IRImmediateExpression, right: IRImmediateExpression, optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt") {
        super(IRStatementTag.IRErrorDivisionByZeroCheckStatement, file, sinfo, undefined, checkID, left, right, optypechk);
    }
}

/* This calls the defined invariant check function for the target type decl on the provided value -- errors are reported from there */
class IRTypeDeclInvariantCheckStatement extends IRErrorCheckStatement {
    readonly targetType: IRTypeSignature;
    readonly targetValue: IRImmediateExpression;

    constructor(file: string, sinfo: SourceInfo, diagnosticTag: string | undefined, checkID: number, targetType: IRTypeSignature, targetValue: IRImmediateExpression) {
        super(IRStatementTag.IRTypeDeclInvariantCheckStatement, file, sinfo, diagnosticTag, checkID);
        this.targetType = targetType;
        this.targetValue = targetValue;
    }
}

/* This asserts that the given precondition expression is true */
class IRPreconditionCheckStatement extends IRErrorCheckStatement {
    readonly cond: IRSimpleExpression;

    constructor(file: string, sinfo: SourceInfo, diagnosticTag: string | undefined, checkID: number, cond: IRSimpleExpression) {
        super(IRStatementTag.IRPreconditionCheckStatement, file, sinfo, diagnosticTag, checkID);
        this.cond = cond;
    }
}

/* This asserts that the given postcondition expresssion is true */
class IRPostconditionCheckStatement extends IRErrorCheckStatement {
    readonly cond: IRSimpleExpression;

    constructor(file: string, sinfo: SourceInfo, diagnosticTag: string | undefined, checkID: number, cond: IRSimpleExpression) {
        super(IRStatementTag.IRPostconditionCheckStatement, file, sinfo, diagnosticTag, checkID);
        this.cond = cond;
    }
}

class IRAbortStatement extends IRErrorCheckStatement {
    constructor(file: string, sinfo: SourceInfo, diagnosticTag: string | undefined, checkID: number) {
        super(IRStatementTag.IRAbortStatement, file, sinfo, diagnosticTag, checkID);
    }
}

class IRDebugStatement extends IRAtomicStatement {
    readonly oftype: IRTypeSignature;
    readonly dbgexp: IRAccessTempVariableExpression;

    readonly file: string;
    readonly line: number;

    constructor(oftype: IRTypeSignature, dbgexp: IRAccessTempVariableExpression, file: string, sinfo: SourceInfo) {
        super(IRStatementTag.IRDebugStatement);
        this.oftype = oftype;
        this.dbgexp = dbgexp;

        this.file = file;
        this.line = sinfo.line;
    }
}

class IRBlockStatement {
    readonly statements: IRStatement[];

    constructor(statements: IRStatement[]) {
        this.statements = statements;
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
    DateRepresentation, TimeRepresentation, IRLiteralTZDateTimeExpression, IRLiteralTAITimeExpression, IRLiteralPlainDateExpression, IRLiteralPlainTimeExpression, IRLiteralLogicalTimeExpression, IRLiteralISOTimeStampExpression,
    DeltaDateRepresentation, DeltaTimeRepresentation, IRLiteralDeltaDateTimeExpression, IRLiteralDeltaISOTimeStampExpression, IRLiteralDeltaSecondsExpression, IRLiteralDeltaLogicalTimeExpression,
    IRLiteralUnicodeRegexExpression, IRLiteralCRegexExpression,
    IRLiteralByteExpression, IRLiteralCCharExpression, IRLiteralUnicodeCharExpression,
    IRLiteralCStringExpression, IRLiteralStringExpression,

    IRFormatStringComponent, IRFormatStringTextComponent, IRFormatStringArgComponent,
    IRLiteralFormatStringExpression, IRLiteralFormatCStringExpression,
    IRLiteralTypedExpression, IRLiteralTypedStringExpression, IRLiteralTypedCStringExpression,
    IRLiteralTypedFormatStringExpression, IRLiteralTypedFormatCStringExpression,

    IRAccessEnvHasExpression, IRAccessEnvGetExpression, IRAccessEnvTryGetExpression,
    IRTaskAccessIDExpression, IRTaskAccessParentIDExpression,

    IRAccessNamespaceConstantExpression, IRAccessStaticFieldExpression, IRAccessEnumExpression,
    IRAccessParameterVariableExpression, IRAccessLocalVariableExpression, IRAccessCapturedVariableExpression, IRAccessTempVariableExpression,
    
    IRAccessTypeDeclValueExpression, IRConstructSafeTypeDeclExpression,

    IRUnaryOpExpression, IRPrefixNotOpExpression, IRPrefixNegateOpExpression, IRPrefixPlusOpExpression,
    IRBinOpExpression, IRBinAddExpression, IRBinSubExpression, IRBinMultExpression, IRBinDivExpression,
    IRNumericComparisonExpression, IRNumericEqExpression, IRNumericNeqExpression, IRNumericLessExpression, IRNumericLessEqExpression, IRNumericGreaterExpression, IRNumericGreaterEqExpression,
    IRLogicOpExpression, IRLogicAndExpression, IRLogicOrExpression,

    IRStatementTag, IRStatement, IRAtomicStatement, IRReturnSimpleStatement, IRReturnWithImplicitStatement,
    IRErrorCheckStatement, IRErrorBinArithCheckStatement,

    IRNopStatement,
    IRTempAssignExpressionStatement, IRTempAssignStdInvokeStatement, IRTempAssignRefInvokeStatement, IRTempAssignConditionalStatement,

    IRVariableDeclarationStatement, IRVariableInitializationStatement,
    
    IRReturnVoidSimpleStatement, IRReturnValueSimpleStatement,
    IRChkLogicImpliesShortCircuitStatement,

    IRErrorAdditionBoundsCheckStatement, IRErrorSubtractionBoundsCheckStatement, IRErrorMultiplicationBoundsCheckStatement, IRErrorDivisionByZeroCheckStatement,
    IRTypeDeclInvariantCheckStatement,
    IRPreconditionCheckStatement, IRPostconditionCheckStatement,
    IRAbortStatement, IRDebugStatement,

    IRBlockStatement
};
