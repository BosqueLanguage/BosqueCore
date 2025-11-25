import { SourceInfo } from "./irsupport";
import { IRTypeSignature } from "./irtype";

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
}

abstract class IRExpression {
    readonly tag: IRExpressionTag;

    constructor(tag: IRExpressionTag) {
        this.tag = tag;
    }
}

/* This class represents expressions that are guaranteed to be immediate values (i.e., vars, literals, constants) */
abstract class IRImmediateExpression extends IRExpression {
    constructor(tag: IRExpressionTag) {
        super(tag);
    }
}

/* This class represents expressions that are guaranteed to be immediate values (i.e., constants, typdecl literals) */
abstract class IRLiteralExpression extends IRExpression {
    constructor(tag: IRExpressionTag) {
        super(tag);
    }
}

enum IRStatementTag {
    IRNopStatement = "IRNopStatement",

    IRErrorAdditionBoundsCheckStatement = "IRErrorAdditionBoundsCheckStatement",
    IRErrorSubtractionBoundsCheckStatement = "IRErrorSubtractionBoundsCheckStatement",
    IRErrorMultiplicationBoundsCheckStatement = "IRErrorMultiplicationBoundsCheckStatement",
    IRErrorDivisionByZeroCheckStatement = "IRErrorDivisionByZeroCheckStatement",

    IRTypeDeclInvariantCheckStatement = "IRTypeDeclInvariantCheckStatement",
}

class IRStatement {
    readonly tag: IRStatementTag;

    constructor(tag: IRStatementTag) {
        this.tag = tag;
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

////////////////////////////////////////
//Basic Line statements

////////////////////////////////////////
//Explicit error condition checks -- all possible error conditions must be made explicit during flattening

class IRNopStatement extends IRStatement {
    constructor() {
        super(IRStatementTag.IRNopStatement);
    }
}

abstract class IRErrorCheckStatement extends IRStatement {
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
class IRTypeDeclInvariantCheckStatement  extends IRStatement {
    readonly targetType: IRTypeSignature;
    readonly targetValue: IRImmediateExpression;

    constructor(targetType: IRTypeSignature, targetValue: IRImmediateExpression) {
        super(IRStatementTag.IRTypeDeclInvariantCheckStatement);
        this.targetType = targetType;
        this.targetValue = targetValue;
    }
}

export {
    IRExpressionTag, IRExpression, IRImmediateExpression, IRLiteralExpression,
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

    IRStatementTag, IRStatement,
    IRNopStatement,
    IRErrorCheckStatement,
    IRErrorBinArithCheckStatement, IRErrorAdditionBoundsCheckStatement, IRErrorSubtractionBoundsCheckStatement, IRErrorMultiplicationBoundsCheckStatement, IRErrorDivisionByZeroCheckStatement,
    IRTypeDeclInvariantCheckStatement
};
