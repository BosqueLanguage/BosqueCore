import { SourceInfo } from "./irsupport";

enum IRExpressionTag {
    IRLiteralNoneExpression = "IRLiteralNoneExpression",
    IRLiteralBoolExpression = "IRLiteralBoolExpression",
    
    IRLiteralNatExpression = "IRLiteralNatExpression",
    IRLiteralIntExpression = "IRLiteralIntExpression",
    IRLiteralBigNatExpression = "IRLiteralBigNatExpression",
    IRLiteralBigIntExpression = "IRLiteralBigIntExpression",
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


}

class IRExpression {
    readonly tag: IRExpressionTag;

    constructor(tag: IRExpressionTag) {
        this.tag = tag;
    }
}

enum IRStatementTag {
    IRErrorAdditionBoundsCheckStatement = "IRErrorAdditionBoundsCheckStatement",
    IRErrorSubtractionBoundsCheckStatement = "IRErrorSubtractionBoundsCheckStatement",
    IRErrorMultiplicationBoundsCheckStatement = "IRErrorMultiplicationBoundsCheckStatement",
    IRErrorDivisionByZeroCheckStatement = "IRErrorDivisionByZeroCheckStatement"
}

class IRStatement {
    readonly tag: IRStatementTag;

    constructor(tag: IRStatementTag) {
        this.tag = tag;
    }
}
////////////////////////////////////////
//Our literal expressions are all very safe and will never fail to construct -- if there are possible issues the flattening phase should have emitted and explicit check

class IRLiteralNoneExpression extends IRExpression {
    constructor() {
        super(IRExpressionTag.IRLiteralNoneExpression);
    }
}

class IRLiteralBoolExpression extends IRExpression {
    readonly value: boolean;

    constructor(value: boolean) {
        super(IRExpressionTag.IRLiteralBoolExpression);
        this.value = value;
    }
}

abstract class IRLiteralIntegralNumberExpression extends IRExpression {
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
class IRLiteralBigNatExpression extends IRLiteralIntegralNumberExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralBigNatExpression, value);
    }
}
class IRLiteralBigIntExpression extends IRLiteralIntegralNumberExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralBigIntExpression, value);
    }
}

class IRLiteralRationalExpression extends IRExpression {
    readonly numerator: string;
    readonly denominator: string;

    constructor(numerator: string, denominator: string) {
        super(IRExpressionTag.IRLiteralRationalExpression);
        this.numerator = numerator;
        this.denominator = denominator;
    }
}

abstract class IRLiteralFloatingPointExpression extends IRExpression {
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

class IRLiteralLatLongCoordinateExpression extends IRExpression {
    readonly latitude: string;
    readonly longitude: string;

    constructor(latitude: string, longitude: string) {
        super(IRExpressionTag.IRLiteralLatLongCoordinateExpression);
        this.latitude = latitude;
        this.longitude = longitude;
    }
}

class IRLiteralComplexExpression extends IRExpression {
    readonly real: string;
    readonly imaginary: string;

    constructor(real: string, imaginary: string) {
        super(IRExpressionTag.IRLiteralComplexExpression);
        this.real = real;
        this.imaginary = imaginary;
    }
}

class IRLiteralByteBufferExpression extends IRExpression {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralByteBufferExpression);
        this.bytes = bytes;
    }
}

class IRLiteralUUIDv4Expression extends IRExpression {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralUUIDv4Expression);
        this.bytes = bytes;
    }
}

class IRLiteralUUIDv7Expression extends IRExpression {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralUUIDv7Expression);
        this.bytes = bytes;
    }
}

class IRLiteralSHAContentHashExpression extends IRExpression {
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

class IRLiteralTZDateTimeExpression extends IRExpression {
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

class IRLiteralTAITimeExpression extends IRExpression {
    readonly date: DateRepresentation;
    readonly time: TimeRepresentation;

    constructor(date: DateRepresentation, time: TimeRepresentation) {
        super(IRExpressionTag.IRLiteralTAITimeExpression);
        this.date = date;
        this.time = time;
    }
}

class IRLiteralPlainDateExpression extends IRExpression {
    readonly date: DateRepresentation;

    constructor(date: DateRepresentation) {
        super(IRExpressionTag.IRLiteralPlainDateExpression);
        this.date = date;
    }
}

class IRLiteralPlainTimeExpression extends IRExpression {
    readonly time: TimeRepresentation;

    constructor(time: TimeRepresentation) {
        super(IRExpressionTag.IRLiteralPlainTimeExpression);
        this.time = time;
    }
}

class IRLiteralLogicalTimeExpression extends IRExpression {
    readonly ticks: string;
    
    constructor(ticks: string) {
        super(IRExpressionTag.IRLiteralLogicalTimeExpression);
        this.ticks = ticks;
    }
}

class IRLiteralISOTimeStampExpression extends IRExpression {
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

class IRLiteralDeltaDateTimeExpression extends IRExpression {
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
 
class IRLiteralDeltaISOTimeStampExpression extends IRExpression {
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

class IRLiteralDeltaSecondsExpression extends IRExpression {
    readonly sign: "+" | "-";
    readonly seconds: string;

    constructor(sign: "+" | "-", seconds: string) {
        super(IRExpressionTag.IRLiteralDeltaSecondsExpression);
        this.sign = sign;
        this.seconds = seconds;
    }
}

class IRLiteralDeltaLogicalTimeExpression extends IRExpression {
    readonly sign: "+" | "-";
    readonly ticks: string;

    constructor(sign: "+" | "-", ticks: string) {
        super(IRExpressionTag.IRLiteralDeltaLogicalTimeExpression);
        this.sign = sign;
        this.ticks = ticks;
    }
}

class IRLiteralUnicodeRegexExpression extends IRExpression {
    readonly regexID: number
    readonly value: string;

    constructor(regexID: number, value: string) {
        super(IRExpressionTag.IRLiteralUnicodeRegexExpression);
        this.regexID = regexID;
        this.value = value;
    }
}

class IRLiteralCRegexExpression extends IRExpression {
    readonly regexID: number
    readonly value: string;

    constructor(regexID: number, value: string) {
        super(IRExpressionTag.IRLiteralCRegexExpression);
        this.regexID = regexID;
        this.value = value;
    }
}

class IRLiteralByteExpression extends IRExpression {
    readonly value: number;

    constructor(value: number) {
        super(IRExpressionTag.IRLiteralByteExpression);
        this.value = value;
    }
}

class IRLiteralCCharExpression extends IRExpression {
    readonly value: number;

    constructor(value: number) {
        super(IRExpressionTag.IRLiteralCCharExpression);
        this.value = value;
    }
}

class IRLiteralUnicodeCharExpression extends IRExpression {
    readonly value: number;

    constructor(value: number) {
        super(IRExpressionTag.IRLiteralUnicodeCharExpression);
        this.value = value;
    }
}

class IRLiteralCStringExpression extends IRExpression {
    readonly srcstring: string; //source code string literal format
    readonly bytes: number[]; //char bytes

    constructor(srcstring: string, bytes: number[]) {
        super(IRExpressionTag.IRLiteralCStringExpression);
        this.srcstring = srcstring;
        this.bytes = bytes;
    }
}

class IRLiteralStringExpression extends IRExpression {
    readonly srcstring: string; //source code string literal format
    readonly bytes: number[]; //utf8 bytes

    constructor(srcstring: string, bytes: number[]) {
        super(IRExpressionTag.IRLiteralStringExpression);
        this.srcstring = srcstring;
        this.bytes = bytes;
    }
}

abstract class IRFormatStringComponent {
}

class IRFormatStringTextComponent extends IRFormatStringComponent {
    readonly srcstring: string; //source code string literal format
    readonly bytes: number[];

    constructor(srcstring: string, bytes: number[]) {
        super();
        this.srcstring = srcstring;
        this.bytes = bytes;
    }
}

class IRFormatStringArgComponent extends IRFormatStringComponent {
    readonly argPos: string; // number | name
    readonly argType: TypeSignature; //can be AutoTypeSignature, string, or typed string

    constructor(argPos: string, argType: TypeSignature) {
        super();
        this.argPos = argPos;
        this.argType = argType;
    }
}

class IRLiteralFormatStringExpression extends IRExpression {
    readonly fmts: IRFormatStringComponent[];

    constructor(value: string, fmts: IRFormatStringComponent[]) {
        super(IRExpressionTag.IRLiteralFormatStringExpression);
        this.fmts = fmts;
    }
}

class IRLiteralFormatCStringExpression extends IRExpression {
    readonly fmts: IRFormatStringComponent[];

    constructor(value: string, fmts: IRFormatStringComponent[]) {
        super(IRExpressionTag.IRLiteralFormatCStringExpression);
        this.fmts = fmts;
    }
}



////////////////////////////////////////
//Basic Line statements

////////////////////////////////////////
//Explicit error condition checks -- all possible error conditions must be made explicit during flattening

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
    readonly left: IRExpression;
    readonly right: IRExpression;

    readonly optypechk: "Nat" | "Int" | "BigNat" | "BigInt";

    constructor(tag: IRStatementTag, file: string, sinfo: SourceInfo, diagnosticTag: string | undefined, checkID: number, left: IRExpression, right: IRExpression, optypechk: "Nat" | "Int" | "BigNat" | "BigInt") {
        super(tag, file, sinfo, diagnosticTag, checkID);
        this.left = left;
        this.right = right;
        this.optypechk = optypechk;
    }
}

class IRErrorAdditionBoundsCheckStatement extends IRErrorBinArithCheckStatement {
    constructor(file: string, sinfo: SourceInfo, diagnosticTag: string | undefined, checkID: number, left: IRExpression, right: IRExpression, optypechk: "Nat" | "Int" | "BigNat" | "BigInt") {
        super(IRStatementTag.IRErrorAdditionBoundsCheckStatement, file, sinfo, diagnosticTag, checkID, left, right, optypechk);
    }
}

class IRErrorSubtractionBoundsCheckStatement extends IRErrorBinArithCheckStatement {
    constructor(file: string, sinfo: SourceInfo, diagnosticTag: string | undefined, checkID: number, left: IRExpression, right: IRExpression, optypechk: "Nat" | "Int" | "BigNat" | "BigInt") {
        super(IRStatementTag.IRErrorSubtractionBoundsCheckStatement, file, sinfo, diagnosticTag, checkID, left, right, optypechk);
    }
}

class IRErrorMultiplicationBoundsCheckStatement extends IRErrorBinArithCheckStatement {
    constructor(file: string, sinfo: SourceInfo, diagnosticTag: string | undefined, checkID: number, left: IRExpression, right: IRExpression, optypechk: "Nat" | "Int" | "BigNat" | "BigInt") {
        super(IRStatementTag.IRErrorMultiplicationBoundsCheckStatement, file, sinfo, diagnosticTag, checkID, left, right, optypechk);
    }
}

class IRErrorDivisionByZeroCheckStatement extends IRErrorBinArithCheckStatement {
    constructor(file: string, sinfo: SourceInfo, diagnosticTag: string | undefined, checkID: number, left: IRExpression, right: IRExpression, optypechk: "Nat" | "Int" | "BigNat" | "BigInt") {
        super(IRStatementTag.IRErrorDivisionByZeroCheckStatement, file, sinfo, diagnosticTag, checkID, left, right, optypechk);
    }
}

export {
    IRExpressionTag, IRExpression,
    IRLiteralNoneExpression, IRLiteralBoolExpression,
    IRLiteralIntegralNumberExpression, IRLiteralNatExpression, IRLiteralIntExpression, IRLiteralBigNatExpression, IRLiteralBigIntExpression,
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

    IRStatementTag, IRStatement,
    IRErrorCheckStatement,
    IRErrorBinArithCheckStatement, IRErrorAdditionBoundsCheckStatement, IRErrorSubtractionBoundsCheckStatement, IRErrorMultiplicationBoundsCheckStatement, IRErrorDivisionByZeroCheckStatement
};
