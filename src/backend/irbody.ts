
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
    IRLiteralDeltaLogicalExpression = "IRLiteralDeltaLogicalExpression"
}

class IRExpression {
    readonly tag: IRExpressionTag;

    constructor(tag: IRExpressionTag) {
        this.tag = tag;
    }
}

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

class IRLiteralDeltaLogicalExpression extends IRExpression {
    readonly sign: "+" | "-";
    readonly ticks: string;

    constructor(sign: "+" | "-", ticks: string) {
        super(IRExpressionTag.IRLiteralDeltaLogicalExpression);
        this.sign = sign;
        this.ticks = ticks;
    }
}

class IRStatement {
}

export {
    IRExpressionTag, IRExpression, IRLiteralNoneExpression, IRLiteralBoolExpression,
    IRLiteralIntegralNumberExpression, IRLiteralNatExpression, IRLiteralIntExpression, IRLiteralBigNatExpression, IRLiteralBigIntExpression,
    IRLiteralRationalExpression, IRLiteralFloatingPointExpression, IRLiteralFloatExpression, IRLiteralDecimalExpression,
    IRLiteralDecimalDegreeExpression, IRLiteralLatLongCoordinateExpression, IRLiteralComplexExpression,
    IRLiteralByteBufferExpression, 
    IRLiteralUUIDv4Expression, IRLiteralUUIDv7Expression, IRLiteralSHAContentHashExpression,
    DateRepresentation, TimeRepresentation, IRLiteralTZDateTimeExpression, IRLiteralTAITimeExpression, IRLiteralPlainDateExpression, IRLiteralPlainTimeExpression, IRLiteralLogicalTimeExpression, IRLiteralISOTimeStampExpression,
    DeltaDateRepresentation, DeltaTimeRepresentation, IRLiteralDeltaDateTimeExpression, IRLiteralDeltaISOTimeStampExpression, IRLiteralDeltaSecondsExpression, IRLiteralDeltaLogicalExpression,
    IRStatement
};
