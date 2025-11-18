
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
    IRLiteralComplexExpression = "IRLiteralComplexExpression"
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

class IRStatement {
}

export {
    IRExpressionTag, IRExpression, IRLiteralNoneExpression, IRLiteralBoolExpression,
    IRLiteralIntegralNumberExpression, IRLiteralNatExpression, IRLiteralIntExpression, IRLiteralBigNatExpression, IRLiteralBigIntExpression,
    IRLiteralRationalExpression, IRLiteralFloatingPointExpression, IRLiteralFloatExpression, IRLiteralDecimalExpression,
    IRLiteralDecimalDegreeExpression, IRLiteralLatLongCoordinateExpression, IRLiteralComplexExpression,
    IRStatement
};
