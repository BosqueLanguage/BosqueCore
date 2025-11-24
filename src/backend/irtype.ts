

abstract class IRTypeSignature {
    readonly tkeystr: string;

    constructor(tkeystr: string) {
        this.tkeystr = tkeystr;
    }
}

class IRVoidTypeSignature extends IRTypeSignature {
    constructor() {
        super("Void");
    }
}

class IRNominalTypeSignature extends IRTypeSignature {
    constructor(tkeystr: string) {
        super(tkeystr);
    }
}

class IREListTypeSignature extends IRTypeSignature {
    readonly entries: IRTypeSignature[];

    constructor(tkeystr: string, entries: IRTypeSignature[]) {
        super(tkeystr);
        this.entries = entries;
    }
}

class IRDashResultTypeSignature extends IRTypeSignature {
    readonly entries: IRTypeSignature[];

    constructor(tkeystr: string, entries: IRTypeSignature[]) {
        super(tkeystr);
        this.entries = entries;
    }
}

abstract class IRFormatTypeSignature extends IRTypeSignature {
    readonly rtype: IRTypeSignature;
    readonly terms: {argname: string | undefined, argtype: IRTypeSignature}[];

    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string | undefined, argtype: IRTypeSignature}[]) {
        super(tkeystr);
        this.rtype = rtype;
        this.terms = terms;
    }
}

class IRFormatCStringTypeSignature extends IRFormatTypeSignature {
    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string | undefined, argtype: IRTypeSignature}[]) {
        super(tkeystr, rtype, terms);
    }
}

class IRFormatStringTypeSignature extends IRFormatTypeSignature {
    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string | undefined, argtype: IRTypeSignature}[]) {
        super(tkeystr, rtype, terms);
    }
}

class IRFormatPathTypeSignature extends IRFormatTypeSignature {
    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string | undefined, argtype: IRTypeSignature}[]) {
        super(tkeystr, rtype, terms);
    }
}

class IRFormatPathFragmentTypeSignature extends IRFormatTypeSignature {
    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string | undefined, argtype: IRTypeSignature}[]) {
        super(tkeystr, rtype, terms);
    }
}

class IRFormatPathGlobTypeSignature extends IRFormatTypeSignature {
    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string | undefined, argtype: IRTypeSignature}[]) {
        super(tkeystr, rtype, terms);
    }
}

class IRLambdaParameterPackTypeSignature extends IRTypeSignature {
    readonly stdvalues: {vname: string, vtype: IRTypeSignature}[];
    readonly lambdavalues: {lname: string, ltype: IRLambdaParameterPackTypeSignature}[];

    constructor(tkeystr: string, stdvalues: {vname: string, vtype: IRTypeSignature}[], lambdavalues: {lname: string, ltype: IRLambdaParameterPackTypeSignature}[]) {
        super(tkeystr);
        this.stdvalues = stdvalues;
        this.lambdavalues = lambdavalues;
    }
}

export {
    IRTypeSignature,
    IRVoidTypeSignature,
    IRNominalTypeSignature,
    IREListTypeSignature,
    IRDashResultTypeSignature,
    IRFormatTypeSignature,
    IRFormatCStringTypeSignature,
    IRFormatStringTypeSignature,
    IRFormatPathTypeSignature,
    IRFormatPathFragmentTypeSignature,
    IRFormatPathGlobTypeSignature,
    IRLambdaParameterPackTypeSignature
};
