
abstract class IRTypeSignature {
    readonly tkeystr: string;

    constructor(tkeystr: string) {
        this.tkeystr = tkeystr;
    }

    abstract getDirectDependencyTypes(): IRTypeSignature[];

    static jsonEmit_IRTypeSignature(tsig: IRTypeSignature): object {
        if(tsig instanceof IRVoidTypeSignature) {
            return ["Assembly::VoidTypeSignature", IRVoidTypeSignature.jsonEmit(tsig)];
        }
        else if(tsig instanceof IRNominalTypeSignature) {
            return ["Assembly::NominalTypeSignature", IRNominalTypeSignature.jsonEmit(tsig)];
        }
        else if(tsig instanceof IREListTypeSignature) {
            return ["Assembly::EListTypeSignature", IREListTypeSignature.jsonEmit(tsig)];
        }
        else if(tsig instanceof IRDashResultTypeSignature) {
            return ["Assembly::DashResultTypeSignature", IRDashResultTypeSignature.jsonEmit(tsig)];
        }
        else if(tsig instanceof IRFormatCStringTypeSignature) {
            return ["Assembly::FormatCStringTypeSignature", IRFormatCStringTypeSignature.jsonEmit(tsig)];
        }
        else if(tsig instanceof IRFormatStringTypeSignature) {
            return ["Assembly::FormatStringTypeSignature", IRFormatStringTypeSignature.jsonEmit(tsig)];
        }
        else if(tsig instanceof IRFormatPathTypeSignature) {
            return ["Assembly::FormatPathTypeSignature", IRFormatPathTypeSignature.jsonEmit(tsig)];
        }
        else if(tsig instanceof IRFormatPathFragmentTypeSignature) {
            return ["Assembly::FormatPathFragmentTypeSignature", IRFormatPathFragmentTypeSignature.jsonEmit(tsig)];
        }
        else if(tsig instanceof IRFormatPathGlobTypeSignature) {
            return ["Assembly::FormatPathGlobTypeSignature", IRFormatPathGlobTypeSignature.jsonEmit(tsig)];
        }
        else if(tsig instanceof IRLambdaParameterPackTypeSignature) {
            return ["Assembly::LambdaParameterPackTypeSignature", IRLambdaParameterPackTypeSignature.jsonEmit(tsig)];
        }
        else {
            throw new Error(`Unexpected IRTypeSignature instance ${tsig}`);
        }
    }

    static jsonParse_IRTypeSignature(obj: any): IRTypeSignature {
        const kind = (obj as any[])[0] as string;
        const data = (obj as any[])[1];

        if(kind === "Assembly::VoidTypeSignature") {
            return IRVoidTypeSignature.jsonParse(data);
        }
        else if(kind === "Assembly::NominalTypeSignature") {
            return IRNominalTypeSignature.jsonParse(data);
        }
        else if(kind === "Assembly::EListTypeSignature") {
            return IREListTypeSignature.jsonParse(data);
        }
        else if(kind === "Assembly::DashResultTypeSignature") {
            return IRDashResultTypeSignature.jsonParse(data);
        }
        else if(kind === "Assembly::FormatCStringTypeSignature") {
            return IRFormatCStringTypeSignature.jsonParse(data);
        }
        else if(kind === "Assembly::FormatStringTypeSignature") {
            return IRFormatStringTypeSignature.jsonParse(data);
        }
        else if(kind === "Assembly::FormatPathTypeSignature") {
            return IRFormatPathTypeSignature.jsonParse(data);
        }
        else if(kind === "Assembly::FormatPathFragmentTypeSignature") {
            return IRFormatPathFragmentTypeSignature.jsonParse(data);
        }
        else if(kind === "Assembly::FormatPathGlobTypeSignature") {
            return IRFormatPathGlobTypeSignature.jsonParse(data);
        }
        else if(kind === "Assembly::LambdaParameterPackTypeSignature") {
            return IRLambdaParameterPackTypeSignature.jsonParse(data);
        }
        else {
            throw new Error(`Unexpected TypeKey token value ${kind}`);
        }
    }
}

class IRVoidTypeSignature extends IRTypeSignature {
    constructor() {
        super("Void");
    }

    getDirectDependencyTypes(): IRTypeSignature[] {
        return [];
    }

    static jsonEmit(tsig: IRVoidTypeSignature): object {
        return { tkeystr: tsig.tkeystr };
    }

    static jsonParse(obj: any): IRVoidTypeSignature {
        return new IRVoidTypeSignature();
    }
}

class IRNominalTypeSignature extends IRTypeSignature {
    constructor(tkeystr: string) {
        super(tkeystr);
    }

    getDirectDependencyTypes(): IRTypeSignature[] {
        return [];
    }

    static jsonEmit(tsig: IRNominalTypeSignature): object {
        return { tkeystr: tsig.tkeystr };
    }

    static jsonParse(obj: any): IRNominalTypeSignature {
        return new IRNominalTypeSignature(obj.tkeystr);
    }
}

class IREListTypeSignature extends IRTypeSignature {
    readonly entries: IRTypeSignature[];

    constructor(tkeystr: string, entries: IRTypeSignature[]) {
        super(tkeystr);
        this.entries = entries;
    }

    getDirectDependencyTypes(): IRTypeSignature[] {
        return this.entries;
    }

    static jsonEmit(tsig: IREListTypeSignature): object {
        return { tkeystr: tsig.tkeystr, entries: tsig.entries.map(e => IRTypeSignature.jsonEmit_IRTypeSignature(e)) };
    }
    
    static jsonParse(obj: any): IREListTypeSignature {
        return new IREListTypeSignature(obj.tkeystr, obj.entries.map((e: any) => IRTypeSignature.jsonParse_IRTypeSignature(e)));
    }
}

class IRDashResultTypeSignature extends IRTypeSignature {
    readonly entries: IRTypeSignature[];

    constructor(tkeystr: string, entries: IRTypeSignature[]) {
        super(tkeystr);
        this.entries = entries;
    }

    getDirectDependencyTypes(): IRTypeSignature[] {
        return this.entries;
    }

    static jsonEmit(tsig: IRDashResultTypeSignature): object {
        return { tkeystr: tsig.tkeystr, entries: tsig.entries.map(e => IRTypeSignature.jsonEmit_IRTypeSignature(e)) };
    }

    static jsonParse(obj: any): IRDashResultTypeSignature {
        return new IRDashResultTypeSignature(obj.tkeystr, obj.entries.map((e: any) => IRTypeSignature.jsonParse_IRTypeSignature(e)));
    }
}

abstract class IRFormatTypeSignature extends IRTypeSignature {
    readonly rtype: IRTypeSignature;
    readonly terms: {argname: string, argtype: IRTypeSignature}[];

    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string, argtype: IRTypeSignature}[]) {
        super(tkeystr);
        this.rtype = rtype;
        this.terms = terms;
    }

    getDirectDependencyTypes(): IRTypeSignature[] {
        return [this.rtype, ...this.terms.map(t => t.argtype)];
    }

    static jsonEmit_IRFormatTypeSignature(tsig: IRFormatTypeSignature): object {
        const terms = tsig.terms.map(term => ({argname: term.argname, argtype: IRTypeSignature.jsonEmit_IRTypeSignature(term.argtype)})); 
        return { tkeystr: tsig.tkeystr, rtype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.rtype), terms: terms };
    }
    
    static jsonParse_IRFormatTypeSignature(obj: any): [string, IRTypeSignature, {argname: string, argtype: IRTypeSignature}[]] {
        const terms = obj.terms.map((t: any) => ({argname: t.argname, argtype: IRTypeSignature.jsonParse_IRTypeSignature(t.argtype)}));
        return [obj.tkeystr, IRTypeSignature.jsonParse_IRTypeSignature(obj.rtype), terms];
    }
}

class IRFormatCStringTypeSignature extends IRFormatTypeSignature {
    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string, argtype: IRTypeSignature}[]) {
        super(tkeystr, rtype, terms);
    }

    static jsonEmit(tsig: IRFormatCStringTypeSignature): object {
        return IRFormatTypeSignature.jsonEmit_IRFormatTypeSignature(tsig);
    }

    static jsonParse(obj: any): IRFormatCStringTypeSignature {
        return new IRFormatCStringTypeSignature(...IRFormatTypeSignature.jsonParse_IRFormatTypeSignature(obj));
    }
}

class IRFormatStringTypeSignature extends IRFormatTypeSignature {
    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string, argtype: IRTypeSignature}[]) {
        super(tkeystr, rtype, terms);
    }

    static jsonEmit(tsig: IRFormatStringTypeSignature): object {
        return IRFormatTypeSignature.jsonEmit_IRFormatTypeSignature(tsig);
    }

    static jsonParse(obj: any): IRFormatStringTypeSignature {
        return new IRFormatStringTypeSignature(...IRFormatTypeSignature.jsonParse_IRFormatTypeSignature(obj));
    }
}

class IRFormatPathTypeSignature extends IRFormatTypeSignature {
    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string, argtype: IRTypeSignature}[]) {
        super(tkeystr, rtype, terms);
    }

    static jsonEmit(tsig: IRFormatPathTypeSignature): object {
        return IRFormatTypeSignature.jsonEmit_IRFormatTypeSignature(tsig);
    }

    static jsonParse(obj: any): IRFormatPathTypeSignature {
        return new IRFormatPathTypeSignature(...IRFormatTypeSignature.jsonParse_IRFormatTypeSignature(obj));
    }
}

class IRFormatPathFragmentTypeSignature extends IRFormatTypeSignature {
    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string, argtype: IRTypeSignature}[]) {
        super(tkeystr, rtype, terms);
    }

    static jsonEmit(tsig: IRFormatPathFragmentTypeSignature): object {
        return IRFormatTypeSignature.jsonEmit_IRFormatTypeSignature(tsig);
    }

    static jsonParse(obj: any): IRFormatPathFragmentTypeSignature {
        return new IRFormatPathFragmentTypeSignature(...IRFormatTypeSignature.jsonParse_IRFormatTypeSignature(obj));
    }
}

class IRFormatPathGlobTypeSignature extends IRFormatTypeSignature {
    constructor(tkeystr: string, rtype: IRTypeSignature, terms: {argname: string, argtype: IRTypeSignature}[]) {
        super(tkeystr, rtype, terms);
    }

    static jsonEmit(tsig: IRFormatPathGlobTypeSignature): object {
        return IRFormatTypeSignature.jsonEmit_IRFormatTypeSignature(tsig);
    }

    static jsonParse(obj: any): IRFormatPathGlobTypeSignature {
        return new IRFormatPathGlobTypeSignature(...IRFormatTypeSignature.jsonParse_IRFormatTypeSignature(obj));
    }
}

class IRLambdaParameterPackTypeSignature extends IRTypeSignature {
    constructor(tkeystr: string) {
        super(tkeystr);
    }

    getDirectDependencyTypes(): IRTypeSignature[] {
        return [];
    }

    static jsonEmit(tsig: IRLambdaParameterPackTypeSignature): object {
        return { tkeystr: tsig.tkeystr };
    }

    static jsonParse(obj: any): IRLambdaParameterPackTypeSignature {
        return new IRLambdaParameterPackTypeSignature(obj.tkeystr);
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
