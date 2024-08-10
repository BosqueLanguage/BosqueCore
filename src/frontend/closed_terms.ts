import assert from "node:assert";

import { AbstractNominalTypeDecl, Assembly, InvokeParameterDecl, NamespaceDeclaration, NamespaceFunctionDecl, TypeFunctionDecl } from "./assembly.js";
import { NamespaceInstantiationInfo } from "./instantiation_map.js";
import { EListTypeSignature, LambdaTypeSignature, NominalTypeSignature, TemplateNameMapper, TypeSignature } from "./type.js";
import { ArgumentValue, Expression, ExpressionTag, LiteralNoneExpression, LiteralSimpleExpression } from "./body.js";

function computeTBindsKey(tbinds: TypeSignature[]): string {
    return (tbinds.length !== 0) ? `<${tbinds.map(t => t.toString()).join(", ")}>` : "";
}

class PendingNamespaceFunction {
    readonly namespace: NamespaceDeclaration;
    readonly function: NamespaceFunctionDecl;
    readonly instantiation: TypeSignature[];

    readonly fkey: string;

    constructor(namespace: NamespaceDeclaration, func: NamespaceFunctionDecl, instantiation: TypeSignature[]) {
        this.namespace = namespace;
        this.function = func;
        this.instantiation = instantiation;

        this.fkey = `${namespace.name}::${func.name}${computeTBindsKey(instantiation)}`;
    }
}

class PendingTypeFunction {
    readonly type: TypeSignature;
    readonly function: TypeFunctionDecl;
    readonly instantiation: TypeSignature[];

    readonly fkey: string;

    constructor(type: TypeSignature, func: TypeFunctionDecl, instantiation: TypeSignature[]) {
        this.type = type;
        this.function = func;
        this.instantiation = instantiation;

        this.fkey = `${type.tkeystr}::${func.name}${computeTBindsKey(instantiation)}`;
    }
}

class PendingTypeMethod {
    readonly type: TypeSignature;
    readonly function: TypeFunctionDecl;
    readonly instantiation: TypeSignature[];

    readonly mkey: string;

    constructor(type: TypeSignature, func: TypeFunctionDecl, instantiation: TypeSignature[]) {
        this.type = type;
        this.function = func;
        this.instantiation = instantiation;

        this.mkey = `${type.tkeystr}@${func.name}${computeTBindsKey(instantiation)}`;
    }
}

class PendingNominalTypeDecl {
    readonly type: AbstractNominalTypeDecl;
    readonly instantiation: TypeSignature[];

    readonly tkey: string;

    constructor(tkeystr: string, type: AbstractNominalTypeDecl, instantiation: TypeSignature[]) {
        this.type = type;
        this.instantiation = instantiation;

        this.tkey = tkeystr;
    }
}

class InstantiationPropagator {
    readonly assembly: Assembly;
    readonly instantiation: NamespaceInstantiationInfo[];

    readonly wellknowntypes: Map<string, TypeSignature>;

    readonly pendingNamespaceFunctions: PendingNamespaceFunction[] = [];
    readonly pendingTypeFunctions: PendingTypeFunction[] = [];
    readonly pendingTypeMethods: PendingTypeMethod[] = [];
    readonly pendingNominalTypeDecls: PendingNominalTypeDecl[] = [];

    currentMapping: TemplateNameMapper | undefined = undefined;
    currentNSInstantiation: NamespaceInstantiationInfo | undefined = undefined;

    constructor(assembly: Assembly, wellknowntypes: Map<string, TypeSignature>) {
        this.assembly = assembly;
        this.instantiation = [];

        this.wellknowntypes = wellknowntypes;
    }

    private getWellKnownType(name: string): TypeSignature {
        assert(this.wellknowntypes.has(name), `Well known type ${name} not found`);
        return this.wellknowntypes.get(name) as TypeSignature;
    }

    private isAlreadySeenType(tkey: string): boolean {
        const isdoneNominal = this.instantiation.some((ainfo) => ainfo.typebinds.has(tkey));
        if(isdoneNominal) {
            return true;
        }

        const isdoneEList = this.instantiation.some((ainfo) => ainfo.elists.has(tkey));
        if(isdoneEList) {
            return true;
        }

        return this.pendingNominalTypeDecls.some((pntd) => pntd.tkey === tkey);
    }

    //Given a type signature -- instantiate it and all sub-component types
    private instantiateTypeSignature(type: TypeSignature, mapping: TemplateNameMapper | undefined) {
        let rt = mapping !== undefined ? type.remapTemplateBindings(mapping) : type;
        if(this.isAlreadySeenType(rt.tkeystr)) {
            return;
        }

        if(rt instanceof NominalTypeSignature) {
            rt.alltermargs.forEach((tt) => this.instantiateTypeSignature(tt, mapping));
            this.pendingNominalTypeDecls.push(new PendingNominalTypeDecl(rt.tkeystr, rt.decl, rt.alltermargs));
        }
        else if(rt instanceof EListTypeSignature) {
            rt.entries.forEach((tt) => this.instantiateTypeSignature(tt, mapping));
            (this.currentNSInstantiation as NamespaceInstantiationInfo).elists.set(rt.tkeystr, rt);
        }
        else if(rt instanceof LambdaTypeSignature) {
            rt.params.forEach((param) => this.instantiateTypeSignature(param.type, mapping));
            this.instantiateTypeSignature(rt.resultType, mapping);
        }
        else {
            assert(false, "Unknown TypeSignature type");
        }
    }

    private instantiateArgumentList(args: ArgumentValue[]) {
        args.forEach((arg) => this.insantiateExpression(arg.exp));
    }

    private instantiateConstructorArgumentList(args: ArgumentValue[]) {
        args.forEach((arg) => this.insantiateExpression(arg.exp));
    }

    insantiateExpression(exp: Expression) {
        switch (exp.tag) {
            case ExpressionTag.LiteralNoneExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("None"), this.currentMapping);
            }
            case ExpressionTag.LiteralBoolExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("Bool"), this.currentMapping);
            }
            case ExpressionTag.LiteralNatExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("Nat"), this.currentMapping);
            }
            case ExpressionTag.LiteralIntExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("Int"), this.currentMapping);
            }
            case ExpressionTag.LiteralBigNatExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("BigNat"), this.currentMapping);
            }
            case ExpressionTag.LiteralBigIntExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("BigInt"), this.currentMapping);
            }
            case ExpressionTag.LiteralRationalExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("Rational"), this.currentMapping);
            }
            case ExpressionTag.LiteralFloatExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("Float"), this.currentMapping);
            }
            case ExpressionTag.LiteralDecimalExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("Decimal"), this.currentMapping);
            }
            case ExpressionTag.LiteralDecimalDegreeExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("DecimalDegree"), this.currentMapping);
            }
            case ExpressionTag.LiteralLatLongCoordinateExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("LatLongCoordinate"), this.currentMapping);
            }
            case ExpressionTag.LiteralComplexNumberExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("Complex"), this.currentMapping);
            }
            case ExpressionTag.LiteralByteBufferExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("ByteBuffer"), this.currentMapping);
            }
            case ExpressionTag.LiteralUUIDv4Expression: {
                this.instantiateTypeSignature(this.getWellKnownType("UUIDv4"), this.currentMapping);
            }
            case ExpressionTag.LiteralUUIDv7Expression: {
                this.instantiateTypeSignature(this.getWellKnownType("UUIDv7"), this.currentMapping);
            }
            case ExpressionTag.LiteralSHAContentHashExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("SHAContentHash"), this.currentMapping);
            }
            case ExpressionTag.LiteralDateTimeExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("DateTime"), this.currentMapping);
            }
            case ExpressionTag.LiteralUTCDateTimeExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("UTCDateTime"), this.currentMapping);
            }
            case ExpressionTag.LiteralPlainDateExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("PlainDate"), this.currentMapping);
            }
            case ExpressionTag.LiteralPlainTimeExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("PlainTime"), this.currentMapping);
            }
            case ExpressionTag.LiteralLogicalTimeExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("LogicalTime"), this.currentMapping);
            }
            case ExpressionTag.LiteralTickTimeExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("TickTime"), this.currentMapping);
            }
            case ExpressionTag.LiteralISOTimeStampExpression: {
                this.instantiateTypeSignature(this.getWellKnownType("ISOTimeStamp"), this.currentMapping);
            }
        }
    }

    static computeInstantiations(assembly: Assembly): AssemblyInstantiationInfo {

        xxxx;
    }
}

export { 
    InstantiationPropagator
};