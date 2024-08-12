import assert from "node:assert";

import { AbstractNominalTypeDecl, Assembly, InvokeParameterDecl, NamespaceDeclaration, NamespaceFunctionDecl, TypeFunctionDecl } from "./assembly.js";
import { NamespaceInstantiationInfo } from "./instantiation_map.js";
import { EListTypeSignature, LambdaTypeSignature, NominalTypeSignature, TemplateNameMapper, TypeSignature } from "./type.js";
import { AccessEnumExpression, AccessEnvValueExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, ArgumentValue, CallNamespaceFunctionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, Expression, ExpressionTag, LambdaInvokeExpression, LetExpression, LiteralNoneExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralTypeDeclValueExpression, LogicActionAndExpression, LogicActionOrExpression, ParseAsTypeExpression, SpecialConstructorExpression, SpecialConverterExpression, TaskAccessInfoExpression } from "./body.js";

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


    private instantiateLiteralCRegexExpression(exp: LiteralRegexExpression) {
        this.instantiateTypeSignature(exp.value.endsWith("c") ? exp.setType(this.getWellKnownType("CRegex")) : exp.setType(this.getWellKnownType("PathRegex")), this.currentMapping);
    }

    private instantiateLiteralTypeDeclValueExpression(exp: LiteralTypeDeclValueExpression) {
        this.instantiateTypeSignature(exp.constype, this.currentMapping);
        this.insantiateExpression(exp.value);
    }
    
    private instantiateHasEnvValueExpression(exp: AccessEnvValueExpression) {
        assert(false, "Not Implemented -- instantiateHasEnvValueExpression");
    }
    
    private instantiateAccessEnvValueExpression(exp: AccessEnvValueExpression) {
        assert(false, "Not Implemented -- instantiateAccessEnvValueExpression");
    }

    private instantiateTaskAccessInfoExpression(exp: TaskAccessInfoExpression) {
        assert(false, "Not Implemented -- instantiateTaskAccessInfoExpression");
    }

    private instantiateAccessEnumExpression(exp: AccessEnumExpression) {
        assert(false, "Not Implemented -- instantiateAccessEnumExpression");
    }

    private instantiateAccessStaticFieldExpression(exp: AccessStaticFieldExpression) {
        assert(false, "Not Implemented -- instantiateAccessStaticFieldExpression");
    }

    private instantiateConstructorPrimaryExpression(exp: ConstructorPrimaryExpression) {
        this.instantiateTypeSignature(exp.ctype);

        if(!(exp.ctype instanceof NominalTypeSignature)) {
            this.reportError(exp.sinfo, `Invalid type for constructor expression -- ${exp.ctype}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const ctype = exp.ctype as NominalTypeSignature;
        const decl = ctype.decl;
        if(decl instanceof AbstractCollectionTypeDecl) {
            return this.instantiateCollectionConstructor(env, decl, exp);
        }
        else if(decl instanceof ConstructableTypeDecl) {
            return this.instantiateSpecialConstructableConstructor(env, decl, exp);
        }
        else {
            if(decl instanceof EntityTypeDecl) {
                return this.instantiateStandardConstructor(env, decl.fields, exp);
            }
            else if(decl instanceof DatatypeMemberEntityTypeDecl) {
                return this.instantiateStandardConstructor(env, decl.fields, exp);
            }
            else {
                this.reportError(exp.sinfo, `Invalid type for constructor expression -- ${exp.ctype}`);
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
        }
    }
    
    private instantiateConstructorEListExpression(exp: ConstructorEListExpression) {
        assert(false, "Not Implemented -- instantiateConstructorEListExpression");
    }

    private instantiateConstructorLambdaExpression(exp: ConstructorLambdaExpression) {
        assert(false, "Not Implemented -- instantiateConstructorLambdaExpression");
    }

    private instantiateLetExpression(exp: LetExpression) {
        assert(false, "Not Implemented -- instantiateLetExpression");
    }

    private instantiateLambdaInvokeExpression(exp: LambdaInvokeExpression) {
        assert(false, "Not Implemented -- instantiateLambdaInvokeExpression");
    }

    private instantiateSpecialConstructorExpression(exp: SpecialConstructorExpression) {
        if(infertype === undefined || !(infertype instanceof NominalTypeSignature)) {
            return this.instantiateSpecialConstructorExpressionNoInfer(env, exp);
        }
        else {
            const ninfer = infertype as NominalTypeSignature;
            if(exp.rop === "some") {
                if(ninfer.decl instanceof SomeTypeDecl) {
                    const ttype = ninfer.alltermargs[0];
                    const etype = this.instantiateExpression(env, exp.arg, ttype);
                    this.instantiateError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Some constructor argument is not a subtype of ${ttype.tkeystr}`);

                    return exp.setType(ninfer);
                }
                else if(ninfer.decl instanceof OptionTypeDecl) {
                    const ttype = ninfer.alltermargs[0];
                    const etype = this.instantiateExpression(env, exp.arg, ttype);
                    this.instantiateError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Some constructor argument is not a subtype of ${ttype.tkeystr}`);

                    return exp.setType(ninfer);
                }
                else {
                    return this.instantiateSpecialConstructorExpressionNoInfer(env, exp);
                }
            }
            else if(exp.rop === "ok") {
                if(ninfer.decl instanceof OkTypeDecl) {
                    const ttype = ninfer.alltermargs[0];
                    const etype = this.instantiateExpression(env, exp.arg, ttype);
                    this.instantiateError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Ok constructor argument is not a subtype of ${ttype.tkeystr}`);

                    return exp.setType(ninfer);
                }
                else if(ninfer.decl instanceof ResultTypeDecl) {
                    const ttype = ninfer.alltermargs[0];
                    const etype = this.instantiateExpression(env, exp.arg, ttype);
                    this.instantiateError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Ok constructor argument is not a subtype of ${ttype.tkeystr}`);

                    return exp.setType(ninfer);
                }
                else {
                    this.reportError(exp.sinfo, `Cannot infer type for special Ok constructor -- got ${infertype.tkeystr}`);
                    return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
                }
            }
            else {
                if(ninfer.decl instanceof ErrTypeDecl) {
                    const ttype = ninfer.alltermargs[1];
                    const etype = this.instantiateExpression(env, exp.arg, ttype);
                    this.instantiateError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Err constructor argument is not a subtype of ${ttype.tkeystr}`);

                    return exp.setType(ninfer);
                }
                else if(ninfer.decl instanceof ResultTypeDecl) {
                    const ttype = ninfer.alltermargs[1];
                    const etype = this.instantiateExpression(env, exp.arg, ttype);
                    this.instantiateError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Err constructor argument is not a subtype of ${ttype.tkeystr}`);

                    return exp.setType(ninfer);
                }
                else {
                    this.reportError(exp.sinfo, `Cannot infer type for special Err constructor -- got ${infertype.tkeystr}`);
                    return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
                }
            }
        }
    }

    private instantiateSpecialConverterExpression(exp: SpecialConverterExpression) {
        assert(false, "Not Implemented -- instantiateSpecialConverterExpression");
    }

    private instantiateCallNamespaceFunctionExpression(exp: CallNamespaceFunctionExpression) {
        this.instantiateTemplateBindingsOnInvoke(env, exp.terms, fdecl); 

        this.instantiateArgumentList(exp.args.args);

        xxxx;
    }

    private instantiateCallTypeFunctionExpression(exp: CallTypeFunctionExpression) {
        assert(false, "Not Implemented -- instantiateCallTypeFunctionExpression");
    }
    
    private instantiateLogicActionAndExpression(exp: LogicActionAndExpression) {
        assert(false, "Not Implemented -- instantiateLogicActionAndExpression");
    }

    private instantiateLogicActionOrExpression(exp: LogicActionOrExpression) {
        assert(false, "Not Implemented -- instantiateLogicActionOrExpression");
    }

    private instantiateParseAsTypeExpression(exp: ParseAsTypeExpression) {
        assert(false, "Not Implemented -- instantiateParseAsTypeExpression");
    }

    insantiateExpression(exp: Expression) {
        this.instantiateTypeSignature(exp.getType(), this.currentMapping);

        switch (exp.tag) {
            case ExpressionTag.LiteralTypeDeclValueExpression: {
                this.instantiateLiteralTypeDeclValueExpression(exp as LiteralTypeDeclValueExpression);
                break;
            }
            case ExpressionTag.HasEnvValueExpression: {
                this.instantiateHasEnvValueExpression(exp as AccessEnvValueExpression);
                break;
            }
            case ExpressionTag.AccessEnvValueExpression: {
                this.instantiateAccessEnvValueExpression(exp as AccessEnvValueExpression);
                break;
            }
            case ExpressionTag.TaskAccessInfoExpression: {
                this.instantiateTaskAccessInfoExpression(exp as TaskAccessInfoExpression);
                break;
            }
            case ExpressionTag.AccessEnumExpression: {
                this.instantiateAccessEnumExpression(exp as AccessEnumExpression);
                break;
            }
            case ExpressionTag.AccessStaticFieldExpression: {
                this.instantiateAccessStaticFieldExpression(exp as AccessStaticFieldExpression);
                break;
            }
            case ExpressionTag.ConstructorPrimaryExpression: {
                this.instantiateConstructorPrimaryExpression(exp as ConstructorPrimaryExpression);
                break;
            }
            case ExpressionTag.ConstructorEListExpression: {
                this.instantiateConstructorEListExpression(exp as ConstructorEListExpression);
                break;
            }
            case ExpressionTag.ConstructorLambdaExpression: {
                this.instantiateConstructorLambdaExpression(exp as ConstructorLambdaExpression);
                break;
            }
            case ExpressionTag.LetExpression: {
                this.instantiateLetExpression(exp as LetExpression);
                break;
            }
            case ExpressionTag.LambdaInvokeExpression: {
                this.instantiateLambdaInvokeExpression(exp as LambdaInvokeExpression);
                break;
            }
            case ExpressionTag.SpecialConstructorExpression: {
                this.instantiateSpecialConstructorExpression(exp as SpecialConstructorExpression);
                break;
            }
            case ExpressionTag.SpecialConverterExpression: {
                this.instantiateSpecialConverterExpression(exp as SpecialConverterExpression);
                break;
            }
            case ExpressionTag.CallNamespaceFunctionExpression: {
                this.instantiateCallNamespaceFunctionExpression(exp as CallNamespaceFunctionExpression);
                break;
            }
            case ExpressionTag.CallTypeFunctionExpression: {
                this.instantiateCallTypeFunctionExpression(exp as CallTypeFunctionExpression);
                break;
            }
            case ExpressionTag.LogicActionAndExpression: {
                this.instantiateLogicActionAndExpression(exp as LogicActionAndExpression);
                break;
            }
            case ExpressionTag.LogicActionOrExpression: {
                this.instantiateLogicActionOrExpression(exp as LogicActionOrExpression);
                break;
            }
            case ExpressionTag.ParseAsTypeExpression: {
                this.instantiateParseAsTypeExpression(exp as ParseAsTypeExpression);
                break;
            }
            default: {
                ; //handled by the type signature instantiation on exp type
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