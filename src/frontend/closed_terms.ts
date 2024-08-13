import assert from "node:assert";

import { AbstractNominalTypeDecl, Assembly, NamespaceDeclaration, NamespaceFunctionDecl, TypeFunctionDecl } from "./assembly.js";
import { FunctionInstantiationInfo, NamespaceInstantiationInfo } from "./instantiation_map.js";
import { EListTypeSignature, LambdaTypeSignature, NominalTypeSignature, TemplateNameMapper, TypeSignature } from "./type.js";
import { AccessEnumExpression, AccessEnvValueExpression, AccessStaticFieldExpression, ArgumentValue, CallNamespaceFunctionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, Expression, ExpressionTag, ITest, LambdaInvokeExpression, LetExpression, LiteralTypeDeclValueExpression, LogicActionAndExpression, LogicActionOrExpression, ParseAsTypeExpression, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixLiteralKeyAccess, PostfixOp, PostfixOpTag, SpecialConstructorExpression, SpecialConverterExpression, TaskAccessInfoExpression } from "./body.js";

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
        const rt = mapping !== undefined ? type.remapTemplateBindings(mapping) : type;
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

    private areInvokeMappingsEqual(ma: TemplateNameMapper | undefined, mb: TemplateNameMapper | undefined): boolean {
        if(ma === undefined && mb === undefined) {
            return true;
        }
        else if(ma === undefined || mb === undefined) {
            return false;
        }
        else {
            return TemplateNameMapper.identicalMappings(ma, mb);
        }
    }

    private isAlreadySeenNamespaceFunction(fkey: string, fdecl: NamespaceFunctionDecl, mapping: TemplateNameMapper | undefined): boolean {
        const isdonef = this.instantiation.some((ainfo) => {
            if(!ainfo.functionbinds.has(fdecl.name)) {
                return false;
            }

            const bop = ainfo.functionbinds.get(fdecl.name) as FunctionInstantiationInfo;
            if(bop.binds === undefined) {
                return true;
            }
            else {
                return bop.binds.some((b) => this.areInvokeMappingsEqual(b, mapping));
            }
        });

        if(isdonef) {
            return true;
        }
        
        return this.pendingNamespaceFunctions.some((pnf) => pnf.fkey === fkey);
    }

    //Given a namespace function -- instantiate it
    private instantiateNamespaceFunction(ns: NamespaceDeclaration, fdecl: NamespaceFunctionDecl, terms: TypeSignature[], mapping: TemplateNameMapper | undefined) {
        const tterms = mapping !== undefined ? terms.map((t) => t.remapTemplateBindings(mapping)) : terms;
        const fkey = `${ns.fullnamespace.emit()}::${fdecl.name}${computeTBindsKey(tterms)}`;


        if(tterms.length === 0) {
            if(this.isAlreadySeenNamespaceFunction(fkey, fdecl, undefined)) {
                return;
            }
    
            this.pendingNamespaceFunctions.push(new PendingNamespaceFunction(ns, fdecl, []));
        }
        else {
            let fmapping = new Map<string, TypeSignature>();
            for(let i = 0; i < fdecl.terms.length; ++i) {
                fmapping.set(fdecl.terms[i].name, tterms[i]);
            }

            if(this.isAlreadySeenNamespaceFunction(fkey, fdecl, TemplateNameMapper.createInitialMapping(fmapping))) {
                return;
            }

            this.pendingNamespaceFunctions.push(new PendingNamespaceFunction(ns, fdecl, tterms));
        }
    }

    private processITestAsBoolean(sinfo: SourceInfo, env: TypeEnvironment, src: TypeSignature, tt: ITest): { ttrue: boolean, tfalse: boolean } {
        if(tt instanceof ITestType) {
            if(!this.checkTypeSignature(tt.ttype)) {
                return { ttrue: false, tfalse: false };
            }
            else {
                const tres = this.processITest_Type(src, tt.ttype);
                if(tt.isnot) {
                    return { ttrue: tres.tfalse.length !== 0, tfalse: tres.ttrue.length !== 0 };
                }
                else {
                    return { ttrue: tres.ttrue.length !== 0, tfalse: tres.tfalse.length !== 0 };
                }
            }
        }
        else {
            if(tt instanceof ITestNone) {
                const tres = this.processITest_None(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else if(tt instanceof ITestSome) {
                const tres = this.processITest_Some(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else if(tt instanceof ITestOk) {
                const tres = this.processITest_Ok(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else {
                assert(tt instanceof ITestErr, "missing case in ITest");
                const tres = this.processITest_Err(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
        }
    }

    private processITestAsConvert(sinfo: SourceInfo, env: TypeEnvironment, src: TypeSignature, tt: ITest): { ttrue: TypeSignature | undefined, tfalse: TypeSignature | undefined } {
        if(tt instanceof ITestType) {
            if(!this.checkTypeSignature(tt.ttype)) {
                return { ttrue: undefined, tfalse: undefined };
            }
            else {
                const tres = this.processITest_Type(src, tt.ttype);
                if(tt.isnot) {
                    const ttrue = tres.tfalse.length !== 0 ? this.processITestConvertLUB(sinfo, tres.tfalse, src) : undefined; //negate takes the remain and lubs to the src
                    const tfalse = tres.ttrue.length !== 0 ? this.processITestConvertForce(tres.ttrue, tt.ttype) : undefined; //overlap and passes as the user spec type -- does not matter now but short circuiting return will use this

                    return { ttrue: ttrue, tfalse: tfalse };
                }
                else {
                    const ttrue = tres.ttrue.length !== 0 ? this.processITestConvertForce(tres.ttrue, tt.ttype) : undefined; //always cast to what the user asked for
                    const tfalse = tres.tfalse.length !== 0 ? this.processITestConvertLUB(sinfo, tres.tfalse, src) : undefined; //cast to the LUB of the remaining types (with src as a default option)

                    return { ttrue: ttrue, tfalse: tfalse };
                }
            }
        }
        else {
            if(tt instanceof ITestNone) {
                const tres = this.processITest_None(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else if(tt instanceof ITestSome) {
                const tres = this.processITest_Some(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else if(tt instanceof ITestOk) {
                const tres = this.processITest_Ok(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else {
                assert(tt instanceof ITestErr, "missing case in ITest");
                const tres = this.processITest_Err(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
        }
    }

    private instantiateArgumentList(args: ArgumentValue[]) {
        args.forEach((arg) => this.insantiateExpression(arg.exp));
    }

    private instantiateConstructorArgumentList(args: ArgumentValue[]) {
        args.forEach((arg) => this.insantiateExpression(arg.exp));
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
        this.instantiateConstructorArgumentList(exp.args.args);
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
        this.insantiateExpression(exp.arg);
    }

    private instantiateSpecialConverterExpression(exp: SpecialConverterExpression) {
        assert(false, "Not Implemented -- instantiateSpecialConverterExpression");
    }

    private instantiateCallNamespaceFunctionExpression(exp: CallNamespaceFunctionExpression) {
        this.instantiateArgumentList(exp.args.args);

        const nns = this.assembly.resolveNamespaceDecl(exp.ns.ns) as NamespaceDeclaration;
        const nfd = this.assembly.resolveNamespaceFunction(exp.ns, exp.name) as NamespaceFunctionDecl;
        this.instantiateNamespaceFunction(nns, nfd, exp.terms, this.currentMapping);
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

    private instantiatePostfixIsTest(exp: PostfixIsTest) {
        this.instantiateITe
        const splits = this.processITestAsBoolean(exp.sinfo, env, rcvrtype, exp.ttest);
        this.checkError(exp.sinfo, !splits.ttrue, "Test is never true");
        this.checkError(exp.sinfo, !splits.tfalse, "Test is never false");

        return exp.setType(this.getWellKnownType("Bool"));
    }

    private instantiatePostfixAsConvert(exp: PostfixAsConvert) {
        const splits = this.processITestAsConvert(exp.sinfo, env, rcvrtype, exp.ttest);
        this.checkError(exp.sinfo, splits.ttrue === undefined, "Convert always fails");
        //if always true then this is an upcast and OK!

        return exp.setType(splits.ttrue || new ErrorTypeSignature(exp.sinfo, undefined));
    }

    private instantiatePostfixAssignFields(exp: PostfixAssignFields) {
        assert(false, "Not Implemented -- instantiatePostfixAssignFields");
    }

    private instantiatePostfixInvoke(exp: PostfixInvoke) {
        assert(false, "Not Implemented -- instantiatePostfixInvoke");
    }

    private instantiatePostfixLiteralKeyAccess(exp: PostfixLiteralKeyAccess) {
        assert(false, "Not Implemented -- instantiatePostfixLiteralKeyAccess");
    }

    private instantiatePostfixOp(exp: PostfixOp) {
        this.insantiateExpression(exp.rootExp);
        
        for(let i = 0; i < exp.ops.length; ++i) {
            const op = exp.ops[i];

            this.instantiateTypeSignature(op.getType(), this.currentMapping);
            this.instantiateTypeSignature(op.getRcvrType(), this.currentMapping);

            switch(op.tag) {
                case PostfixOpTag.PostfixIsTest: {
                    this.instantiatePostfixIsTest(op as PostfixIsTest);
                    break;
                }
                case PostfixOpTag.PostfixAsConvert: {
                    this.instantiatePostfixAsConvert(op as PostfixAsConvert);
                    break;
                }
                case PostfixOpTag.PostfixAssignFields: {
                    this.instantiatePostfixAssignFields(op as PostfixAssignFields);
                    break;
                }
                case PostfixOpTag.PostfixInvoke: {
                    this.instantiatePostfixInvoke(op as PostfixInvoke);
                    break;
                }
                case PostfixOpTag.PostfixLiteralKeyAccess: {
                    this.instantiatePostfixLiteralKeyAccess(op as PostfixLiteralKeyAccess);
                    break;
                }
                default: {
                    break; //instantiation handled by standard type signature instantiation
                }
            }
        }
    }

    private insantiateExpression(exp: Expression) {
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
            case ExpressionTag.PostfixOpExpression: {
                return this.instantiatePostfixOp(env, exp as PostfixOp);
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