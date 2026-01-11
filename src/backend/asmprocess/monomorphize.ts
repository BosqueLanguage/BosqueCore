import assert from "node:assert";

import { AbstractCollectionTypeDecl, AbstractNominalTypeDecl, AgentDecl, APIDecl, APIDeniedTypeDecl, APIErrorTypeDecl, APIFlaggedTypeDecl, APIRejectedTypeDecl, APIResultTypeDecl, APISuccessTypeDecl, Assembly, ConceptTypeDecl, ConstMemberDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, EntityTypeDecl, EnumTypeDecl, EnvironmentVariableInformation, EventListTypeDecl, ExplicitInvokeDecl, FailTypeDecl, InvariantDecl, ListTypeDecl, MapEntryTypeDecl, MapTypeDecl, MemberFieldDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, OkTypeDecl, OptionTypeDecl, PostConditionDecl, PreConditionDecl, PrimitiveEntityTypeDecl, QueueTypeDecl, ResourceInformation, ResultTypeDecl, SetTypeDecl, SomeTypeDecl, StackTypeDecl, TaskActionDecl, TaskConfiguration, TaskDecl, TaskMethodDecl, TypedeclTypeDecl, TypeFunctionDecl, ValidateDecl } from "../../frontend/assembly.js";
import { InvokeInstantiationInfo, NamespaceInstantiationInfo, TypeInstantiationInfo } from "./instantiations.js";
import { DashResultTypeSignature, EListTypeSignature, FormatPathTypeSignature, FormatStringTypeSignature, LambdaTypeSignature, NominalTypeSignature, TemplateNameMapper, TypeSignature, VoidTypeSignature } from "../../frontend/type.js";
import { AbortStatement, AbstractBodyImplementation, AccessEnumExpression, AccessEnvValueExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, AgentInvokeExpression, APIInvokeExpression, ArgumentValue, AssertStatement, BaseRValueExpression, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinMultExpression, BinSubExpression, BlockStatement, BodyImplementation, BuiltinBodyImplementation, CallNamespaceFunctionExpression, CallRefInvokeExpression, CallRefSelfExpression, CallRefThisExpression, CallRefVariableExpression, CallTaskActionExpression, CallTypeFunctionExpression, ChkLogicBaseExpression, ChkLogicExpression, ChkLogicExpressionTag, ChkLogicImpliesExpression, ConditionalValueExpression, ConstructorEListExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, DebugStatement, DispatchPatternStatement, DispatchTaskStatement, EmptyStatement, Expression, ExpressionBodyImplementation, ExpressionTag, FormatStringArgComponent, FormatStringComponent, HoleBodyImplementation, HoleExpression, HoleStatement, IfElifElseStatement, IfElseStatement, IfStatement, ITestGuard, ITestGuardSet, ITestSimpleGuard, KeyCompareEqExpression, KeyCompareLessExpression, LambdaInvokeExpression, LiteralFormatCStringExpression, LiteralFormatStringExpression, LiteralTypedCStringExpression, LiteralTypeDeclValueExpression, LiteralTypedFormatCStringExpression, LiteralTypedFormatStringExpression, LiteralTypedStringExpression, LogicAndExpression, LogicOrExpression, MapEntryConstructorExpression, MatchStatement, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixSliceOperator, PostfixOp, PostfixOpTag, PredicateUFBodyImplementation, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, ReturnMultiStatement, ReturnSingleStatement, ReturnVoidStatement, RValueExpression, RValueExpressionTag, SelfUpdateStatement, SpecialConstructorExpression, StandardBodyImplementation, Statement, StatementTag, SwitchStatement, TaskAccessInfoExpression, TaskAllExpression, TaskCheckAndHandleTerminationStatement, TaskDashExpression, TaskMultiExpression, TaskRaceExpression, TaskRunExpression, TaskStatusStatement, TaskYieldStatement, ThisUpdateStatement, UpdateStatement, ValidateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VarUpdateStatement, VoidRefCallStatement } from "../../frontend/body.js";
import { SourceInfo } from "../../frontend/build_decls.js";

import { IRLambdaParameterPackTypeSignature } from "../irdefs/irtype.js";

class PendingNamespaceFunction {
    readonly namespace: NamespaceDeclaration;
    readonly function: NamespaceFunctionDecl;
    readonly instantiation: TypeSignature[];
    readonly lambdas: { pname: string, psig: IRLambdaParameterPackTypeSignature, invtrgt: string }[];

    readonly fkey: string;

    constructor(namespace: NamespaceDeclaration, func: NamespaceFunctionDecl, instantiation: TypeSignature[], lambdas: { pname: string, psig: IRLambdaParameterPackTypeSignature, invtrgt: string }[], fkey: string) {
        this.namespace = namespace;
        this.function = func;
        this.instantiation = instantiation;
        this.lambdas = lambdas;

        this.fkey = fkey;
    }
}

class PendingTypeFunction {
    readonly type: TypeSignature;
    readonly function: TypeFunctionDecl;
    readonly instantiation: TypeSignature[];
    readonly lambdas: { pname: string, psig: IRLambdaParameterPackTypeSignature, invtrgt: string }[];

    readonly fkey: string;

    constructor(type: TypeSignature, func: TypeFunctionDecl, instantiation: TypeSignature[], lambdas: { pname: string, psig: IRLambdaParameterPackTypeSignature, invtrgt: string }[], fkey: string) {
        this.type = type;
        this.function = func;
        this.instantiation = instantiation;
        this.lambdas = lambdas;

        this.fkey = fkey;;
    }
}

class PendingTypeMethod {
    readonly type: TypeSignature;
    readonly method: ExplicitInvokeDecl;
    readonly instantiation: TypeSignature[];
    readonly lambdas: { pname: string, psig: IRLambdaParameterPackTypeSignature, invtrgt: string }[];

    readonly mkey: string;

    constructor(type: TypeSignature, mthd: ExplicitInvokeDecl, instantiation: TypeSignature[], lambdas: { pname: string, psig: IRLambdaParameterPackTypeSignature, invtrgt: string }[], mkey: string) {
        this.type = type;
        this.method = mthd;
        this.instantiation = instantiation;
        this.lambdas = lambdas;

        this.mkey = mkey;
    }
}

class PendingNominalTypeDecl {
    readonly type: AbstractNominalTypeDecl;
    readonly instantiation: TypeSignature[];

    readonly tkey: string;
    readonly tsig: TypeSignature;

    constructor(tkeystr: string, tsig: TypeSignature, type: AbstractNominalTypeDecl, instantiation: TypeSignature[]) {
        this.type = type;
        this.tsig = tsig;
        this.instantiation = instantiation;

        this.tkey = tkeystr;
    }
}

class Monomorphizer {
    readonly assembly: Assembly;
    readonly instantiation: NamespaceInstantiationInfo[];

    lambdaCtr: number = 0;

    readonly wellknowntypes: Map<string, TypeSignature>;

    readonly pendingNominalTypeDecls: PendingNominalTypeDecl[] = [];
    readonly pendingNamespaceFunctions: PendingNamespaceFunction[] = [];
    readonly pendingTypeFunctions: PendingTypeFunction[] = [];
    readonly pendingTypeMethods: PendingTypeMethod[] = [];
    
    readonly completedInstantiations: Set<string> = new Set<string>();
    readonly completedNamespaceFunctions: Set<string> = new Set<string>();
    readonly completedTypeFunctions: Set<string> = new Set<string>();
    readonly completedMemberMethods: Set<string> = new Set<string>();

    currentMapping: TemplateNameMapper | undefined = undefined;
    currentNSInstantiation: NamespaceInstantiationInfo | undefined = undefined;

    constructor(assembly: Assembly, wellknowntypes: Map<string, TypeSignature>) {
        this.assembly = assembly;
        this.instantiation = [];

        this.wellknowntypes = wellknowntypes;
    }


    private static computeTBindsKey(tbinds: TypeSignature[]): string {
        return (tbinds.length !== 0) ? `<${tbinds.map(t => t.tkeystr).join(", ")}>` : "";
    }

    private static computeLambdaKey(packs: { pname: string, psig: IRLambdaParameterPackTypeSignature, invtrgt: string }[]): string {
        return (packs.length !== 0) ? `[${packs.map(lp => lp.pname).join(", ")}]` : "";
    }

    /*
    private getFreshLambdaKey(): string {
        return `lambda_${this.lambdaCtr++}`;
    }
    */

    private computeResolveKeyForInvoke(ikey: string, termcount: number, hasref: boolean, lambdas: boolean): string {
        const tci = (termcount !== 0) ? `*tc_${termcount}_` : "";
        const rfi = (hasref ? "*_ref_" : "");
        const li = (lambdas ? "*_lambdas_" : "");

        return `${ikey}${tci}${rfi}${li}`;
    }

    private computeInvokeKeyForNamespaceFunction(ns: NamespaceDeclaration, fdecl: NamespaceFunctionDecl, terms: TypeSignature[], lambdas: { pname: string, psig: IRLambdaParameterPackTypeSignature, invtrgt: string }[]): string {
        const rti = fdecl.params.some((p) => p.pkind !== undefined) ? "#ref" : "";
        return `${ns.fullnamespace.emit()}::${fdecl.name}${rti}${Monomorphizer.computeTBindsKey(terms)}${Monomorphizer.computeLambdaKey(lambdas)}`;
    }

    private computeInvokeKeyForTypeFunction(rcvrtype: TypeSignature, fdecl: TypeFunctionDecl, terms: TypeSignature[], lambdas: { pname: string, psig: IRLambdaParameterPackTypeSignature, invtrgt: string }[]): string {
        const rti = fdecl.params.some((p) => p.pkind !== undefined) ? "#ref" : "";
        return `${rcvrtype.tkeystr}::${fdecl.name}${rti}${Monomorphizer.computeTBindsKey(terms)}${Monomorphizer.computeLambdaKey(lambdas)}`;
    }
/*
    private computeInvokeKeyForTypeMethod(rcvrtype: TypeSignature, mdecl: MethodDecl, terms: TypeSignature[], lambdas: { pname: string, psig: IRLambdaParameterPackTypeSignature, invtrgt: string }[]): string {
        const rti = ((mdecl.isThisRef) || mdecl.params.some((p) => p.pkind !== undefined)) ? "#ref" : "";
        return `${rcvrtype.tkeystr}@${mdecl.name}${rti}${Monomorphizer.computeTBindsKey(terms)}${Monomorphizer.computeLambdaKey(lambdas)}`;
    }
*/
    private getWellKnownType(name: string): TypeSignature {
        assert(this.wellknowntypes.has(name), `Well known type ${name} not found`);
        return this.wellknowntypes.get(name) as TypeSignature;
    }

    private isAlreadySeenType(tkey: string): boolean {
        return this.completedInstantiations.has(tkey) || this.pendingNominalTypeDecls.some((pntd) => pntd.tkey === tkey);
    }
/*
    private isAlreadySeenNamespaceFunction(fkey: string): boolean {
        return this.completedNamespaceFunctions.has(fkey) || this.pendingNamespaceFunctions.some((pnf) => pnf.fkey === fkey);
    }

    private isAlreadySeenTypeFunction(tkey: string): boolean {
        return this.completedTypeFunctions.has(tkey) || this.pendingTypeFunctions.some((ptf) => ptf.fkey === tkey);
    }

    private isAlreadySeenMemberMethod(mkey: string): boolean {
        return this.completedMemberMethods.has(mkey) || this.pendingTypeMethods.some((ptm) => ptm.mkey === mkey);
    }
*/
    //Given a type signature -- instantiate it and all sub-component types
    private instantiateTypeSignature(type: TypeSignature, mapping: TemplateNameMapper | undefined) {
        const rt = mapping !== undefined ? type.remapTemplateBindings(mapping) : type;
        if(this.isAlreadySeenType(rt.tkeystr)) {
            return;
        }

        if(rt instanceof VoidTypeSignature) {
            ; //nothing to do
        }
        else if(rt instanceof NominalTypeSignature) {
            rt.alltermargs.forEach((tt) => this.instantiateTypeSignature(tt, mapping));
            this.pendingNominalTypeDecls.push(new PendingNominalTypeDecl(rt.tkeystr, rt, rt.decl, rt.alltermargs));
        }
        else if(rt instanceof EListTypeSignature) {
            rt.entries.forEach((tt) => this.instantiateTypeSignature(tt, mapping));
            (this.currentNSInstantiation as NamespaceInstantiationInfo).elists.set(rt.tkeystr, rt);
        }
        else if(rt instanceof DashResultTypeSignature) {
            rt.entries.forEach((tt) => this.instantiateTypeSignature(tt, mapping));
        }
        else if(rt instanceof LambdaTypeSignature) {
            rt.params.forEach((param) => this.instantiateTypeSignature(param.type, mapping));
            this.instantiateTypeSignature(rt.resultType, mapping);
        }
        else if(rt instanceof FormatStringTypeSignature) {
            rt.terms.forEach((tt) => this.instantiateTypeSignature(tt.argtype, mapping));
            this.instantiateTypeSignature(rt.rtype, mapping);
        }
        else if(rt instanceof FormatPathTypeSignature) {
            rt.terms.forEach((tt) => this.instantiateTypeSignature(tt.argtype, mapping));
            this.instantiateTypeSignature(rt.rtype, mapping);
        }
        else {
            //Lambda parameter packs are only introduced in monomorphize to we should not get them here
            assert(false, "Unknown TypeSignature type -- " + rt.tkeystr);
        }
    }

/*
    //Given a namespace function -- instantiate it
    private instantiateNamespaceFunction(ns: NamespaceDeclaration, fdecl: NamespaceFunctionDecl, terms: TypeSignature[], lambdas: { pname: string, psig: IRLambdaParameterPackTypeSignature, invtrgt: string }[]) {
        const tterms = this.currentMapping !== undefined ? terms.map((t) => t.remapTemplateBindings(this.currentMapping as TemplateNameMapper)) : terms;
        const fkey = this.computeInvokeKeyForNamespaceFunction(ns, fdecl, tterms, lambdas);

        if(this.isAlreadySeenNamespaceFunction(fkey)) {
            return;
        }

        this.pendingNamespaceFunctions.push(new PendingNamespaceFunction(ns, fdecl, tterms, lambdas, fkey));
    }

    //Given a type function -- instantiate it
    private instantiateTypeFunction(enclosingType: TypeSignature, fdecl: TypeFunctionDecl, terms: TypeSignature[], lambdas: { pname: string, psig: IRLambdaParameterPackTypeSignature, invtrgt: string }[]) {
        const rcvrtype = this.currentMapping !== undefined ? enclosingType.remapTemplateBindings(this.currentMapping) : enclosingType;
        const tterms = this.currentMapping !== undefined ? terms.map((t) => t.remapTemplateBindings(this.currentMapping as TemplateNameMapper)) : terms;
        const fkey = this.computeInvokeKeyForTypeFunction(rcvrtype, fdecl, tterms, lambdas);

        if(this.isAlreadySeenTypeFunction(fkey)) {
            return;
        }

        this.pendingTypeFunctions.push(new PendingTypeFunction(rcvrtype, fdecl, tterms, lambdas, fkey));
    }

    //Given a type method -- instantiate it
    private instantiateMemberMethod(enclosingType: TypeSignature, mdecl: MethodDecl, terms: TypeSignature[], lambdas: { pname: string, psig: IRLambdaParameterPackTypeSignature, invtrgt: string }[]) {
        const retype = this.currentMapping !== undefined ? enclosingType.remapTemplateBindings(this.currentMapping) : enclosingType;
        const tterms = this.currentMapping !== undefined ? terms.map((t) => t.remapTemplateBindings(this.currentMapping as TemplateNameMapper)) : terms;
        const mkey = this.computeInvokeKeyForTypeMethod(retype, mdecl, tterms, lambdas);

        if(this.isAlreadySeenMemberMethod(mkey)) {
            return;
        }

        this.pendingTypeMethods.push(new PendingTypeMethod(retype, mdecl, tterms, lambdas, mkey));
    }
*/

    private instantiateStringFormatsList(formats: FormatStringComponent[]) {
        for(let i = 0; i < formats.length; ++i) {
            const fc = formats[i];
            if(fc instanceof FormatStringArgComponent) {
                this.instantiateTypeSignature(fc.argType, this.currentMapping);
            }
        }
    }

/*
    private processITestAsBoolean(src: TypeSignature, tt: ITest) {
        this.instantiateTypeSignature(src, this.currentMapping);
        
        if(tt instanceof ITestType) {
            this.instantiateTypeSignature(tt.ttype, this.currentMapping);
        }
        else {
            ; //any needed instantiations will happen in the specific type processing (e.g. Option<T> will also force processing Some<T> and None)
        }
    }

    private processITestAsConvert(src: TypeSignature, tt: ITest) {
        this.instantiateTypeSignature(src, this.currentMapping);
        
        if(tt instanceof ITestType) {
            this.instantiateTypeSignature(tt.ttype, this.currentMapping);
        }
        else {
            ; //any needed instantiations will happen in the specific type processing (e.g. Option<T> will also force processing Some<T> and None)
        }
    }
*/

    private instantiateITestGuardExpression(exp: Expression) {
        switch (exp.tag) {
            case ExpressionTag.CallRefVariableExpression: {
                return this.instantiateCallRefVariableExpression(exp as CallRefVariableExpression);
            }
            case ExpressionTag.CallRefThisExpression: {
                return this.instantiateCallRefThisExpression(exp as CallRefThisExpression);
            }
            case ExpressionTag.CallRefSelfExpression: {
                return this.instantiateCallRefSelfExpression(exp as CallRefSelfExpression);
            }
            case ExpressionTag.CallTaskActionExpression: {
                return this.instantiateCallTaskActionExpression(exp as CallTaskActionExpression);
            }
            default: {
                const ttag = exp.tag;

                if(ttag === ExpressionTag.CallNamespaceFunctionExpression) {
                    return this.instantiateCallNamespaceFunctionExpression(exp as CallNamespaceFunctionExpression);
                }
                else if(ttag === ExpressionTag.CallTypeFunctionExpression) {
                    return this.instantiateCallTypeFunctionExpression(exp as CallTypeFunctionExpression);
                }
                else if(ttag === ExpressionTag.LambdaInvokeExpression) {
                    return this.instantiateLambdaInvokeExpression(exp as LambdaInvokeExpression);
                }
                else if(ttag === ExpressionTag.PostfixOpExpression) {
                    return this.instantiatePostfixOp(exp as PostfixOp);
                }
                else if(ttag === ExpressionTag.PrefixNotOpExpression) {
                    this.instantiateITestGuardExpression((exp as PrefixNotOpExpression).exp);
                }
                else if(ttag === ExpressionTag.LogicAndExpression) {
                    (exp as LogicAndExpression).exps.forEach((e) => this.instantiateITestGuardExpression(e));
                }
                else {
                    return this.instantiateExpression(exp);
                }
            }
        }
    }

    private instantiateITestGuard(tt: ITestGuard) {
        if(tt instanceof ITestSimpleGuard) {
            return this.instantiateITestGuardExpression(tt.exp);
        }
        else {
            assert(false, "Unknown ITestGuard type"); //TODO check and do binders here!!!
        }
    }

    private instantiateITestGuardSet(tt: ITestGuardSet) {
        tt.guards.forEach((guard) => this.instantiateITestGuard(guard));
    }

/*
    private instantiateArgumentList(args: ArgumentValue[]) {
        args.forEach((arg) => this.instantiateExpression(arg.exp));
    }
*/

    private instantiateConstructorArgumentList(args: ArgumentValue[]) {
        args.forEach((arg) => this.instantiateExpression(arg.exp));
    }

    private instantiateLiteralTypeDeclValueExpression(exp: LiteralTypeDeclValueExpression) {
        this.instantiateTypeSignature(exp.constype, this.currentMapping);
        this.instantiateExpression(exp.value);
    }

    private instantiateLiteralTypedStringExpression(exp: LiteralTypedStringExpression) {
        this.instantiateTypeSignature(exp.constype, this.currentMapping);
    }

    private instantiateLiteralTypedCStringExpression(exp: LiteralTypedCStringExpression) {
        this.instantiateTypeSignature(exp.constype, this.currentMapping);
    }

    private instantiateLiteralTypedFormatStringExpression(exp: LiteralTypedFormatStringExpression) {
        this.instantiateTypeSignature(exp.constype, this.currentMapping);
        this.instantiateStringFormatsList(exp.fmts);
    }

    private instantiateLiteralTypedFormatCStringExpression(exp: LiteralTypedFormatCStringExpression) {
        this.instantiateTypeSignature(exp.constype, this.currentMapping);
        this.instantiateStringFormatsList(exp.fmts);
    }
    
    private instantiateAccessEnvValueExpression(exp: AccessEnvValueExpression) {
        if(exp.optoftype !== undefined) {
            this.instantiateTypeSignature(exp.optoftype, this.currentMapping);
        }
    }

    private instantiateTaskAccessInfoExpression(exp: TaskAccessInfoExpression) {
        return;
    }

    private instantiateNamespaceConstExpression(exp: AccessNamespaceConstantExpression) {
        return;
    }

    private instantiateAccessStaticFieldExpression(exp: AccessStaticFieldExpression) {
        this.instantiateTypeSignature(exp.stype, this.currentMapping);
        this.instantiateTypeSignature(exp.resolvedDeclType as NominalTypeSignature, this.currentMapping);
    }

    private instantiateAccessEnumExpression(exp: AccessEnumExpression) {
        this.instantiateTypeSignature(exp.stype, this.currentMapping);
    }

    private instantiateAccessVariableExpression(exp: AccessVariableExpression) {
        return;
    }

    private instantiateCollectionConstructor(decl: AbstractCollectionTypeDecl, t: NominalTypeSignature, args: ArgumentValue[]) {
        /*
        let ists: TypeSignature | undefined = undefined;

        if(decl instanceof ListTypeDecl) {
            const lops = this.assembly.getCoreNamespace().subns.find((ns) => ns.name === "ListOps");
            if(lops !== undefined) {
                const mtree = lops.typedecls.find((tt) => tt.name === "Tree");
                ists = (mtree !== undefined) ? new NominalTypeSignature(t.sinfo, undefined, mtree, [t.alltermargs[0]]) : undefined;

                if(ists !== undefined) {
                    this.instantiateTypeSignature(ists, this.currentMapping);
                }

                if(args.every((arg) => arg instanceof PositionalArgumentValue)) {
                    if(args.length === 0) {
                        const ff = lops.functions.find((f) => f.name === "s_list_create_empty") as NamespaceFunctionDecl;
                        this.instantiateNamespaceFunction(lops, ff, [t.alltermargs[0]]);
                    }
                    else if(args.length <= 6) {
                        const ff = lops.functions.find((f) => f.name === `s_list_create_${args.length}`);
                        if(ff !== undefined) {
                            this.instantiateNamespaceFunction(lops, ff, [t.alltermargs[0]]);
                        }
                    }
                    else {
                        assert(false, "Not Implemented -- large explicit list constructors");
                    }
                }
                else {
                    assert(false, "Not Implemented -- list spread constructors");
                }
            }
        }
        else if(decl instanceof StackTypeDecl) {
            assert(false, "Not Implemented");
        }
        else if(decl instanceof QueueTypeDecl) {
            assert(false, "Not Implemented");
        }
        else if(decl instanceof SetTypeDecl) {
            assert(false, "Not Implemented");
        }
        else {
            const medecl = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "MapEntry") as MapTypeDecl;
            const metdecl = new NominalTypeSignature(t.sinfo, undefined, medecl, [t.alltermargs[0], t.alltermargs[1]]);
            this.instantiateTypeSignature(metdecl, this.currentMapping);

            const mops = this.assembly.getCoreNamespace().subns.find((ns) => ns.name === "MapOps");
            if(mops !== undefined) {
                const mtree = mops.typedecls.find((tt) => tt.name === "Tree");
                ists = (mtree !== undefined) ? new NominalTypeSignature(t.sinfo, undefined, mtree, [t.alltermargs[0], t.alltermargs[1]]) : undefined;

                if(ists !== undefined) {
                    this.instantiateTypeSignature(ists, this.currentMapping);
                }

                if(args.every((arg) => arg instanceof PositionalArgumentValue)) {
                    if(args.length === 0) {
                        const ff = mops.functions.find((f) => f.name === "s_map_create_empty") as NamespaceFunctionDecl;
                        this.instantiateNamespaceFunction(mops, ff, [t.alltermargs[0], t.alltermargs[1]]);
                    }
                    else if(args.length <= 2) {
                        const ff = mops.functions.find((f) => f.name === `s_map_create_${args.length}`) as NamespaceFunctionDecl;

                        this.instantiateNamespaceFunction(mops, ff, [t.alltermargs[0], t.alltermargs[1]]);
                    }
                    else {
                        assert(false, "Not Implemented -- large explicit map constructors");
                    }
                }
                else {
                    assert(false, "Not Implemented -- map spread constructors");
                }
            }
        }
        */
        assert(false, "Not Implemented -- instantiateCollectionConstructor");
    }

    private instantiateConstructorPrimaryExpression(exp: ConstructorPrimaryExpression) {
        this.instantiateConstructorArgumentList(exp.args.args);

        const ctype = (exp.ctype as NominalTypeSignature);
        const decl = ctype.decl;
        if(decl instanceof AbstractCollectionTypeDecl) {
            this.instantiateCollectionConstructor(decl, ctype, exp.args.args);
        }
    }
    
    private instantiateConstructorEListExpression(exp: ConstructorEListExpression) {
        for(let i = 0; i < exp.args.args.length; ++i) {
           this.instantiateExpression(exp.args.args[i].exp);
        }
    }

    private instantiateConstructorLambdaExpression(exp: ConstructorLambdaExpression) {
        /*
        this.instantiateBodyImplementation(exp.invoke.body);
        */
       assert(false, "Not Implemented -- instantiateConstructorLambdaExpression");
    }

    private instantiateLambdaInvokeExpression(exp: LambdaInvokeExpression) {
        /*
        this.instantiateTypeSignature(exp.lambda as LambdaTypeSignature, this.currentMapping);

        this.instantiateArgumentList(exp.args.args);

        for(let i = 0; i < exp.arginfo.length; ++i) {
            this.instantiateTypeSignature(exp.arginfo[i], this.currentMapping);
        }
        if(exp.restinfo !== undefined) {
            const rparamtype = (this.currentMapping !== undefined ? (exp.resttype as TypeSignature).remapTemplateBindings(this.currentMapping) : (exp.resttype as TypeSignature)) as NominalTypeSignature;
            let rargs: ArgumentValue[] = [];

            for(let i = 0; i < exp.restinfo.length; ++i) {
                this.instantiateTypeSignature(exp.restinfo[i][2], this.currentMapping);
                rargs.push(exp.args.args[exp.restinfo[i][0]]);
            }

            this.instantiateCollectionConstructor(rparamtype.decl as AbstractCollectionTypeDecl, rparamtype, rargs);
        }
        */
       assert(false, "Not Implemented -- instantiateLambdaInvokeExpression");
    }

    private instantiateSpecialConstructorExpression(exp: SpecialConstructorExpression) {
        this.instantiateTypeSignature(exp.constype as TypeSignature, this.currentMapping);
        this.instantiateExpression(exp.arg);
    }

    private instantiateCallNamespaceFunctionExpression(exp: CallNamespaceFunctionExpression) {
        /*
        this.instantiateArgumentList(exp.args.args);

        for(let i = 0; i < exp.shuffleinfo.length; ++i) {
            this.instantiateTypeSignature(exp.shuffleinfo[i][1], this.currentMapping);
        }
        if(exp.restinfo !== undefined) {
            const rparamtype = (this.currentMapping !== undefined ? (exp.resttype as TypeSignature).remapTemplateBindings(this.currentMapping) : (exp.resttype as TypeSignature)) as NominalTypeSignature;
            let rargs: ArgumentValue[] = [];

            for(let i = 0; i < exp.restinfo.length; ++i) {
                this.instantiateTypeSignature(exp.restinfo[i][2], this.currentMapping);
                rargs.push(exp.args.args[exp.restinfo[i][0]]);
            }

            this.instantiateCollectionConstructor(rparamtype.decl as AbstractCollectionTypeDecl, rparamtype, rargs);
        }

        const nns = this.assembly.resolveNamespaceDecl(exp.ns.ns) as NamespaceDeclaration;
        const nfd = this.assembly.resolveNamespaceFunction(exp.ns, exp.name) as NamespaceFunctionDecl;
        this.instantiateNamespaceFunction(nns, nfd, exp.terms);
        */
       assert(false, "Not Implemented -- instantiateCallNamespaceFunctionExpression");
    }

    private instantiateCallTypeFunctionExpression(exp: CallTypeFunctionExpression) {
        /*
        this.instantiateTypeSignature(exp.ttype, this.currentMapping);
        this.instantiateTypeSignature(exp.resolvedDeclType as TypeSignature, this.currentMapping);

        this.instantiateArgumentList(exp.args.args);

        for(let i = 0; i < exp.shuffleinfo.length; ++i) {
            this.instantiateTypeSignature(exp.shuffleinfo[i][1], this.currentMapping);
        }
        if(exp.restinfo !== undefined) {
            const rparamtype = (this.currentMapping !== undefined ? (exp.resttype as TypeSignature).remapTemplateBindings(this.currentMapping) : (exp.resttype as TypeSignature)) as NominalTypeSignature;
            let rargs: ArgumentValue[] = [];

            for(let i = 0; i < exp.restinfo.length; ++i) {
                this.instantiateTypeSignature(exp.restinfo[i][2], this.currentMapping);
                rargs.push(exp.args.args[exp.restinfo[i][0]]);
            }

            this.instantiateCollectionConstructor(rparamtype.decl as AbstractCollectionTypeDecl, rparamtype, rargs);
        }

        if(!exp.isSpecialCall) {
            const fdecl = (exp.resolvedDeclType as NominalTypeSignature).decl.functions.find((ff) => ff.name === exp.name) as TypeFunctionDecl;
            this.instantiateTypeFunction(exp.resolvedDeclType as TypeSignature, (exp.resolvedDeclType as NominalTypeSignature).decl, fdecl, exp.terms);
        }
        */
       assert(false, "Not Implemented -- instantiateCallTypeFunctionExpression");
    }

    private instantiateParseAsTypeExpression(exp: ParseAsTypeExpression) {
        this.instantiateTypeSignature(exp.ttype, this.currentMapping);
        this.instantiateExpression(exp.exp);
    }

    private instantiatePostfixIsTest(exp: PostfixIsTest) {
        /*
        this.processITestAsBoolean(exp.getRcvrType(), exp.ttest);
        */
        assert(false, "Not Implemented -- instantiatePostfixIsTest");
    }

    private instantiatePostfixAsConvert(exp: PostfixAsConvert) {
        /*
        this.processITestAsConvert(exp.getRcvrType(), exp.ttest);
        */
        assert(false, "Not Implemented -- instantiatePostfixAsConvert");
    }

    private instantiatePostfixAssignFields(exp: PostfixAssignFields) {
        /*
        for(let i = 0; i < exp.updates.length; ++i) {
            this.instantiateExpression(exp.updates[i][1]);
        }

        this.instantiateTypeSignature(exp.updatetype as TypeSignature, this.currentMapping);

        for(let i = 0; i < exp.updateinfo.length; ++i) {
            this.instantiateTypeSignature(exp.updateinfo[i].fieldtype, this.currentMapping);
            this.instantiateTypeSignature(exp.updateinfo[i].etype, this.currentMapping);
        }
        */
        assert(false, "Not Implemented -- instantiatePostfixAssignFields");
    }

    private instantiatePostfixSliceOperator(exp: PostfixSliceOperator) {
        assert(false, "Not Implemented -- instantiatePostfixSliceOperator");
    }

    private instantiatePostfixInvoke(exp: PostfixInvoke) {
        /*
        this.instantiateArgumentList(exp.args.args);

        for(let i = 0; i < exp.shuffleinfo.length; ++i) {
            this.instantiateTypeSignature(exp.shuffleinfo[i][1], this.currentMapping);
        }
        if(exp.restinfo !== undefined) {
            const rparamtype = (this.currentMapping !== undefined ? (exp.resttype as TypeSignature).remapTemplateBindings(this.currentMapping) : (exp.resttype as TypeSignature)) as NominalTypeSignature;
            let rargs: ArgumentValue[] = [];

            for(let i = 0; i < exp.restinfo.length; ++i) {
                this.instantiateTypeSignature(exp.restinfo[i][2], this.currentMapping);
                rargs.push(exp.args.args[exp.restinfo[i][0]]);
            }

            this.instantiateCollectionConstructor(rparamtype.decl as AbstractCollectionTypeDecl, rparamtype, rargs);
        }

        if(exp.resolvedTrgt !== undefined) {
            this.instantiateTypeSignature(exp.resolvedTrgt, this.currentMapping);

            const nns = (exp.resolvedTrgt as NominalTypeSignature).decl.ns;
            const mm = (exp.resolvedMethod as MethodDecl);
            this.instantiateSpecificResolvedMemberMethod(nns, exp.resolvedTrgt, mm, exp.terms);
        }
        else {
            assert(false, "Not Implemented -- instantiatePostfixInvoke for virtual");
        }
        */
        assert(false, "Not Implemented -- instantiatePostfixInvoke");
    }

    private instantiatePostfixOp(exp: PostfixOp) {
        this.instantiateExpression(exp.rootExp);
        
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
                case PostfixOpTag.PostfixSliceOperator: {
                    this.instantiatePostfixSliceOperator(op as PostfixSliceOperator);
                    break;
                }
                case PostfixOpTag.PostfixInvoke: {
                    this.instantiatePostfixInvoke(op as PostfixInvoke);
                    break;
                }
                default: {
                    break; //instantiation handled by standard type signature instantiation
                }
            }
        }
    }

    private instantiatePrefixNotOpExpression(exp: PrefixNotOpExpression) {
        this.instantiateExpression(exp.exp);
    }

    private instantiatePrefixNegateOrPlusOpExpression(exp: PrefixNegateOrPlusOpExpression) {
        this.instantiateExpression(exp.exp);
    }

    private instantiateBinaryNumericArgs(lhs: Expression, rhs: Expression) {
        this.instantiateExpression(lhs);
        this.instantiateExpression(rhs);
    }

    private instantiateBinAddExpression(exp: BinAddExpression) {
        this.instantiateBinaryNumericArgs(exp.lhs, exp.rhs);
    }

    private instantiateBinSubExpression(exp: BinSubExpression) {
        this.instantiateBinaryNumericArgs(exp.lhs, exp.rhs);
    }

    private instantiateBinMultExpression(exp: BinMultExpression) {
        this.instantiateBinaryNumericArgs(exp.lhs, exp.rhs);
    }

    private instantiateBinDivExpression(exp: BinDivExpression) {
        this.instantiateBinaryNumericArgs(exp.lhs, exp.rhs);
    }

    private instantiateBinKeyEqExpression(exp: BinKeyEqExpression) {
        this.instantiateExpression(exp.lhs);
        this.instantiateExpression(exp.rhs);
    }

    private instantiateBinKeyNeqExpression(exp: BinKeyNeqExpression) {
        this.instantiateExpression(exp.lhs);
        this.instantiateExpression(exp.rhs);
    }

    private instantiateKeyCompareEqExpression(exp: KeyCompareEqExpression) {
        this.instantiateTypeSignature(exp.ktype, this.currentMapping);

        this.instantiateExpression(exp.lhs);
        this.instantiateExpression(exp.rhs);
    }

    private instantiateKeyCompareLessExpression(exp: KeyCompareLessExpression) {
        this.instantiateTypeSignature(exp.ktype, this.currentMapping);

        this.instantiateExpression(exp.lhs);
        this.instantiateExpression(exp.rhs);
    }

    private instantiateNumericEqExpression(exp: NumericEqExpression) {
        this.instantiateBinaryNumericArgs(exp.lhs, exp.rhs);
    }

    private instantiateNumericNeqExpression(exp: NumericNeqExpression) {
        this.instantiateBinaryNumericArgs(exp.lhs, exp.rhs);
    }

    private instantiateNumericLessExpression(exp: NumericLessExpression) {
        this.instantiateBinaryNumericArgs(exp.lhs, exp.rhs);
    }

    private instantiateNumericLessEqExpression(exp: NumericLessEqExpression) {
        this.instantiateBinaryNumericArgs(exp.lhs, exp.rhs);
    }

    private instantiateNumericGreaterExpression(exp: NumericGreaterExpression) {
        this.instantiateBinaryNumericArgs(exp.lhs, exp.rhs);
    }

    private instantiateNumericGreaterEqExpression(exp: NumericGreaterEqExpression) {
        this.instantiateBinaryNumericArgs(exp.lhs, exp.rhs);
    }

    private instantiateLogicAndExpression(exp: LogicAndExpression) {
        exp.exps.forEach((e) => this.instantiateExpression(e));
    }

    private instantiateLogicOrExpression(exp: LogicOrExpression) {
        exp.exps.forEach((e) => this.instantiateExpression(e));
    }

    private instantiateHoleExpression(exp: HoleExpression) {
        if(exp.explicittype !== undefined) {
            this.instantiateTypeSignature(exp.explicittype, this.currentMapping);
        }

        if(exp.samplesfile !== undefined) {
            this.instantiateExpression(exp.samplesfile);
        }
    }

    private instantiateMapEntryConstructorExpression(exp: MapEntryConstructorExpression) {
        this.instantiateExpression(exp.kexp);
        this.instantiateExpression(exp.vexp);
    }

    // Add our rope instantiation here, check if we are cstring or string and go lookup ns to find the constructor for the correct size
    private instantiateExpression(exp: Expression) {
        this.instantiateTypeSignature(exp.getType(), this.currentMapping);

        switch (exp.tag) {
            case ExpressionTag.LiteralNoneExpression:
            case ExpressionTag.LiteralBoolExpression:
            case ExpressionTag.LiteralNatExpression:
            case ExpressionTag.LiteralIntExpression:
            case ExpressionTag.LiteralChkNatExpression:
            case ExpressionTag.LiteralChkIntExpression:
            case ExpressionTag.LiteralRationalExpression:
            case ExpressionTag.LiteralFloatExpression:
            case ExpressionTag.LiteralDecimalExpression:
            case ExpressionTag.LiteralDecimalDegreeExpression:
            case ExpressionTag.LiteralLatLongCoordinateExpression:
            case ExpressionTag.LiteralComplexNumberExpression:
            case ExpressionTag.LiteralByteBufferExpression:
            case ExpressionTag.LiteralUUIDv4Expression:
            case ExpressionTag.LiteralUUIDv7Expression:
            case ExpressionTag.LiteralSHAContentHashExpression:
            case ExpressionTag.LiteralTZDateTimeExpression:
            case ExpressionTag.LiteralTAITimeExpression:
            case ExpressionTag.LiteralPlainDateExpression:
            case ExpressionTag.LiteralPlainTimeExpression:
            case ExpressionTag.LiteralLogicalTimeExpression:
            case ExpressionTag.LiteralISOTimeStampExpression:
            case ExpressionTag.LiteralDeltaDateTimeExpression:
            case ExpressionTag.LiteralDeltaISOTimeStampExpression:
            case ExpressionTag.LiteralDeltaSecondsExpression:
            case ExpressionTag.LiteralDeltaLogicalExpression:
            case ExpressionTag.LiteralUnicodeRegexExpression:
            case ExpressionTag.LiteralCRegexExpression:
            case ExpressionTag.LiteralByteExpression:
            case ExpressionTag.LiteralCCharExpression:
            case ExpressionTag.LiteralUnicodeCharExpression:
            case ExpressionTag.LiteralStringExpression:
            case ExpressionTag.LiteralCStringExpression: {
                break; //nothing to do
            }
            case ExpressionTag.LiteralFormatStringExpression: {
                this.instantiateStringFormatsList((exp as LiteralFormatStringExpression).fmts);
                break;
            }
            case ExpressionTag.LiteralFormatCStringExpression: {
                this.instantiateStringFormatsList((exp as LiteralFormatCStringExpression).fmts);
                break;
            }
            case ExpressionTag.LiteralPathExpression:
            case ExpressionTag.LiteralPathFragmentExpression:
            case ExpressionTag.LiteralGlobExpression: {
                break; //nothing to do
            }
            case ExpressionTag.LiteralTypeDeclValueExpression: {
                this.instantiateLiteralTypeDeclValueExpression(exp as LiteralTypeDeclValueExpression);
                break;
            }
            case ExpressionTag.LiteralTypedStringExpression: {
                this.instantiateLiteralTypedStringExpression(exp as LiteralTypedStringExpression);
                break;
            }
            case ExpressionTag.LiteralTypedCStringExpression: {
                this.instantiateLiteralTypedCStringExpression(exp as LiteralTypedCStringExpression);
                break;
            }
            case ExpressionTag.LiteralTypedFormatStringExpression: {
                this.instantiateLiteralTypedFormatStringExpression(exp as LiteralTypedFormatStringExpression);
                break;
            }
            case ExpressionTag.LiteralTypedFormatCStringExpression: {
                this.instantiateLiteralTypedFormatCStringExpression(exp as LiteralTypedFormatCStringExpression);
                break;
            }
            case ExpressionTag.AccessEnvValueExpression: {
                this.instantiateAccessEnvValueExpression(exp as AccessEnvValueExpression);
                break;
            }
            case ExpressionTag.TaskAccessIDExpression: {
                this.instantiateTaskAccessInfoExpression(exp as TaskAccessInfoExpression);
                break;
            }
            case ExpressionTag.AccessNamespaceConstantExpression: {
                this.instantiateNamespaceConstExpression(exp as AccessNamespaceConstantExpression);
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
            case ExpressionTag.AccessVariableExpression: {
                this.instantiateAccessVariableExpression(exp as AccessVariableExpression);
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
            case ExpressionTag.LambdaInvokeExpression: {
                this.instantiateLambdaInvokeExpression(exp as LambdaInvokeExpression);
                break;
            }
            case ExpressionTag.SpecialConstructorExpression: {
                this.instantiateSpecialConstructorExpression(exp as SpecialConstructorExpression);
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
            case ExpressionTag.ParseAsTypeExpression: {
                this.instantiateParseAsTypeExpression(exp as ParseAsTypeExpression);
                break;
            }
            case ExpressionTag.PostfixOpExpression: {
                this.instantiatePostfixOp(exp as PostfixOp);
                break;
            }
            case ExpressionTag.PrefixNotOpExpression: {
                this.instantiatePrefixNotOpExpression(exp as PrefixNotOpExpression);
                break;
            }
            case ExpressionTag.PrefixNegateOrPlusOpExpression: {
                this.instantiatePrefixNegateOrPlusOpExpression(exp as PrefixNegateOrPlusOpExpression);
                break;
            }
            case ExpressionTag.BinAddExpression: {
                this.instantiateBinAddExpression(exp as BinAddExpression);
                break;
            }
            case ExpressionTag.BinSubExpression: {
                this.instantiateBinSubExpression(exp as BinSubExpression);
                break;
            }
            case ExpressionTag.BinMultExpression: {
                this.instantiateBinMultExpression(exp as BinMultExpression);
                break;
            }
            case ExpressionTag.BinDivExpression: {
                this.instantiateBinDivExpression(exp as BinDivExpression);
                break;
            }
            case ExpressionTag.BinKeyEqExpression: {
                this.instantiateBinKeyEqExpression(exp as BinKeyEqExpression);
                break;
            }
            case ExpressionTag.BinKeyNeqExpression: {
                this.instantiateBinKeyNeqExpression(exp as BinKeyNeqExpression);
                break;
            }
            case ExpressionTag.KeyCompareEqExpression: {
                this.instantiateKeyCompareEqExpression(exp as KeyCompareEqExpression);
                break;
            }
            case ExpressionTag.KeyCompareLessExpression: {
                this.instantiateKeyCompareLessExpression(exp as KeyCompareLessExpression);
                break;
            }
            case ExpressionTag.NumericEqExpression: {
                this.instantiateNumericEqExpression(exp as NumericEqExpression);
                break;
            }
            case ExpressionTag.NumericNeqExpression: {
                this.instantiateNumericNeqExpression(exp as NumericNeqExpression);
                break;
            }
            case ExpressionTag.NumericLessExpression: {
                this.instantiateNumericLessExpression(exp as NumericLessExpression);
                break;
            }
            case ExpressionTag.NumericLessEqExpression: {
                this.instantiateNumericLessEqExpression(exp as NumericLessEqExpression);
                break;
            }
            case ExpressionTag.NumericGreaterExpression: {
                this.instantiateNumericGreaterExpression(exp as NumericGreaterExpression);
                break;
            }
            case ExpressionTag.NumericGreaterEqExpression: {
                this.instantiateNumericGreaterEqExpression(exp as NumericGreaterEqExpression);
                break;
            }
            case ExpressionTag.LogicAndExpression: {
                this.instantiateLogicAndExpression(exp as LogicAndExpression);
                break;
            }
            case ExpressionTag.LogicOrExpression: {
                this.instantiateLogicOrExpression(exp as LogicOrExpression);
                break;
            }
            case ExpressionTag.HoleExpression: {
                this.instantiateHoleExpression(exp as HoleExpression);
                break;
            }
            case ExpressionTag.MapEntryConstructorExpression: {
                this.instantiateMapEntryConstructorExpression(exp as MapEntryConstructorExpression);
                break;
            }
            default: {
                ; //handled by the type signature instantiation on exp type
            }
        }
    }

    private instantiateCallRefInvokeExpression(exp: CallRefInvokeExpression) {
        /*
        this.instantiateExpression(exp.rcvr);

        if(exp.specificResolve !== undefined) {
            this.instantiateTypeSignature(exp.specificResolve, this.currentMapping);
        }

        this.instantiateArgumentList(exp.args.args);

        for(let i = 0; i < exp.shuffleinfo.length; ++i) {
            this.instantiateTypeSignature(exp.shuffleinfo[i][1], this.currentMapping);
        }
        if(exp.restinfo !== undefined) {
            const rparamtype = (this.currentMapping !== undefined ? (exp.resttype as TypeSignature).remapTemplateBindings(this.currentMapping) : (exp.resttype as TypeSignature)) as NominalTypeSignature;
            let rargs: ArgumentValue[] = [];

            for(let i = 0; i < exp.restinfo.length; ++i) {
                this.instantiateTypeSignature(exp.restinfo[i][2], this.currentMapping);
                rargs.push(exp.args.args[exp.restinfo[i][0]]);
            }

            this.instantiateCollectionConstructor(rparamtype.decl as AbstractCollectionTypeDecl, rparamtype, rargs);
        }

        this.instantiateTypeSignature(exp.resolvedTrgt as TypeSignature, this.currentMapping);

        const nns = (exp.resolvedTrgt as NominalTypeSignature).decl.ns;
        const mm = (exp.resolvedTrgt as NominalTypeSignature).decl.methods.find((m) => m.isThisRef && m.name === exp.name) as MethodDecl;
        this.instantiateSpecificResolvedMemberMethod(nns, exp.resolvedTrgt as NominalTypeSignature, mm, exp.terms);
        */
         assert(false, "Not Implemented -- instantiateCallRefInvokeExpression");
    }

    private instantiateCallRefVariableExpression(exp: CallRefVariableExpression) {
        this.instantiateCallRefInvokeExpression(exp);
    }

    private instantiateCallRefThisExpression(exp: CallRefThisExpression) {
        this.instantiateCallRefInvokeExpression(exp);
    }

    private instantiateCallRefSelfExpression(exp: CallRefSelfExpression) {
        this.instantiateCallRefInvokeExpression(exp);
    }

    private instantiateCallTaskActionExpression(exp: CallTaskActionExpression) {
        assert(false, "Not Implemented -- instantiateCallTaskActionExpression");
    }

    private instantiateTaskRunExpression(exp: TaskRunExpression) {
        assert(false, "Not Implemented -- instantiateTaskRunExpression");
    }

    private instantiateTaskMultiExpression(exp: TaskMultiExpression) {
        assert(false, "Not Implemented -- instantiateTaskMultiExpression");
    }

    private instantiateTaskDashExpression(exp: TaskDashExpression) {
        assert(false, "Not Implemented -- instantiateTaskDashExpression");
    }

    private instantiateTaskAllExpression(exp: TaskAllExpression) {
        assert(false, "Not Implemented -- instantiateTaskAllExpression");
    }

    private instantiateTaskRaceExpression(exp: TaskRaceExpression) {
        assert(false, "Not Implemented -- instantiateTaskRaceExpression");
    }

    private instantiateAPIInvokeExpression(exp: APIInvokeExpression) {
        assert(false, "Not Implemented");
    }
    
    private instantiateAgentInvokeExpression(exp: AgentInvokeExpression) {
        assert(false, "Not Implemented");
    }

    private instantiateChkLogicExpression(exp: ChkLogicExpression) {
        if(exp.tag === ChkLogicExpressionTag.ChkLogicBaseExpression) {
            return this.instantiateExpression((exp as ChkLogicBaseExpression).exp);
        }
        else {
            const iiexp = exp as ChkLogicImpliesExpression;
            this.instantiateITestGuardSet(iiexp.lhs);
            this.instantiateExpression(iiexp.rhs);
        }
    }

    private instantiateConditionalValueExpression(exp: ConditionalValueExpression) {
        this.instantiateITestGuardSet(exp.guardset);

        this.instantiateExpression(exp.trueValue);
        this.instantiateExpression(exp.falseValue);
    }

    private instantiateBaseRValueExpression(exp: Expression) {
        const ttag = exp.tag;
        switch (ttag) {
            case ExpressionTag.CallRefVariableExpression: {
                this.instantiateCallRefVariableExpression(exp as CallRefVariableExpression);
                break;
            }
            case ExpressionTag.CallRefThisExpression: {
                this.instantiateCallRefThisExpression(exp as CallRefThisExpression);
                break;
            }
            case ExpressionTag.CallRefSelfExpression: {
                this.instantiateCallRefSelfExpression(exp as CallRefSelfExpression);
                break;
            }
            case ExpressionTag.CallTaskActionExpression: {
                this.instantiateCallTaskActionExpression(exp as CallTaskActionExpression);
                break;
            }
            case ExpressionTag.TaskRunExpression: {
                this.instantiateTaskRunExpression(exp as TaskRunExpression);
                break;
            }
            case ExpressionTag.TaskMultiExpression: {
                this.instantiateTaskMultiExpression(exp as TaskMultiExpression);
                break;
            }
            case ExpressionTag.TaskDashExpression: {
                this.instantiateTaskDashExpression(exp as TaskDashExpression);
                break;
            }
            case ExpressionTag.TaskAllExpression: {
                this.instantiateTaskAllExpression(exp as TaskAllExpression);
                break;
            }
            case ExpressionTag.TaskRaceExpression: {
                this.instantiateTaskRaceExpression(exp as TaskRaceExpression);
                break;
            }
            case ExpressionTag.APIInvokeExpression: {
                this.instantiateAPIInvokeExpression(exp as APIInvokeExpression);
                break;
            }
            case ExpressionTag.AgentInvokeExpression: {
                this.instantiateAgentInvokeExpression(exp as AgentInvokeExpression);
                break;
            }
            default: {
                this.instantiateExpression(exp);
                break;
            }
        }
    }

    private instantiateExpressionRHS(exp: RValueExpression) {
        const ttag = exp.tag;
        
        if(ttag === RValueExpressionTag.BaseExpression) {
            this.instantiateBaseRValueExpression((exp as BaseRValueExpression).exp);
        }
        else if(ttag === RValueExpressionTag.ShortCircuitAssignRHSExpressionFail) {
            assert(false, "Not Implemented -- checkShortCircuitAssignRHSFailExpression");
        }
        else if(ttag === RValueExpressionTag.ShortCircuitAssignRHSExpressionReturn) {
            assert(false, "Not Implemented -- checkShortCircuitAssignRHSReturnExpression");
        }
        else if(ttag === RValueExpressionTag.ConditionalValueExpression) {
            this.instantiateConditionalValueExpression(exp as ConditionalValueExpression);
        }
        else {
            assert(false, "Unknown RValueExpression kind");
        }

        this.instantiateTypeSignature(exp.rtype as TypeSignature, this.currentMapping);
    }

    private instantiateEmptyStatement(stmt: EmptyStatement) {
        return;
    }

    private instantiateVariableDeclarationStatement(stmt: VariableDeclarationStatement) {
        this.instantiateTypeSignature(stmt.vtype, this.currentMapping);
    }
    
    private instantiateVariableMultiDeclarationStatement(stmt: VariableMultiDeclarationStatement) {
        for(let i = 0; i < stmt.decls.length; ++i) {
            this.instantiateTypeSignature(stmt.decls[i].vtype, this.currentMapping);
        }
    }

    private instantiateVariableInitializationStatement(stmt: VariableInitializationStatement) {
        this.instantiateTypeSignature(stmt.actualtype as TypeSignature, this.currentMapping);
        this.instantiateExpressionRHS(stmt.exp);
    }

    private instantiateVariableMultiInitializationStatement(stmt: VariableMultiInitializationStatement) {
        /*
        for(let i = 0; i < stmt.decls.length; ++i) {
            if(!(stmt.decls[i].vtype instanceof AutoTypeSignature)) {
                this.instantiateTypeSignature(stmt.decls[i].vtype, this.currentMapping);
            }
            this.instantiateTypeSignature(stmt.actualtypes[i], this.currentMapping);
        }

        if(Array.isArray(stmt.exp)) {
            for(let i = 0; i < stmt.exp.length; ++i) {
                this.instantiateExpression(stmt.exp[i]); 
            }
        }
        else {
            this.instantiateExpressionRHS(stmt.exp);
        }
        */
       assert(false, "Not Implemented -- instantiateVariableMultiInitializationStatement");
    }

    private instantiateVariableAssignmentStatement(stmt: VariableAssignmentStatement) {
        /*
        this.instantiateExpressionRHS(stmt.exp);
        */
        assert(false, "Not Implemented -- instantiateVariableAssignmentStatement");
    }

    private instantiateVariableMultiAssignmentStatement(stmt: VariableMultiAssignmentStatement) {
        /*
        if(Array.isArray(stmt.exp)) {
            for(let i = 0; i < stmt.exp.length; ++i) {
                this.instantiateExpression(stmt.exp[i]); 
            }
        }
        else {
            this.instantiateExpressionRHS(stmt.exp);
        }
        */
        assert(false, "Not Implemented -- instantiateVariableMultiAssignmentStatement");
    }

    private instantiateReturnVoidStatement(stmt: ReturnVoidStatement) {
        return;
    }

    private instantiateReturnSingleStatement(stmt: ReturnSingleStatement) {
        this.instantiateExpressionRHS(stmt.value);
        this.instantiateTypeSignature(stmt.rtype as TypeSignature, this.currentMapping);
    }

    private instantiateReturnMultiStatement(stmt: ReturnMultiStatement) {
        /*
        for(let i = 0; i < stmt.value.length; ++i) {
            this.instantiateExpression(stmt.value[i]);
        }

        for(let i = 0; i < stmt.rtypes.length; ++i) {
           this.instantiateTypeSignature(stmt.rtypes[i], this.currentMapping);
        }

        this.instantiateTypeSignature(new EListTypeSignature(stmt.sinfo, stmt.rtypes), this.currentMapping);
        */
        assert(false, "Not Implemented -- instantiateReturnMultiStatement");
    }

    private instantiateIfStatement(stmt: IfStatement) {
        /*
        this.instantiateExpression(stmt.cond.exp);
        
        this.instantiateBlockStatement(stmt.trueBlock);

        if(stmt.cond.itestopt !== undefined) {
            this.processITestAsConvert(stmt.cond.exp.getType(), stmt.cond.itestopt);

            if(stmt.trueBindType !== undefined) {
                this.instantiateTypeSignature(stmt.trueBindType, this.currentMapping);
            }
        }
        */
        assert(false, "Not Implemented -- instantiateIfStatement");
    }

    private instantiateIfElseStatement(stmt: IfElseStatement) {
        /*
        this.instantiateExpression(stmt.cond.exp);

        this.instantiateBlockStatement(stmt.trueBlock);
        this.instantiateBlockStatement(stmt.falseBlock);

        if(stmt.cond.itestopt !== undefined) {
            this.processITestAsConvert(stmt.cond.exp.getType(), stmt.cond.itestopt);

            if(stmt.trueBindType !== undefined) {
                this.instantiateTypeSignature(stmt.trueBindType, this.currentMapping);
            }
            if(stmt.falseBindType !== undefined) {
                this.instantiateTypeSignature(stmt.falseBindType, this.currentMapping);
            }
        }
        */
        assert(false, "Not Implemented -- instantiateIfElseStatement");
    }

    private instantiateIfElifElseStatement(stmt: IfElifElseStatement) {
        /*
        for(let i = 0; i < stmt.condflow.length; ++i) {
            this.instantiateExpression(stmt.condflow[i].cond);
            this.instantiateBlockStatement(stmt.condflow[i].block);
        }

        this.instantiateBlockStatement(stmt.elseflow);
        */
        assert(false, "Not Implemented -- instantiateIfElifElseStatement");
    }

    private instantiateSwitchStatement(stmt: SwitchStatement) {
        /*
        this.instantiateExpression(stmt.sval);
        
        for (let i = 0; i < stmt.switchflow.length; ++i) {
            this.instantiateBlockStatement(stmt.switchflow[i].value);

            if(stmt.switchflow[i].lval !== undefined) {
                const slitexp = (stmt.switchflow[i].lval as LiteralExpressionValue).exp;
                this.instantiateExpression(slitexp);
            }
        }
        */
        assert(false, "Not Implemented -- instantiateSwitchStatement");
    }

    private instantiateMatchStatement(stmt: MatchStatement) {
        /*
        this.instantiateExpression(stmt.sval[0]);
        
        for(let i = 0; i < stmt.matchflow.length; ++i) {
            this.instantiateBlockStatement(stmt.matchflow[i].value);

            if(stmt.matchflow[i].mtype !== undefined) {
                const mtype = stmt.matchflow[i].mtype as TypeSignature;
                this.instantiateTypeSignature(mtype, this.currentMapping);
            }
        }

        if(stmt.implicitFinalType !== undefined) {
            this.instantiateTypeSignature(stmt.implicitFinalType, this.currentMapping);
        }
        */
        assert(false, "Not Implemented -- instantiateMatchStatement");
    }

    private instantiateDispatchPatternStatement(stmt: DispatchPatternStatement) {
        assert(false, "Not implemented -- DispatchPatternStatement");
    }
    
    private instantiateDispatchTaskStatement(stmt: DispatchTaskStatement) {
        assert(false, "Not implemented -- DispatchTaskStatement");
    }

    private instantiateAbortStatement(stmt: AbortStatement) {
        return;
    }

    private instantiateAssertStatement(stmt: AssertStatement) {
        this.instantiateChkLogicExpression(stmt.cond);
    }

    private instantiateValidateStatement(stmt: ValidateStatement) {
        this.instantiateChkLogicExpression(stmt.cond);
    }

    private instantiateDebugStatement(stmt: DebugStatement) {
        this.instantiateExpression(stmt.value);
    }

    private instantiateVoidRefCallStatement(stmt: VoidRefCallStatement) {
        this.instantiateExpression(stmt.exp);
    }

    private instantiateUpdateStatement(stmt: UpdateStatement) {
        this.instantiateExpression(stmt.vexp);
        
        for(let i = 0; i < stmt.updates.length; ++i) {
            this.instantiateExpression(stmt.updates[i][1]);
        }

        this.instantiateTypeSignature(stmt.updatetype as TypeSignature, this.currentMapping);

        for(let i = 0; i < stmt.updateinfo.length; ++i) {
            this.instantiateTypeSignature(stmt.updateinfo[i].fieldtype, this.currentMapping);
            this.instantiateTypeSignature(stmt.updateinfo[i].etype, this.currentMapping);
        }
    }

    private instantiateVarUpdateStatement(stmt: VarUpdateStatement) {
        this.instantiateUpdateStatement(stmt);
    }

    private instantiateThisUpdateStatement(stmt: ThisUpdateStatement) {
        this.instantiateUpdateStatement(stmt);
    }

    private instantiateSelfUpdateStatement(stmt: SelfUpdateStatement) {
        assert(false, "Not implemented -- SelfUpdateStatement");
    }

    private instantiateHoleStatement(stmt: HoleStatement) {
        assert(false, "Not implemented -- HoleStatement");
    }

    private instantiateTaskStatusStatement(stmt: TaskStatusStatement) {
        assert(false, "Not implemented -- TaskStatusStatement");
    }

    private instantiateTaskCheckAndHandleTerminationStatement(stmt: TaskCheckAndHandleTerminationStatement) {
        assert(false, "Not implemented -- TaskCheckAndHandleTerminationStatement");
    }

    private instantiateTaskYieldStatement(stmt: TaskYieldStatement) {
        assert(false, "Not implemented -- TaskYieldStatement");
    }

    private instantiateBlockStatement(stmt: BlockStatement) {
        for(let i = 0; i < stmt.statements.length; ++i) {
            this.instantiateStatement(stmt.statements[i]);
        }
    }

    private instantiateStatement(stmt: Statement) {
        switch(stmt.tag) {
            case StatementTag.EmptyStatement: {
                this.instantiateEmptyStatement(stmt as EmptyStatement);
                break;
            }
            case StatementTag.VariableDeclarationStatement: {
                this.instantiateVariableDeclarationStatement(stmt as VariableDeclarationStatement);
                break;
            }
            case StatementTag.VariableMultiDeclarationStatement: {
                this.instantiateVariableMultiDeclarationStatement(stmt as VariableMultiDeclarationStatement);
                break;
            }
            case StatementTag.VariableInitializationStatement: {
                this.instantiateVariableInitializationStatement(stmt as VariableInitializationStatement);
                break;
            }
            case StatementTag.VariableMultiInitializationStatement: {
                this.instantiateVariableMultiInitializationStatement(stmt as VariableMultiInitializationStatement);
                break;
            }
            case StatementTag.VariableAssignmentStatement: {
                this.instantiateVariableAssignmentStatement(stmt as VariableAssignmentStatement);
                break;
            }
            case StatementTag.VariableMultiAssignmentStatement: {
                this.instantiateVariableMultiAssignmentStatement(stmt as VariableMultiAssignmentStatement);
                break;
            }
            case StatementTag.ReturnVoidStatement: {
                this.instantiateReturnVoidStatement(stmt as ReturnVoidStatement);
                break;
            }
            case StatementTag.ReturnSingleStatement: {
                this.instantiateReturnSingleStatement(stmt as ReturnSingleStatement);
                break;
            }
            case StatementTag.ReturnMultiStatement: {
                this.instantiateReturnMultiStatement(stmt as ReturnMultiStatement);
                break;
            }
            case StatementTag.IfStatement: {
                this.instantiateIfStatement(stmt as IfStatement);
                break;
            }
            case StatementTag.IfElseStatement: {
                this.instantiateIfElseStatement(stmt as IfElseStatement);
                break;
            }
            case StatementTag.IfElifElseStatement: {
                this.instantiateIfElifElseStatement(stmt as IfElifElseStatement);
                break;
            }
            case StatementTag.SwitchStatement: {
                this.instantiateSwitchStatement(stmt as SwitchStatement);
                break;
            }
            case StatementTag.MatchStatement: {
                this.instantiateMatchStatement(stmt as MatchStatement);
                break;
            }
            case StatementTag.DispatchPatternStatement: {
                this.instantiateDispatchPatternStatement(stmt as DispatchPatternStatement);
                break;
            }
            case StatementTag.DispatchTaskStatement: {
                this.instantiateDispatchTaskStatement(stmt as DispatchTaskStatement);
                break;
            }
            case StatementTag.AbortStatement: {
                this.instantiateAbortStatement(stmt as AbortStatement);
                break;
            }
            case StatementTag.AssertStatement: {
                this.instantiateAssertStatement(stmt as AssertStatement);
                break;
            }
            case StatementTag.ValidateStatement: {
                this.instantiateValidateStatement(stmt as ValidateStatement);
                break;
            }
            case StatementTag.DebugStatement: {
                this.instantiateDebugStatement(stmt as DebugStatement);
                break;
            }
            case StatementTag.VoidRefCallStatement: {
                this.instantiateVoidRefCallStatement(stmt as VoidRefCallStatement);
                break;
            }
            case StatementTag.VarUpdateStatement: {
                this.instantiateVarUpdateStatement(stmt as VarUpdateStatement);
                break;
            }
            case StatementTag.ThisUpdateStatement: {
                this.instantiateThisUpdateStatement(stmt as ThisUpdateStatement);
                break;
            }
            case StatementTag.SelfUpdateStatement: {
                this.instantiateSelfUpdateStatement(stmt as SelfUpdateStatement);
                break;
            }
            case StatementTag.HoleStatement: {
                this.instantiateHoleStatement(stmt as HoleStatement);
                break;
            }
            case StatementTag.TaskStatusStatement: {
                this.instantiateTaskStatusStatement(stmt as TaskStatusStatement);
                break;
            }
            case StatementTag.TaskCheckAndHandleTerminationStatement: {
                this.instantiateTaskCheckAndHandleTerminationStatement(stmt as TaskCheckAndHandleTerminationStatement);
                break;
            }
            case StatementTag.TaskYieldStatement: {
                this.instantiateTaskYieldStatement(stmt as TaskYieldStatement);
                break;
            }
            case StatementTag.BlockStatement: {
                this.instantiateBlockStatement(stmt as BlockStatement);
                break;
            }
            default: {
                assert(false, `Unknown statement kind -- ${stmt.tag}`);
            }
        }
    }

    private instantiateBodyImplementation(body: BodyImplementation) {
        if((body instanceof AbstractBodyImplementation) || (body instanceof PredicateUFBodyImplementation) || (body instanceof BuiltinBodyImplementation)) {
            return;
        }

        if(body instanceof HoleBodyImplementation) {
            if(body.samplesfile !== undefined) {
                this.instantiateExpression(body.samplesfile);
            }
        }
        else if(body instanceof ExpressionBodyImplementation) {
            this.instantiateExpression(body.exp);
        }
        else {
            assert(body instanceof StandardBodyImplementation);
            
            for(let i = 0; i < body.statements.length; ++i) {
                this.instantiateStatement(body.statements[i]);
            }
        }
    }

    private instantiateRequires(requires: PreConditionDecl[]) {
        for(let i = 0; i < requires.length; ++i) {
            const precond = requires[i];
            this.instantiateChkLogicExpression(precond.exp);
        }
    }

    private instantiateEnsures(eventtype: TypeSignature | undefined, ensures: PostConditionDecl[]) {
        if(eventtype !== undefined) {
            this.instantiateTypeSignature(eventtype, this.currentMapping);
        }
        
        for(let i = 0; i < ensures.length; ++i) {
            const postcond = ensures[i];
            this.instantiateChkLogicExpression(postcond.exp);
        }
    }

    private instantiateInvariants(invariants: InvariantDecl[]) {
        for(let i = 0; i < invariants.length; ++i) {
            const inv = invariants[i];
            this.instantiateChkLogicExpression(inv.exp);
        }
    }

    private instantiateValidates(validates: ValidateDecl[]) {
        for(let i = 0; i < validates.length; ++i) {
            const validate = validates[i];
            this.instantiateChkLogicExpression(validate.exp);
        }
    }

    private instantiateExplicitInvokeDeclSignature(idecl: ExplicitInvokeDecl) {
        for(let i = 0; i < idecl.params.length; ++i) {
            const p = idecl.params[i];
            
            this.instantiateTypeSignature(p.type, this.currentMapping);
            if(p.optDefaultValue !== undefined) {
                this.instantiateExpression(p.optDefaultValue);
            }
        }

        this.instantiateTypeSignature(idecl.resultType, this.currentMapping);
    }

    private instantiateExplicitInvokeDeclMetaData(idecl: ExplicitInvokeDecl, eventtype: TypeSignature | undefined) {
        this.instantiateRequires(idecl.preconditions);
        this.instantiateEnsures(eventtype, idecl.postconditions);
    }

    private instantiateNamespaceFunctionDecl(ns: NamespaceDeclaration, fdecl: PendingNamespaceFunction) {
        this.instantiateNamespaceDeclaration(ns);

        this.currentMapping = undefined;
        if(fdecl.function.terms.length !== 0) {
            let tmap = new Map<string, TypeSignature>();
            fdecl.function.terms.forEach((t, ii) => {
                tmap.set(t.name, fdecl.instantiation[ii]);
            });

            this.currentMapping = TemplateNameMapper.createInitialMapping(tmap);
        }

        this.instantiateExplicitInvokeDeclSignature(fdecl.function);
        this.instantiateExplicitInvokeDeclMetaData(fdecl.function, undefined);

        this.instantiateBodyImplementation(fdecl.function.body);

        const cnns = this.currentNSInstantiation as NamespaceInstantiationInfo;
        const rkey = this.computeResolveKeyForInvoke(fdecl.function.name, fdecl.function.terms.length, fdecl.function.params.some((p) => p.pkind !== undefined), fdecl.function.params.some((p) => p.type instanceof LambdaTypeSignature));

        if(!cnns.functionbinds.has(rkey)) {
            cnns.functionbinds.set(rkey, []);
        }

        const ikey = this.computeInvokeKeyForNamespaceFunction(ns, fdecl.function, fdecl.instantiation, fdecl.lambdas);
        (cnns.functionbinds.get(rkey) as InvokeInstantiationInfo[]).push(new InvokeInstantiationInfo(ikey, this.currentMapping as TemplateNameMapper, fdecl.lambdas));

        this.currentMapping = undefined;
    }

    private instantiateTypeFunctionDecl(tdecl: AbstractNominalTypeDecl, fdecl: PendingTypeFunction) {
        const nskey = tdecl.ns.emit();
        this.currentNSInstantiation = this.instantiation.find((nsi) => nsi.ns.emit() === nskey);
        const typeinst = ((this.currentNSInstantiation as NamespaceInstantiationInfo).typebinds.get(tdecl.name) as TypeInstantiationInfo[]).find((ti) => ti.tkey === fdecl.type.tkeystr) as TypeInstantiationInfo;

        this.currentMapping = undefined;
        if(fdecl.function.terms.length === 0) {
            this.currentMapping = typeinst.binds;
        }
        else {
            let tmap = new Map<string, TypeSignature>();
            fdecl.function.terms.forEach((t, ii) => {
                tmap.set(t.name, fdecl.instantiation[ii])
            });

            this.currentMapping = TemplateNameMapper.tryMerge(typeinst.binds, TemplateNameMapper.createInitialMapping(tmap));
        }

        this.instantiateExplicitInvokeDeclSignature(fdecl.function);
        this.instantiateExplicitInvokeDeclMetaData(fdecl.function, undefined);

        this.instantiateBodyImplementation(fdecl.function.body);

        const rkey = this.computeResolveKeyForInvoke(fdecl.function.name, fdecl.function.terms.length, fdecl.function.params.some((p) => p.pkind !== undefined), fdecl.function.params.some((p) => p.type instanceof LambdaTypeSignature));

        if(!typeinst.functionbinds.has(rkey)) {
            typeinst.functionbinds.set(rkey, []);
        }

        const ikey = this.computeInvokeKeyForTypeFunction(fdecl.type, fdecl.function, fdecl.instantiation, fdecl.lambdas);
        (typeinst.functionbinds.get(rkey) as InvokeInstantiationInfo[]).push(new InvokeInstantiationInfo(ikey, this.currentMapping as TemplateNameMapper, fdecl.lambdas));

        this.currentMapping = undefined;
    }

    private instantiateMethodDecl(tdecl: AbstractNominalTypeDecl, mdecl: PendingTypeMethod) {
        /*
        const nskey = tdecl.ns.emit();
        this.currentNSInstantiation = this.instantiation.find((nsi) => nsi.ns.emit() === nskey);
        const typeinst = ((this.currentNSInstantiation as NamespaceInstantiationInfo).typebinds.get(tdecl.name) as TypeInstantiationInfo[]).find((ti) => ti.tkey === mdecl.type.tkeystr) as TypeInstantiationInfo;

        this.currentMapping = undefined;
        if(mdecl.method.terms.length === 0) {
            this.currentMapping = typeinst.binds;
        }
        else {
            let tmap = new Map<string, TypeSignature>();
            mdecl.method.terms.forEach((t, ii) => {
                tmap.set(t.name, mdecl.instantiation[ii])
            });

            this.currentMapping = TemplateNameMapper.tryMerge(typeinst.binds, TemplateNameMapper.createInitialMapping(tmap));
        }

        this.instantiateExplicitInvokeDeclSignature(mdecl.method);
        this.instantiateExplicitInvokeDeclMetaData(mdecl.method, undefined);

        this.instantiateBodyImplementation(mdecl.method.body);

        if(!typeinst.methodbinds.has(mdecl.method.name)) {
            typeinst.methodbinds.set(mdecl.method.name, new MethodInstantiationInfo(mdecl.method.terms.length !== 0 ? [] : undefined));
        }

        if(mdecl.method.terms.length !== 0) {
            ((typeinst.methodbinds.get(mdecl.method.name) as MethodInstantiationInfo).binds as TemplateNameMapper[]).push(this.currentMapping as TemplateNameMapper);
        }

        this.currentMapping = undefined;
        */
        assert(false, "Not implemented -- instantiateMethodDecl");
    }

    private instantiateTaskMethodDecl(tdecl: AbstractNominalTypeDecl, mdecl: PendingTypeMethod) {
        assert(false, "Not implemented -- instantiateTaskMethodDecl");
    }

    private instantiateTaskActionDecl(tdecl: AbstractNominalTypeDecl, mdecl: PendingTypeMethod) {
        assert(false, "Not implemented -- instantiateTaskActionDecl");
    }

    private instantiateConstMemberDecls(tdecl: AbstractNominalTypeDecl, mdecls: ConstMemberDecl[]) {
        for(let i = 0; i < mdecls.length; ++i) {
            const m = mdecls[i];

            this.instantiateTypeSignature(m.declaredType, this.currentMapping);
            this.instantiateExpression(m.value);
        }
    }

    private instantiateMemberFieldDecls(fdecls: MemberFieldDecl[]) {
        for(let i = 0; i < fdecls.length; ++i) {
            const f = fdecls[i];
            
            this.instantiateTypeSignature(f.declaredType, this.currentMapping);
            if(f.defaultValue !== undefined) {
                this.instantiateExpression(f.defaultValue);
            }
        }
    }

    private instantiateProvides(provides: TypeSignature[]) {
        for(let i = 0; i < provides.length; ++i) {
            const p = provides[i];
            this.instantiateTypeSignature(p, this.currentMapping);
        }
    }

    private instantiateAbstractNominalTypeDeclHelper(pdecl: PendingNominalTypeDecl, terms: string[], optfdecls: MemberFieldDecl[] | undefined, optreqtypes: TypeSignature[] | undefined) {
        this.currentMapping = undefined;
        if(terms.length !== 0) {
            let tmap = new Map<string, TypeSignature>();
            terms.forEach((t, ii) => {
                tmap.set(t, pdecl.instantiation[ii])
            });

            this.currentMapping = TemplateNameMapper.createInitialMapping(tmap)
        }

        this.instantiateProvides(pdecl.type.provides);

        if(optreqtypes !== undefined) {
            for(let i = 0; i < optreqtypes.length; ++i) {
                this.instantiateTypeSignature(optreqtypes[i], this.currentMapping);
            }
        }

        //make sure all of the invariants on this typecheck
        this.instantiateInvariants(pdecl.type.invariants);
        this.instantiateValidates(pdecl.type.validates);
        
        this.instantiateConstMemberDecls(pdecl.type, pdecl.type.consts);

        if(optfdecls !== undefined) {
            this.instantiateMemberFieldDecls(optfdecls);
        }

        const cnns = this.currentNSInstantiation as NamespaceInstantiationInfo;
        if(!cnns.typebinds.has(pdecl.type.name)) {
            cnns.typebinds.set(pdecl.type.name, []);
        }
        const bbl = cnns.typebinds.get(pdecl.type.name) as TypeInstantiationInfo[];

        if(terms.length === 0) {
            bbl.push(new TypeInstantiationInfo(pdecl.tkey, pdecl.tsig, undefined, new Map<string, InvokeInstantiationInfo[]>(), new Map<string, InvokeInstantiationInfo[]>()));
        }
        else {
            bbl.push(new TypeInstantiationInfo(pdecl.tkey, pdecl.tsig, this.currentMapping as TemplateNameMapper, new Map<string, InvokeInstantiationInfo[]>(), new Map<string, InvokeInstantiationInfo[]>()));
            this.currentMapping = undefined;
        }
    }

    private instantiateEnumTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateAbstractNominalTypeDeclHelper(pdecl, [], undefined, undefined);
    }

    private instantiateTypedeclTypeDecl(tdecl: TypedeclTypeDecl, pdecl: PendingNominalTypeDecl) {
        this.instantiateAbstractNominalTypeDeclHelper(pdecl, [], undefined, [tdecl.valuetype]);

        if(tdecl.optofexp !== undefined) {
            this.instantiateExpression(tdecl.optofexp);
        }
    }

    private instantiateInteralSimpleTypeDeclHelper(pdecl: PendingNominalTypeDecl, terms: string[], optreqtypes: TypeSignature[] | undefined) {
        this.instantiateAbstractNominalTypeDeclHelper(pdecl, terms, undefined, optreqtypes);
    }

    private instantiatePrimitiveEntityTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, [], undefined);
    }

    private instantiateOkTypeDecl(pdecl: PendingNominalTypeDecl) {
        const stypes = [
            new NominalTypeSignature(pdecl.type.sinfo, undefined, this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Result") as ResultTypeDecl, pdecl.instantiation),
        ];
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T", "E"], stypes)
    }

    private instantiateFailTypeDecl(pdecl: PendingNominalTypeDecl) {
        const stypes = [
            new NominalTypeSignature(pdecl.type.sinfo, undefined, this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Result") as ResultTypeDecl, pdecl.instantiation),
        ];
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T", "E"], stypes);
    }

    private instantiateAPIErrorTypeDecl(pdecl: PendingNominalTypeDecl) {
        const stypes = [
            new NominalTypeSignature(pdecl.type.sinfo, undefined, this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "APIResult") as ResultTypeDecl, pdecl.instantiation),
        ];
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T", "E"], stypes);
    }

    private instantiateAPIRejectedTypeDecl(pdecl: PendingNominalTypeDecl) {
        const stypes = [
            new NominalTypeSignature(pdecl.type.sinfo, undefined, this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "APIResult") as ResultTypeDecl, pdecl.instantiation),
        ];
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T", "E"], stypes);
    }

    private instantiateAPIDeniedTypeDecl(pdecl: PendingNominalTypeDecl) {
        const stypes = [
            new NominalTypeSignature(pdecl.type.sinfo, undefined, this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "APIResult") as ResultTypeDecl, pdecl.instantiation),
        ];
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T", "E"], stypes);
    }

    private instantiateAPIFlaggedTypeDecl(pdecl: PendingNominalTypeDecl) {
        const stypes = [
            new NominalTypeSignature(pdecl.type.sinfo, undefined, this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "APIResult") as ResultTypeDecl, pdecl.instantiation),
        ];
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T", "E"], stypes);
    }

    private instantiateAPISuccessTypeDecl(pdecl: PendingNominalTypeDecl) {
        const stypes = [
            new NominalTypeSignature(pdecl.type.sinfo, undefined, this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "APIResult") as ResultTypeDecl, pdecl.instantiation),
        ];
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T", "E"], stypes);
    }

    private instantiateSomeTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T"], undefined);
    }

    private instantiateMapEntryTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["K", "V"], undefined);
    }

    private instantiateListTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T"], undefined);
    }

    private instantiateStackTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T"], undefined);
    }

    private instantiateQueueTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T"], undefined);
    }

    private instantiateSetTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T"], undefined);
    }

    private instantiateMapTypeDecl(tdecl: MapTypeDecl, pdecl: PendingNominalTypeDecl) {
        const metype = [
            new NominalTypeSignature(tdecl.sinfo, undefined, this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "MapEntry") as MapEntryTypeDecl, pdecl.instantiation)
        ];
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["K", "V"],  metype);
    }

    private instantiateEventListTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T"], undefined);
    }

    private instantiateEntityTypeDecl(tdecl: EntityTypeDecl, pdecl: PendingNominalTypeDecl) {
        this.instantiateAbstractNominalTypeDeclHelper(pdecl, tdecl.terms.map((tt) => tt.name), tdecl.fields, undefined);
    }

    private instantiateOptionTypeDecl(tdecl: OptionTypeDecl, pdecl: PendingNominalTypeDecl) {
        const stypes = [
            this.getWellKnownType("None"),
            new NominalTypeSignature(tdecl.sinfo, undefined, this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Some") as SomeTypeDecl, pdecl.instantiation)
        ];
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T"], stypes);
    }

    private instantiateResultTypeDecl(tdecl: ResultTypeDecl, pdecl: PendingNominalTypeDecl) {
        const stypes = [
            new NominalTypeSignature(tdecl.sinfo, undefined, tdecl.nestedEntityDecls[0], pdecl.instantiation),
            new NominalTypeSignature(tdecl.sinfo, undefined, tdecl.nestedEntityDecls[1], pdecl.instantiation)
        ];
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T", "E"], stypes);
    }

    private instantiateAPIResultTypeDecl(tdecl: APIResultTypeDecl, pdecl: PendingNominalTypeDecl) {
        const stypes = [
            new NominalTypeSignature(tdecl.sinfo, undefined, tdecl.nestedEntityDecls[0], pdecl.instantiation),
            new NominalTypeSignature(tdecl.sinfo, undefined, tdecl.nestedEntityDecls[1], pdecl.instantiation),
            new NominalTypeSignature(tdecl.sinfo, undefined, tdecl.nestedEntityDecls[2], pdecl.instantiation),
            new NominalTypeSignature(tdecl.sinfo, undefined, tdecl.nestedEntityDecls[3], pdecl.instantiation),
            new NominalTypeSignature(tdecl.sinfo, undefined, tdecl.nestedEntityDecls[4], pdecl.instantiation)
        ];
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T", "E"], stypes);
    }

    private instantiateConceptTypeDecl(tdecl: ConceptTypeDecl, pdecl: PendingNominalTypeDecl) {
        this.instantiateAbstractNominalTypeDeclHelper(pdecl, tdecl.terms.map((tt) => tt.name), tdecl.fields, undefined);
    }

    private instantiateDatatypeMemberEntityTypeDecl(tdecl: DatatypeMemberEntityTypeDecl, pdecl: PendingNominalTypeDecl) {
        this.instantiateAbstractNominalTypeDeclHelper(pdecl, tdecl.terms.map((tt) => tt.name), tdecl.fields, undefined);
    }

    private instantiateDatatypeTypeDecl(tdecl: DatatypeTypeDecl, pdecl: PendingNominalTypeDecl) {
        const stypes = tdecl.associatedMemberEntityDecls.map((dd) => new NominalTypeSignature(tdecl.sinfo, undefined, dd, pdecl.instantiation));
        
        this.instantiateAbstractNominalTypeDeclHelper(pdecl, tdecl.terms.map((tt) => tt.name), tdecl.fields, stypes);
    }

    private instantiateConfigsurationParameters(tconfig: TaskConfiguration) {
        assert(false, "Not implemented -- instantiateEnvironmentVariableInformation");
    }

    private instantiatestatusinfo(status: TypeSignature[]) {
        assert(false, "Not implemented -- instantiateStatusInformation");
    }

    private instantiateenvreqs(envreqs: EnvironmentVariableInformation[]) {
        assert(false, "Not implemented -- instantiateEnvironmentRequirements");
    }

    private instantiateresourcereqs(resourcereqs: ResourceInformation) {
        assert(false, "Not implemented -- instantiateResourceRequirements");
    }

    private instantiateeventinfo(eventinfo: TypeSignature[]) {
        assert(false, "Not implemented -- instantiateEventInformation");
    }

    private instantiateAPIDecl(adecl: APIDecl) {
        assert(false, "Not implemented -- checkAPIDecl");
    }

    private instantiateAgentDecl(adecl: AgentDecl) {
        assert(false, "Not implemented -- checkAgentDecl");
    }

    private instantiateTaskDecl(tdecl: TaskDecl, pdecl: PendingNominalTypeDecl) {
        this.currentMapping = undefined;
        if(tdecl.terms.length !== 0) {
            let tmap = new Map<string, TypeSignature>();
            tdecl.terms.forEach((t, ii) => {
                tmap.set(tdecl.name, pdecl.instantiation[ii])
            });

            this.currentMapping = TemplateNameMapper.createInitialMapping(tmap)
        }

        this.instantiateProvides(pdecl.type.provides);

        //make sure all of the invariants on this typecheck
        this.instantiateInvariants(pdecl.type.invariants);
        this.instantiateValidates(pdecl.type.validates);
        
        this.instantiateConstMemberDecls(pdecl.type, pdecl.type.consts);

        this.instantiateMemberFieldDecls(tdecl.fields);

        this.instantiateConfigsurationParameters(tdecl.configs);

        this.instantiatestatusinfo(tdecl.statusinfo);
        this.instantiateenvreqs(tdecl.envreqs);
        this.instantiateresourcereqs(tdecl.resourcereqs);
        this.instantiateeventinfo(tdecl.eventinfo);

        const cnns = this.currentNSInstantiation as NamespaceInstantiationInfo;
        if(!cnns.typebinds.has(pdecl.type.name)) {
            cnns.typebinds.set(pdecl.type.name, []);
        }
        const bbl = cnns.typebinds.get(pdecl.type.name) as TypeInstantiationInfo[];

        if(tdecl.terms.length === 0) {
            bbl.push(new TypeInstantiationInfo(pdecl.tkey, pdecl.tsig, undefined, new Map<string, InvokeInstantiationInfo[]>(), new Map<string, InvokeInstantiationInfo[]>()));
        }
        else {
            bbl.push(new TypeInstantiationInfo(pdecl.tkey, pdecl.tsig, this.currentMapping as TemplateNameMapper, new Map<string, InvokeInstantiationInfo[]>(), new Map<string, InvokeInstantiationInfo[]>()));
            this.currentMapping = undefined;
        }
    }

    private instantiateNamespaceConstDecls(cdecls: NamespaceConstDecl[]) {
        for(let i = 0; i < cdecls.length; ++i) {
            const m = cdecls[i];

            this.instantiateTypeSignature(m.declaredType, this.currentMapping);
            this.instantiateExpression(m.value);
        }
    }

    private instantiateNamespaceTypeDecl(ns: NamespaceDeclaration, pdecl: PendingNominalTypeDecl) {
        this.instantiateNamespaceDeclaration(ns);

        const tt = pdecl.type;
        if(tt instanceof EnumTypeDecl) {
            this.instantiateEnumTypeDecl(pdecl);
        }
        else if(tt instanceof TypedeclTypeDecl) {
            this.instantiateTypedeclTypeDecl(tt, pdecl);
        }
        else if(tt instanceof PrimitiveEntityTypeDecl) {
            this.instantiatePrimitiveEntityTypeDecl(pdecl);
        }
        else if(tt instanceof OkTypeDecl) {
            this.instantiateOkTypeDecl(pdecl);
        }
        else if(tt instanceof FailTypeDecl) {
            this.instantiateFailTypeDecl(pdecl);
        }
        else if(tt instanceof APIErrorTypeDecl) {
            this.instantiateAPIErrorTypeDecl(pdecl);
        }
        else if(tt instanceof APIRejectedTypeDecl) {
            this.instantiateAPIRejectedTypeDecl(pdecl);
        }
        else if(tt instanceof APIDeniedTypeDecl) {
            this.instantiateAPIDeniedTypeDecl(pdecl);
        }
        else if(tt instanceof APIFlaggedTypeDecl) {
            this.instantiateAPIFlaggedTypeDecl(pdecl);
        }
        else if(tt instanceof APISuccessTypeDecl) {
            this.instantiateAPISuccessTypeDecl(pdecl);
        }
        else if(tt instanceof SomeTypeDecl) {
            this.instantiateSomeTypeDecl(pdecl);
        }
        else if(tt instanceof MapEntryTypeDecl) {
            this.instantiateMapEntryTypeDecl(pdecl);
        }
        else if(tt instanceof ListTypeDecl) {
            this.instantiateListTypeDecl(pdecl);
        }
        else if(tt instanceof StackTypeDecl) {
            this.instantiateStackTypeDecl(pdecl);
        }
        else if(tt instanceof QueueTypeDecl) {
            this.instantiateQueueTypeDecl(pdecl);
        }
        else if(tt instanceof SetTypeDecl) {
            this.instantiateSetTypeDecl(pdecl);
        }
        else if(tt instanceof MapTypeDecl) {
            this.instantiateMapTypeDecl(tt, pdecl);
        }
        else if(tt instanceof EventListTypeDecl) {
            this.instantiateEventListTypeDecl(pdecl);
        }
        else if(tt instanceof EntityTypeDecl) {
            this.instantiateEntityTypeDecl(tt, pdecl);
        }
        else if(tt instanceof OptionTypeDecl) {
            this.instantiateOptionTypeDecl(tt, pdecl);
        }
        else if(tt instanceof ResultTypeDecl) {
            this.instantiateResultTypeDecl(tt, pdecl);
        }
        else if(tt instanceof APIResultTypeDecl) {
            this.instantiateAPIResultTypeDecl(tt, pdecl);
        }
        else if(tt instanceof ConceptTypeDecl) {
            this.instantiateConceptTypeDecl(tt, pdecl);

            if(tt.terms.length === 0) {
                const ttsig = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), undefined, tt, []);
                const ntpt = ns.typedecls.filter((tt) => tt.terms.length === 0 && tt.saturatedProvides.some((sp) => sp.tkeystr === ttsig.tkeystr));
                
                for(let i = 0; i < ntpt.length; ++i) {
                    const nnsig = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), undefined, ntpt[i], []);
                    this.instantiateTypeSignature(nnsig, undefined);
                }
            }
        }
        else if(tt instanceof DatatypeMemberEntityTypeDecl) {
            this.instantiateDatatypeMemberEntityTypeDecl(tt, pdecl);
        }
        else if(tt instanceof DatatypeTypeDecl) {
            this.instantiateDatatypeTypeDecl(tt, pdecl);
        }
        else {
            assert(false, "Unknown type decl kind");
        }
    }

    private instantiateNamespaceDeclaration(decl: NamespaceDeclaration) {
        const nskey = decl.fullnamespace.emit();
        const nns = this.instantiation.find((nsi) => nsi.ns.emit() === nskey);
        if(nns !== undefined) {
            this.currentNSInstantiation = nns;
        }
        else {
            this.currentNSInstantiation = new NamespaceInstantiationInfo(decl.fullnamespace);
            this.instantiation.push(this.currentNSInstantiation);

            this.instantiateNamespaceConstDecls(decl.consts);
        }
    }

    private shouldInstantiateAsRootType(tdecl: AbstractNominalTypeDecl): boolean {
        return tdecl.terms.length === 0 && tdecl.attributes.find((attr) => attr.name === "public") !== undefined; 
    }

    private shouldInstantiateAsRootInvoke(idecl: NamespaceFunctionDecl): boolean {
        return idecl.terms.length === 0 && idecl.attributes.find((attr) => attr.name === "public") !== undefined; 
    }

    private instantiateRootNamespaceDeclaration(decl: NamespaceDeclaration) {
        this.instantiateNamespaceConstDecls(decl.consts);

        for(let i = 0; i < decl.functions.length; ++i) {
            if(this.shouldInstantiateAsRootInvoke(decl.functions[i])) {
                const ikey = this.computeInvokeKeyForNamespaceFunction(decl, decl.functions[i], [], []);
                this.pendingNamespaceFunctions.push(new PendingNamespaceFunction(decl, decl.functions[i], [], [], ikey));
            }
        }

        for(let i = 0; i < decl.typedecls.length; ++i) {
            if(this.shouldInstantiateAsRootType(decl.typedecls[i])) {
                const tsig = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), undefined, decl.typedecls[i], []);
                this.pendingNominalTypeDecls.push(new PendingNominalTypeDecl(tsig.tkeystr, tsig, decl.typedecls[i], []));
            }
        }

        for(let i = 0; i < decl.apis.length; ++i) {
            this.instantiateAPIDecl(decl.apis[i]);
        }

        for(let i = 0; i < decl.agents.length; ++i) {
            this.instantiateAgentDecl(decl.agents[i]);
        }

        for(let i = 0; i < decl.tasks.length; ++i) {
            if(this.shouldInstantiateAsRootType(decl.typedecls[i])) {
                const tsig = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), undefined, decl.typedecls[i], []);
                this.pendingNominalTypeDecls.push(new PendingNominalTypeDecl(tsig.tkeystr, tsig, decl.typedecls[i], []));
            }
        }

        for(let i = 0; i < decl.subns.length; ++i) {
            this.instantiateRootNamespaceDeclaration(decl.subns[i]);
        }
    }

    private shouldInstantiateAsRootInvokeForTest(idecl: NamespaceFunctionDecl): boolean {
        return idecl.terms.length === 0 && (idecl.fkind === "chktest" || idecl.fkind === "errtest" || idecl.fkind === "example");
    }

    private instantiateRootNamespaceDeclarationForTest(decl: NamespaceDeclaration) {
        for(let i = 0; i < decl.functions.length; ++i) {
            if(this.shouldInstantiateAsRootInvokeForTest(decl.functions[i])) {
                const ikey = this.computeInvokeKeyForNamespaceFunction(decl, decl.functions[i], [], []);
                this.pendingNamespaceFunctions.push(new PendingNamespaceFunction(decl, decl.functions[i], [], [], ikey));
            }
        }

        for(let i = 0; i < decl.subns.length; ++i) {
            this.instantiateRootNamespaceDeclarationForTest(decl.subns[i]);
        }
    }

    private hasPendingWork(): boolean {
        if(this.pendingNominalTypeDecls.length !== 0) {
            return true;
        }
        
        return this.pendingNamespaceFunctions.length !== 0 || this.pendingTypeFunctions.length !== 0 || this.pendingTypeMethods.length !== 0;
    }

    private static loadWellKnownType(assembly: Assembly, name: string, wellknownTypes: Map<string, TypeSignature>) {
        const ccore = assembly.getCoreNamespace();

        const tdecl = ccore.typedecls.find((td) => td.name === name);
        assert(tdecl !== undefined, "Failed to find well known type");

        wellknownTypes.set(name, new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []));
    }

    static computeInstantiations(assembly: Assembly, istesting: boolean, roonts: string[]): NamespaceInstantiationInfo[] {
        let wellknownTypes = new Map<string, TypeSignature>();
        wellknownTypes.set("Void", new VoidTypeSignature(SourceInfo.implicitSourceInfo()));

        Monomorphizer.loadWellKnownType(assembly, "None", wellknownTypes);
        Monomorphizer.loadWellKnownType(assembly, "Some", wellknownTypes);
        Monomorphizer.loadWellKnownType(assembly, "Bool", wellknownTypes);
        Monomorphizer.loadWellKnownType(assembly, "Int", wellknownTypes);
        Monomorphizer.loadWellKnownType(assembly, "Nat", wellknownTypes);
        Monomorphizer.loadWellKnownType(assembly, "ChkInt", wellknownTypes);
        Monomorphizer.loadWellKnownType(assembly, "ChkNat", wellknownTypes);
        Monomorphizer.loadWellKnownType(assembly, "Rational", wellknownTypes);
        Monomorphizer.loadWellKnownType(assembly, "Float", wellknownTypes);
        Monomorphizer.loadWellKnownType(assembly, "Decimal", wellknownTypes);
        Monomorphizer.loadWellKnownType(assembly, "DecimalDegree", wellknownTypes);
        Monomorphizer.loadWellKnownType(assembly, "LatLongCoordinate", wellknownTypes);
        Monomorphizer.loadWellKnownType(assembly, "Complex", wellknownTypes);

        Monomorphizer.loadWellKnownType(assembly, "String", wellknownTypes);
        Monomorphizer.loadWellKnownType(assembly, "CString", wellknownTypes);

        Monomorphizer.loadWellKnownType(assembly, "Regex", wellknownTypes);
        Monomorphizer.loadWellKnownType(assembly, "CRegex", wellknownTypes);

        let iim = new Monomorphizer(assembly, wellknownTypes);
        iim.instantiateTypeSignature(iim.getWellKnownType("None"), undefined);
        iim.instantiateTypeSignature(iim.getWellKnownType("Bool"), undefined);

        if(!istesting) {
            for(let i = 0; i < roonts.length; ++i) {
                const ns = assembly.getToplevelNamespace(roonts[i]) as NamespaceDeclaration;
                iim.instantiateRootNamespaceDeclaration(ns);
            }
        }
        else {
            for(let i = 0; i < roonts.length; ++i) {
                const ns = assembly.getToplevelNamespace(roonts[i]) as NamespaceDeclaration;
                iim.instantiateRootNamespaceDeclarationForTest(ns);
            }
        }

        while(iim.hasPendingWork()) {
            if(iim.pendingNominalTypeDecls.length !== 0) {
                const ntd = iim.pendingNominalTypeDecls[0];
                const ns = assembly.resolveNamespaceDecl(ntd.type.ns.ns) as NamespaceDeclaration;
                if(ntd.type instanceof TaskDecl) {
                    iim.instantiateTaskDecl(ntd.type as TaskDecl, ntd);
                }
                else {
                    iim.instantiateNamespaceTypeDecl(ns, ntd);
                }

                iim.completedInstantiations.add(ntd.tkey);
                iim.pendingNominalTypeDecls.shift();
            }
            else {
                if(iim.pendingNamespaceFunctions.length !== 0) {
                    const nfd = iim.pendingNamespaceFunctions[0];
                    iim.instantiateNamespaceFunctionDecl(nfd.namespace, nfd);

                    iim.completedNamespaceFunctions.add(nfd.fkey);
                    iim.pendingNamespaceFunctions.shift();
                }
                else if(iim.pendingTypeFunctions.length !== 0) {
                    const tfd = iim.pendingTypeFunctions[0];
                    iim.instantiateTypeFunctionDecl((tfd.type as NominalTypeSignature).decl, tfd);

                    iim.completedTypeFunctions.add(tfd.fkey);
                    iim.pendingTypeFunctions.shift();
                }
                else {
                    const tmd = iim.pendingTypeMethods[0];
                    if(tmd.method instanceof TaskMethodDecl) {
                        iim.instantiateTaskMethodDecl((tmd.type as NominalTypeSignature).decl, tmd);
                    }
                    else if(tmd.method instanceof TaskActionDecl) {
                        iim.instantiateTaskActionDecl((tmd.type as NominalTypeSignature).decl, tmd);
                    }
                    else {
                        iim.instantiateMethodDecl((tmd.type as NominalTypeSignature).decl, tmd);
                    }

                    iim.completedMemberMethods.add(tmd.mkey);
                    iim.pendingTypeMethods.shift();
                }
            }
        }

        return iim.instantiation;
    }

    static computeExecutableInstantiations(assembly: Assembly, roonts: string[]): NamespaceInstantiationInfo[] {
        return Monomorphizer.computeInstantiations(assembly, false, roonts);

    }

    static computeTestInstantiations(assembly: Assembly, roonts: string[]): NamespaceInstantiationInfo[] {
        return Monomorphizer.computeInstantiations(assembly, true, roonts);
    }
}

export { 
    Monomorphizer
};