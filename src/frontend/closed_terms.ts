import assert from "node:assert";

import { AbstractNominalTypeDecl, Assembly, NamespaceDeclaration, NamespaceFunctionDecl, TypeFunctionDecl } from "./assembly.js";
import { FunctionInstantiationInfo, NamespaceInstantiationInfo } from "./instantiation_map.js";
import { EListTypeSignature, LambdaTypeSignature, NominalTypeSignature, TemplateNameMapper, TypeSignature } from "./type.js";
import { AccessEnumExpression, AccessEnvValueExpression, AccessStaticFieldExpression, ArgumentValue, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndExpression, BinLogicIFFExpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, CallNamespaceFunctionExpression, CallRefSelfExpression, CallRefThisExpression, CallTaskActionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, EmptyStatement, Expression, ExpressionTag, IfElifElseStatement, IfElseStatement, IfExpression, IfStatement, ITest, ITestType, LambdaInvokeExpression, LetExpression, LiteralTypeDeclValueExpression, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixLiteralKeyAccess, PostfixOp, PostfixOpTag, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, ReturnMultiStatement, ReturnSingleStatement, ReturnVoidStatement, SpecialConstructorExpression, SpecialConverterExpression, Statement, StatementTag, TaskAccessInfoExpression, TaskAllExpression, TaskDashExpression, TaskMultiExpression, TaskRaceExpression, TaskRunExpression, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VariableRetypeStatement } from "./body.js";

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

    private instantiateArgumentList(args: ArgumentValue[]) {
        args.forEach((arg) => this.instantiateExpression(arg.exp));
    }

    private instantiateConstructorArgumentList(args: ArgumentValue[]) {
        args.forEach((arg) => this.instantiateExpression(arg.exp));
    }

    private instantiateLiteralTypeDeclValueExpression(exp: LiteralTypeDeclValueExpression) {
        this.instantiateTypeSignature(exp.constype, this.currentMapping);
        this.instantiateExpression(exp.value);
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
        this.instantiateExpression(exp.arg);
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
        this.processITestAsBoolean(exp.getRcvrType(), exp.ttest);
    }

    private instantiatePostfixAsConvert(exp: PostfixAsConvert) {
        this.processITestAsConvert(exp.getRcvrType(), exp.ttest);
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

    private instantiateBinaryBooleanArgs(lhs: Expression, rhs: Expression) {
        this.instantiateExpression(lhs);
        this.instantiateExpression(rhs);
    }

    private instantiateBinLogicAndExpression(exp: BinLogicAndExpression) {
        this.instantiateBinaryBooleanArgs(exp.lhs, exp.rhs);
    }

    private instantiateBinLogicOrExpression(exp: BinLogicOrExpression) {
        this.instantiateBinaryBooleanArgs(exp.lhs, exp.rhs);
    }

    private instantiateBinLogicImpliesExpression(exp: BinLogicImpliesExpression) {
        this.instantiateBinaryBooleanArgs(exp.lhs, exp.rhs);
    }

    private instantiateBinLogicIFFExpression(exp: BinLogicIFFExpression) {
        this.instantiateBinaryBooleanArgs(exp.lhs, exp.rhs);
    }

    private instantiateMapEntryConstructorExpression(exp: MapEntryConstructorExpression) {
        assert(false, "Not Implemented -- instantiateMapEntryConstructorExpression");
    }

    private instantiateIfExpression(exp: IfExpression) {
        this.instantiateExpression(exp.test.exp);

        this.instantiateExpression(exp.trueValue);
        this.instantiateExpression(exp.falseValue);

        if(exp.test.itestopt !== undefined) {
            this.processITestAsConvert(exp.test.exp.getType(), exp.test.itestopt);
        }
    }

    private instantiateExpression(exp: Expression) {
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
            case ExpressionTag.BinLogicAndExpression: {
                this.instantiateBinLogicAndExpression(exp as BinLogicAndExpression);
                break;
            }
            case ExpressionTag.BinLogicOrExpression: {
                this.instantiateBinLogicOrExpression(exp as BinLogicOrExpression);
                break;
            }
            case ExpressionTag.BinLogicImpliesExpression: {
                this.instantiateBinLogicImpliesExpression(exp as BinLogicImpliesExpression);
                break;
            }
            case ExpressionTag.BinLogicIFFExpression: {
                this.instantiateBinLogicIFFExpression(exp as BinLogicIFFExpression);
                break;
            }
            case ExpressionTag.MapEntryConstructorExpression: {
                this.instantiateMapEntryConstructorExpression(exp as MapEntryConstructorExpression);
                break;
            }
            case ExpressionTag.IfExpression: {
                this.instantiateIfExpression(exp as IfExpression);
                break;
            }
            default: {
                ; //handled by the type signature instantiation on exp type
            }
        }
    }

    private instantiateCallRefThisExpression(exp: CallRefThisExpression) {
        assert(false, "Not Implemented -- instantiateCallRefThisExpression");
    }

    private instantiateCallRefSelfExpression(exp: CallRefSelfExpression) {
        assert(false, "Not Implemented -- instantiateCallRefSelfExpression");
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

    private instantiateExpressionRHS(exp: Expression) {
        const ttag = exp.tag;
        switch (ttag) {
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
            default: {
                this.instantiateExpression(exp);
                break;
            }
        }
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
        this.instantiateTypeSignature(stmt.vtype, this.currentMapping);
        this.instantiateExpressionRHS(stmt.exp);
    }

    private instantiateVariableMultiInitializationStatement(stmt: VariableMultiInitializationStatement) {
        for(let i = 0; i < stmt.decls.length; ++i) {
            this.instantiateTypeSignature(stmt.decls[i].vtype, this.currentMapping);
        }

        if(Array.isArray(stmt.exp)) {
            for(let i = 0; i < stmt.exp.length; ++i) {
                this.instantiateExpression(stmt.exp[i]); 
            }
        }
        else {
            this.instantiateExpressionRHS(stmt.exp);
        }
    }

    private instantiateVariableAssignmentStatement(stmt: VariableAssignmentStatement) {
        this.instantiateExpressionRHS(stmt.exp);
    }

    private instantiateVariableMultiAssignmentStatement(stmt: VariableMultiAssignmentStatement) {
        if(Array.isArray(stmt.exp)) {
            for(let i = 0; i < stmt.exp.length; ++i) {
                this.instantiateExpression(stmt.exp[i]); 
            }
        }
        else {
            this.instantiateExpressionRHS(stmt.exp);
        }
    }

    private instantiateVariableRetypeStatement(stmt: VariableRetypeStatement) {
        this.processITestAsConvert(stmt.vtype as TypeSignature, stmt.ttest);
        this.instantiateTypeSignature(stmt.newvtype as TypeSignature, this.currentMapping);
    }

    private instantiateReturnVoidStatement(stmt: ReturnVoidStatement) {
        return;
    }

    private instantiateReturnSingleStatement(stmt: ReturnSingleStatement) {
        this.instantiateExpressionRHS(stmt.value);
    }

    private instantiateReturnMultiStatement(stmt: ReturnMultiStatement) {
        for(let i = 0; i < stmt.value.length; ++i) {
            this.instantiateExpression(stmt.value[i]);
        }
    }

    private instantiateIfStatement(stmt: IfStatement) {
        this.instantiateExpression(stmt.cond.exp);
        
        this.instantiateBlockStatement(stmt.trueBlock);

        if(stmt.cond.itestopt !== undefined) {
            const splits = this.processITestAsConvert(stmt.sinfo, env, eetype, stmt.cond.itestopt);
            this.checkError(stmt.sinfo, splits.ttrue === undefined, "Test is never true -- true branch of if is unreachable");
            this.checkError(stmt.sinfo, splits.tfalse === undefined, "Test is never false -- false branch of if is unreachable");

            if(stmt.binder === undefined) {
                const ttrue = this.checkBlockStatement(env, stmt.trueBlock);
                return TypeEnvironment.mergeEnvironmentsSimple(env, ttrue);
            }
            else {
                stmt.binder.scopename = env.getBindScopeName(stmt.binder.srcname);
                stmt.binder.origtype = eetype;

                const nenv = env.pushNewLocalBinderScope(stmt.binder.srcname, stmt.binder.scopename, splits.ttrue || eetype);
                const ttrue = this.checkStatement(nenv, stmt.trueBlock).popLocalScope();

                const lubtype = ttrue.normalflow ? eetype : splits.tfalse;
                this.checkFlowRebinder(stmt.sinfo, stmt.binder, env);
                this.setFlowRebinderInfo(stmt.binder, stmt.binder.srcname.slice(1), lubtype || eetype);

                return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, lubtype, env, ttrue);
            }
        }
    }

    private instantiateIfElseStatement(stmt: IfElseStatement) {
        this.instantiateExpression(stmt.cond.exp);

        this.instantiateBlockStatement(stmt.trueBlock);
        this.instantiateBlockStatement(stmt.falseBlock);

        if(stmt.cond.itestopt !== undefined) {
            const splits = this.processITestAsConvert(stmt.sinfo, env, eetype, stmt.cond.itestopt);
            this.checkError(stmt.sinfo, splits.ttrue === undefined, "Test is never true -- true branch of if is unreachable");
            this.checkError(stmt.sinfo, splits.tfalse === undefined, "Test is never false -- false branch of if is unreachable");

            if(stmt.binder === undefined) {
                const ttrue = this.checkBlockStatement(env, stmt.trueBlock);
                const tfalse = this.checkBlockStatement(env, stmt.falseBlock);
                return TypeEnvironment.mergeEnvironmentsSimple(ttrue, tfalse);
            }
            else {
                stmt.binder.scopename = env.getBindScopeName(stmt.binder.srcname);
                stmt.binder.origtype = eetype;

                const tenv = env.pushNewLocalBinderScope(stmt.binder.srcname, stmt.binder.scopename, splits.ttrue || eetype);
                const ttrue = this.checkStatement(tenv, stmt.trueBlock).popLocalScope();

                const fenv = env.pushNewLocalBinderScope(stmt.binder.srcname, stmt.binder.scopename, splits.tfalse || eetype);
                const tfalse = this.checkStatement(fenv, stmt.falseBlock).popLocalScope();

                this.checkFlowRebinder(stmt.sinfo, stmt.binder, env);
                if(ttrue.normalflow && tfalse.normalflow) {
                    this.setFlowRebinderInfo(stmt.binder, stmt.binder.srcname.slice(1), eetype);
                    return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, eetype, ttrue, tfalse);
                }
                else if(ttrue.normalflow) {
                    this.setFlowRebinderInfo(stmt.binder, stmt.binder.srcname.slice(1), splits.ttrue as TypeSignature);
                    return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, splits.ttrue as TypeSignature, ttrue, tfalse);
                }
                else if(tfalse.normalflow) {
                    this.setFlowRebinderInfo(stmt.binder, stmt.binder.srcname.slice(1), splits.tfalse as TypeSignature);
                    return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, splits.tfalse as TypeSignature, ttrue, tfalse);
                }
                else {
                    this.setFlowRebinderInfo(stmt.binder, stmt.binder.srcname.slice(1), eetype);
                    return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, eetype, ttrue, tfalse);
                }
            }
        }
    }

    private instantiateIfElifElseStatement(stmt: IfElifElseStatement) {
        for(let i = 0; i < stmt.condflow.length; ++i) {
            this.instantiateExpression(stmt.condflow[i].cond);
            this.instantiateBlockStatement(stmt.condflow[i].block);
        }

        this.instantiateBlockStatement(stmt.elseflow);
    }

    private instantiateSwitchStatement(stmt: SwitchStatement) {
        let ctype = this.checkExpression(env, stmt.sval, undefined);
        
        let exhaustive = false;
        let results: TypeEnvironment[] = [];

        this.checkError(stmt.sinfo, stmt.switchflow.length < 2, "Switch statement must have 2 or more choices");

        for (let i = 0; i < stmt.switchflow.length && !exhaustive; ++i) {
            //it is a wildcard match
            if(stmt.switchflow[i].lval === undefined) {
                this.checkError(stmt.sinfo, i !== stmt.switchflow.length - 1, `wildcard should be last option in switch expression but there were ${stmt.switchflow.length - (i + 1)} more that are unreachable`);
                exhaustive = true;

                const cenv = this.checkBlockStatement(env, stmt.switchflow[i].value);
                results.push(cenv);
            }
            else {
                const slitexp = (stmt.switchflow[i].lval as LiteralExpressionValue).exp;
                const littype = this.checkExpression(env, slitexp, undefined);
                if(!this.relations.isKeyType(littype, this.constraints)) {
                    this.reportError(slitexp.sinfo, `Switch statement requires a unique key type but got ${littype.tkeystr}`);
                }
                else {
                    const cmpok = this.checkValueEq(stmt.sval, ctype, slitexp, littype);
                    this.checkError(slitexp.sinfo, cmpok === "err", `Cannot compare arguments in switch statement ${littype.tkeystr}`);
                }

                const cenv = this.checkBlockStatement(env, stmt.switchflow[i].value);
                results.push(cenv);
            }
        }
        this.checkError(stmt.sinfo, !exhaustive, "Switch statement must be exhaustive or have a wildcard match at the end");
        
        return TypeEnvironment.mergeEnvironmentsSimple(env, ...results);
    }

    private instantiateMatchStatement(stmt: MatchStatement) {
        const eetype = this.checkExpression(env, stmt.sval[0], undefined);
        let ctype = this.relations.decomposeType(eetype) || [];
        if(ctype.length === 0) {
            this.reportError(stmt.sval[0].sinfo, `Match statement requires a decomposable type but got ${eetype.tkeystr}`);
            return env;
        }
        
        let exhaustive = false;
        let results: TypeEnvironment[] = [];

        if(stmt.sval[1] !== undefined) {
            stmt.sval[1].scopename = env.getBindScopeName(stmt.sval[1].srcname);
        }

        this.checkError(stmt.sinfo, stmt.matchflow.length < 2, "Switch statement must have 2 or more choices");

        for (let i = 0; i < stmt.matchflow.length && !exhaustive; ++i) {
            //it is a wildcard match
            if(stmt.matchflow[i].mtype === undefined) {
                this.checkError(stmt.sinfo, i !== stmt.matchflow.length - 1, `wildcard should be last option in switch expression but there were ${stmt.matchflow.length - (i + 1)} more that are unreachable`);
                exhaustive = true;

                let cenv = env;
                if(stmt.sval[1] !== undefined) {
                    const lubattempt = this.relations.flowTypeLUB(stmt.matchflow[i].value.sinfo, eetype, ctype, this.constraints);
                    const defaulttype = (lubattempt instanceof ErrorTypeSignature) ? eetype : lubattempt;

                    cenv = env.pushNewLocalBinderScope(stmt.sval[1].srcname, stmt.sval[1].scopename, defaulttype)
                }
                cenv = this.checkBlockStatement(env, stmt.matchflow[i].value);

                if(stmt.sval[1] !== undefined) {
                    cenv = cenv.popLocalScope();
                }
                results.push(cenv);
            }
            else {
                const mtype = stmt.matchflow[i].mtype as TypeSignature;
                this.checkTypeSignature(mtype);

                const splits = this.relations.refineMatchType(ctype, mtype, this.constraints);
                if(splits === undefined) {
                    this.reportError(stmt.sinfo, `Match statement requires a type that is a subtype of the decomposed type but got ${mtype.tkeystr}`);
                    return env;
                }
                else {
                    this.checkError(stmt.sinfo, splits.overlap.length === 0, "Test is never true -- true branch of if is unreachable");

                    exhaustive = splits.remain.length === 0;
                    this.checkError(stmt.sinfo, exhaustive && i !== stmt.matchflow.length - 1, `Test is never false -- but there were ${stmt.matchflow.length - (i + 1)} more that are unreachable`);

                    let cenv = env;
                    if(stmt.sval[1] !== undefined) {
                        cenv = env.pushNewLocalBinderScope(stmt.sval[1].srcname, stmt.sval[1].scopename, mtype);
                    }
                    cenv = this.checkBlockStatement(env, stmt.matchflow[i].value);

                    if(stmt.sval[1] !== undefined) {
                        cenv = cenv.popLocalScope();
                    }
                    ctype = splits.remain || ctype;
                    results.push(cenv);
                }
            }
        }
        this.checkError(stmt.sinfo, !exhaustive, "Match statement must be exhaustive or have a wildcard match at the end");
        
        return TypeEnvironment.mergeEnvironmentsSimple(env, ...results);
    }

    private instantiateAbortStatement(stmt: AbortStatement) {
        return env.setDeadFlow();
    }

    private instantiateAssertStatement(stmt: AssertStatement) {
        const etype = this.checkExpression(env, stmt.cond, undefined);
        if(etype instanceof ErrorTypeSignature) {
            return env;
        }

        this.checkError(stmt.sinfo, !this.isBooleanType(etype), `Expected a boolean type for assert condition but got ${etype.tkeystr}`);
        return env;
    }

    private instantiateValidateStatement(stmt: ValidateStatement) {
        const etype = this.checkExpression(env, stmt.cond, undefined);
        if(etype instanceof ErrorTypeSignature) {
            return env;
        }

        this.checkError(stmt.sinfo, !this.isBooleanType(etype), `Expected a boolean type for validate condition but got ${etype.tkeystr}`);
        return env;
    }

    private instantiateDebugStatement(stmt: DebugStatement) {
        this.checkExpression(env, stmt.value, undefined);

        return env;
    }

    private instantiateVoidRefCallStatement(stmt: VoidRefCallStatement) {
        assert(false, "Not implemented -- VoidRefCallStatement");
    }

    private instantiateVarUpdateStatement(stmt: VarUpdateStatement) {
        assert(false, "Not implemented -- VarUpdateStatement");
    }

    private instantiateThisUpdateStatement(stmt: ThisUpdateStatement) {
        assert(false, "Not implemented -- ThisUpdateStatement");
    }

    private instantiateSelfUpdateStatement(stmt: SelfUpdateStatement) {
        assert(false, "Not implemented -- SelfUpdateStatement");
    }

    private instantiateEnvironmentUpdateStatement(stmt: EnvironmentUpdateStatement) {
        assert(false, "Not implemented -- EnvironmentUpdateStatement");
    }

    private instantiateEnvironmentBracketStatement(stmt: EnvironmentBracketStatement) {
        assert(false, "Not implemented -- EnvironmentBracketStatement");
    }

    private instantiateTaskStatusStatement(stmt: TaskStatusStatement) {
        assert(false, "Not implemented -- TaskStatusStatement");
    }

    private instantiateTaskEventEmitStatement(stmt: TaskEventEmitStatement) {
        assert(false, "Not implemented -- TaskEventEmitStatement");
    }

    private instantiateTaskYieldStatement(stmt: TaskYieldStatement) {
        assert(false, "Not implemented -- TaskYieldStatement");
    }

    private instantiateBlockStatement(stmt: BlockStatement) {
        let cenv = env;

        if(stmt.isScoping) {
            cenv = cenv.pushNewLocalScope();
            for (let i = 0; i < stmt.statements.length; ++i) {
                cenv = this.checkStatement(cenv, stmt.statements[i]);
            }
            cenv = cenv.popLocalScope();
        }
        else {
            for (let i = 0; i < stmt.statements.length; ++i) {
                cenv = this.checkStatement(cenv, stmt.statements[i]);
            }
        }

        return env;
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
            case StatementTag.VariableRetypeStatement: {
                this.instantiateVariableRetypeStatement(stmt as VariableRetypeStatement);
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
            case StatementTag.EnvironmentUpdateStatement: {
                this.instantiateEnvironmentUpdateStatement(stmt as EnvironmentUpdateStatement);
                break;
            }
            case StatementTag.EnvironmentBracketStatement: {
                this.instantiateEnvironmentBracketStatement(stmt as EnvironmentBracketStatement);
                break;
            }
            case StatementTag.TaskStatusStatement: {
                this.instantiateTaskStatusStatement(stmt as TaskStatusStatement);
                break;
            }
            case StatementTag.TaskEventEmitStatement: {
                this.instantiateTaskEventEmitStatement(stmt as TaskEventEmitStatement);
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

    static computeInstantiations(assembly: Assembly): AssemblyInstantiationInfo {

        xxxx;
    }
}

export { 
    InstantiationPropagator
};