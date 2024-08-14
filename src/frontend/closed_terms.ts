import assert from "node:assert";

import { AbstractNominalTypeDecl, APIDecl, APIErrorTypeDecl, APIFailedTypeDecl, APIRejectedTypeDecl, APIResultTypeDecl, APISuccessTypeDecl, Assembly, ConceptTypeDecl, ConstMemberDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, EntityTypeDecl, EnumTypeDecl, EnvironmentVariableInformation, ErrTypeDecl, EventListTypeDecl, ExplicitInvokeDecl, InternalEntityTypeDecl, InvariantDecl, InvokeExample, InvokeExampleDeclFile, InvokeExampleDeclInline, ListTypeDecl, MapEntryTypeDecl, MapTypeDecl, MemberFieldDecl, MethodDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, OkTypeDecl, OptionTypeDecl, PostConditionDecl, PreConditionDecl, PrimitiveEntityTypeDecl, QueueTypeDecl, ResourceInformation, ResultTypeDecl, SetTypeDecl, SomeTypeDecl, StackTypeDecl, TaskActionDecl, TaskDecl, TaskMethodDecl, TypedeclTypeDecl, TypeFunctionDecl, ValidateDecl } from "./assembly.js";
import { FunctionInstantiationInfo, NamespaceInstantiationInfo } from "./instantiation_map.js";
import { EListTypeSignature, LambdaTypeSignature, NominalTypeSignature, TemplateNameMapper, TypeSignature } from "./type.js";
import { AbortStatement, AbstractBodyImplementation, AccessEnumExpression, AccessEnvValueExpression, AccessStaticFieldExpression, ArgumentValue, AssertStatement, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndExpression, BinLogicIFFExpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, BlockStatement, BodyImplementation, BuiltinBodyImplementation, CallNamespaceFunctionExpression, CallRefSelfExpression, CallRefThisExpression, CallTaskActionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, DebugStatement, EmptyStatement, EnvironmentBracketStatement, EnvironmentUpdateStatement, Expression, ExpressionBodyImplementation, ExpressionTag, IfElifElseStatement, IfElseStatement, IfExpression, IfStatement, ITest, ITestType, LambdaInvokeExpression, LetExpression, LiteralExpressionValue, LiteralTypeDeclValueExpression, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, MatchStatement, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixLiteralKeyAccess, PostfixOp, PostfixOpTag, PredicateUFBodyImplementation, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, ReturnMultiStatement, ReturnSingleStatement, ReturnVoidStatement, SelfUpdateStatement, SpecialConstructorExpression, SpecialConverterExpression, StandardBodyImplementation, Statement, StatementTag, SwitchStatement, SynthesisBodyImplementation, TaskAccessInfoExpression, TaskAllExpression, TaskDashExpression, TaskEventEmitStatement, TaskMultiExpression, TaskRaceExpression, TaskRunExpression, TaskStatusStatement, TaskYieldStatement, ThisUpdateStatement, ValidateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VariableRetypeStatement, VarUpdateStatement, VoidRefCallStatement } from "./body.js";

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
            this.processITestAsConvert(stmt.cond.exp.getType(), stmt.cond.itestopt);

            if(stmt.binder !== undefined && stmt.binder.refinefollowtype !== undefined) {
                this.instantiateTypeSignature(stmt.binder.refinefollowtype, this.currentMapping);
            }
        }
    }

    private instantiateIfElseStatement(stmt: IfElseStatement) {
        this.instantiateExpression(stmt.cond.exp);

        this.instantiateBlockStatement(stmt.trueBlock);
        this.instantiateBlockStatement(stmt.falseBlock);

        if(stmt.cond.itestopt !== undefined) {
            this.processITestAsConvert(stmt.cond.exp.getType(), stmt.cond.itestopt);

            if(stmt.binder !== undefined && stmt.binder.refinefollowtype !== undefined) {
                this.instantiateTypeSignature(stmt.binder.refinefollowtype, this.currentMapping);
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
        this.instantiateExpression(stmt.sval);
        
        for (let i = 0; i < stmt.switchflow.length; ++i) {
            this.instantiateBlockStatement(stmt.switchflow[i].value);

            if(stmt.switchflow[i].lval !== undefined) {
                const slitexp = (stmt.switchflow[i].lval as LiteralExpressionValue).exp;
                this.instantiateExpression(slitexp);
            }
        }
    }

    private instantiateMatchStatement(stmt: MatchStatement) {
        this.instantiateExpression(stmt.sval[0]);
        
        for(let i = 0; i < stmt.matchflow.length; ++i) {
            this.instantiateBlockStatement(stmt.matchflow[i].value);

            if(stmt.matchflow[i].mtype !== undefined) {
                const mtype = stmt.matchflow[i].mtype as TypeSignature;
                this.instantiateTypeSignature(mtype, this.currentMapping);
            }
        }
    }

    private instantiateAbortStatement(stmt: AbortStatement) {
        return;
    }

    private instantiateAssertStatement(stmt: AssertStatement) {
        this.instantiateExpression(stmt.cond);
    }

    private instantiateValidateStatement(stmt: ValidateStatement) {
        this.instantiateExpression(stmt.cond);
    }

    private instantiateDebugStatement(stmt: DebugStatement) {
        this.instantiateExpression(stmt.value);
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

    private instantiateBodyImplementation(body: BodyImplementation) {
        if(body instanceof AbstractBodyImplementation || body instanceof PredicateUFBodyImplementation || body instanceof BuiltinBodyImplementation || body instanceof SynthesisBodyImplementation) {
            return;
        }

        if(body instanceof ExpressionBodyImplementation) {
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
            this.instantiateExpression(precond.exp);
        }
    }

    private instantiateEnsures(eventtype: TypeSignature | undefined, ensures: PostConditionDecl[]) {
        if(eventtype !== undefined) {
            this.instantiateTypeSignature(eventtype, this.currentMapping);
        }
        
        for(let i = 0; i < ensures.length; ++i) {
            const postcond = ensures[i];
            this.instantiateExpression(postcond.exp);
        }
    }

    private instantiateInvariants(invariants: InvariantDecl[]) {
        for(let i = 0; i < invariants.length; ++i) {
            const inv = invariants[i];
            this.instantiateExpression(inv.exp.exp);
        }
    }

    private instantiateValidates(validates: ValidateDecl[]) {
        for(let i = 0; i < validates.length; ++i) {
            const validate = validates[i];
            this.instantiateExpression(validate.exp.exp);
        }
    }

    private instantiateExamplesInline(args: TypeSignature[], resulttype: TypeSignature, example: InvokeExampleDeclInline) {
        assert(false, "This should be checked as a BSQON value"); //maybe in a secondary pass
    }

    private instantiateExamplesFiles(args: TypeSignature[], resulttype: TypeSignature, example: InvokeExampleDeclFile) {
        assert(false, "Not implemented -- checkExamplesFiles"); //We probably don't want to load the contents here -- but maybe as a separate pass????
    }

    private instantiateExamples(args: TypeSignature[], resulttype: TypeSignature, examples: InvokeExample[]) {
        for(let j = 0; j < args.length; ++j) {
            this.instantiateTypeSignature(args[j], this.currentMapping);
        }
        this.instantiateTypeSignature(resulttype, this.currentMapping);

        for(let i = 0; i < examples.length; ++i) {
            const ex = examples[i];
            if(ex instanceof InvokeExampleDeclInline) {
                this.instantiateExamplesInline(args, resulttype, ex);
            }
            else {
                assert(ex instanceof InvokeExampleDeclFile);
                this.instantiateExamplesFiles(args, resulttype, ex);
            }
        }
    }

    private instantiateExplicitInvokeDeclSignature(idecl: ExplicitInvokeDecl) {
        for(let i = 0; i < idecl.params.length; ++i) {
            const p = idecl.params[i];
            
            this.instantiateTypeSignature(p.type, this.currentMapping);
            if(p.optDefaultValue !== undefined) {
                this.instantiateExpression(p.optDefaultValue.exp);
            }
        }

        this.instantiateTypeSignature(idecl.resultType, this.currentMapping);
    }

    private instantiateExplicitInvokeDeclMetaData(idecl: ExplicitInvokeDecl, eventtype: TypeSignature | undefined) {
        this.instantiateRequires(idecl.preconditions);
        this.instantiateEnsures(eventtype, idecl.postconditions);

        this.instantiateExamples(idecl.params.map((p) => p.type), idecl.resultType, idecl.examples);
    }

    private instantiateNamespaceFunctionDecl(fdecl: PendingNamespaceFunction) {
        this.currentMapping = undefined;
        if(fdecl.function.terms.length !== 0) {
            let tmap = new Map<string, TypeSignature>();
            fdecl.function.terms.forEach((t, ii) => {
                tmap.set(t.name, fdecl.instantiation[ii])
            });

            this.currentMapping = new TemplateNameMapper([tmap])
        }

        this.instantiateExplicitInvokeDeclSignature(fdecl.function);
        this.instantiateExplicitInvokeDeclMetaData(fdecl.function, undefined);

        this.instantiateBodyImplementation(fdecl.function.body);
    }

    private instantiateTypeFunctionDecl(tdecl: AbstractNominalTypeDecl, fdecl: TypeFunctionDecl) {
        assert(false, "Not implemented -- instantiateTypeFunctionDecl");
    }

    private instantiateMethodDecls(tdecl: AbstractNominalTypeDecl, rcvr: TypeSignature, mdecl: MethodDecl) { 
        assert(false, "Not implemented -- instantiateMethodDecl");
    }

    private instantiateTaskMethodDecls(tdecl: AbstractNominalTypeDecl, rcvr: TypeSignature, mdecl: TaskMethodDecl) {
        assert(false, "Not implemented -- instantiateTaskMethodDecl");
    }

    private instantiateTaskActionDecls(tdecl: AbstractNominalTypeDecl, rcvr: TypeSignature, mdecl: TaskActionDecl) {
        assert(false, "Not implemented -- instantiateTaskActionDecl");
    }

    private instantiateConstMemberDecls(tdecl: AbstractNominalTypeDecl, mdecls: ConstMemberDecl[]) {
        for(let i = 0; i < mdecls.length; ++i) {
            const m = mdecls[i];

            this.instantiateTypeSignature(m.declaredType, this.currentMapping);
            this.instantiateExpression(m.value.exp);
        }
    }

    private instantiateMemberFieldDecls(fdecls: MemberFieldDecl[]) {
        for(let i = 0; i < fdecls.length; ++i) {
            const f = fdecls[i];
            
            this.instantiateTypeSignature(f.declaredType, this.currentMapping);
            if(f.defaultValue !== undefined) {
                this.instantiateExpression(f.defaultValue.exp);
            }
        }
    }

    private instantiateProvides(provides: TypeSignature[]) {
        for(let i = 0; i < provides.length; ++i) {
            const p = provides[i];
            this.instantiateTypeSignature(p, this.currentMapping);
        }
    }

    private instantiateAbstractNominalTypeDeclHelper(pdecl: PendingNominalTypeDecl, rcvr: TypeSignature, optfdecls: MemberFieldDecl[] | undefined) {
        this.file = tdecl.file;
        this.checkTemplateTypesOnType(tdecl.sinfo, tdecl.terms);

        if(tdecl.terms.length !== 0) {
            this.constraints.pushConstraintScope(tdecl.terms);
        }

        this.checkProvides(tdecl.provides);
        tdecl.saturatedProvides = this.relations.resolveTransitiveProvidesDecls(rcvr, this.constraints).map((tli) => tli.tsig.remapTemplateBindings(tli.mapping));
        tdecl.saturatedBFieldInfo = bnames;

        //make sure all of the invariants on this typecheck
        this.checkInvariants(bnames, tdecl.invariants);
        this.checkValidates(bnames, tdecl.validates);
        
        this.checkConstMemberDecls(tdecl, tdecl.consts);
        this.checkTypeFunctionDecls(tdecl, tdecl.functions);
        this.checkMethodDecls(tdecl, rcvr, tdecl.methods);

        if(optfdecls !== undefined) {
            this.checkMemberFieldDecls(bnames, optfdecls);
        }

        this.checkAbstractNominalTypeDeclVCallAndInheritance(tdecl, optfdecls, isentity);

        if(tdecl.terms.length !== 0) {
            this.constraints.popConstraintScope();
        }
        this.file = CLEAR_FILENAME;
    }

    private instantiateEnumTypeDecl(ns: NamespaceDeclaration, tdecl: EnumTypeDecl) {
        this.file = tdecl.file;
        this.checkError(tdecl.sinfo, tdecl.terms.length !== 0, "Enums cannot have template terms");
        
        this.checkProvides(tdecl.provides);
 
        //Make sure that any provides types are not adding on fields, consts, or functions
        const etype = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        const providesdecls = this.relations.resolveTransitiveProvidesDecls(etype, this.constraints);
        for(let i = 0; i < providesdecls.length; ++i) {
            const pdecl = providesdecls[i];
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).fields.length !== 0, `Provides type cannot have member fields -- ${pdecl.tsig.decl.name}`);
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).invariants.length !== 0 || (pdecl.tsig.decl as ConceptTypeDecl).validates.length !== 0, `Provides type cannot have invariants -- ${pdecl.tsig.decl.name}`);
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).consts.length !== 0, `Provides type cannot have consts -- ${pdecl.tsig.decl.name}`);
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).functions.length !== 0, `Provides type cannot have functions -- ${pdecl.tsig.decl.name}`);
        }

        this.checkError(tdecl.sinfo, tdecl.invariants.length !== 0 || tdecl.validates.length !== 0, "Enums cannot have invariants");

        this.checkError(tdecl.sinfo, tdecl.consts.length !== 0, "Enums cannot have consts");
        this.checkError(tdecl.sinfo, tdecl.functions.length !== 0, "Enums cannot have functions");

        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        this.checkMethodDecls(tdecl, rcvr, tdecl.methods);

        this.checkAbstractNominalTypeDeclVCallAndInheritance(tdecl, [], true);

        let opts = new Set<string>();
        for(let i = 0; i < tdecl.members.length; ++i) {
            this.checkError(tdecl.sinfo, opts.has(tdecl.members[i]), `Duplicate enum option ${tdecl.members[i]}`);
            opts.add(tdecl.members[i]);
        }
        this.file = CLEAR_FILENAME;
    }

    private instantiateTypedeclTypeDecl(ns: NamespaceDeclaration, tdecl: TypedeclTypeDecl) {
        this.file = tdecl.file;
        this.checkTemplateTypesOnType(tdecl.sinfo, tdecl.terms);

        if(tdecl.terms.length !== 0) {
            this.constraints.pushConstraintScope(tdecl.terms);
        }

        this.checkProvides(tdecl.provides);

        //Make sure that any provides types are not adding on fields!
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const providesdecls = this.relations.resolveTransitiveProvidesDecls(rcvr, this.constraints);
        for(let i = 0; i < providesdecls.length; ++i) {
            const pdecl = providesdecls[i];
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).fields.length !== 0, `Provides type cannot have member fields -- ${pdecl.tsig.decl.name}`);
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).invariants.length !== 0 || (pdecl.tsig.decl as ConceptTypeDecl).validates.length !== 0, `Provides type cannot have invariants -- ${pdecl.tsig.decl.name}`);
        }

        if(this.checkTypeSignature(tdecl.valuetype)) {
            //make sure the base type is typedeclable
            this.checkError(tdecl.sinfo, this.relations.isTypedeclableType(tdecl.valuetype), `Base type is not typedeclable -- ${tdecl.valuetype.tkeystr}`);

            //make sure all of the invariants on this typecheck
            this.checkInvariants([{name: "value", type: tdecl.valuetype}], tdecl.invariants);
            this.checkValidates([{name: "value", type: tdecl.valuetype}], tdecl.validates);
        }
        
        this.checkConstMemberDecls(tdecl, tdecl.consts);
        this.checkTypeFunctionDecls(tdecl, tdecl.functions);

        this.checkMethodDecls(tdecl, rcvr, tdecl.methods);
        this.checkAbstractNominalTypeDeclVCallAndInheritance(tdecl, [], true);

        if(tdecl.terms.length !== 0) {
            this.constraints.popConstraintScope();
        }
        this.file = CLEAR_FILENAME;
    }

    private instantiateInteralSimpleTypeDeclHelper(ns: NamespaceDeclaration, tdecl: InternalEntityTypeDecl, isentity: boolean) {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        this.checkAbstractNominalTypeDeclHelper([], rcvr, tdecl, undefined, isentity);
    }

    private instantiatePrimitiveEntityTypeDecl(ns: NamespaceDeclaration, tdecl: PrimitiveEntityTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private instantiateOkTypeDecl(ns: NamespaceDeclaration, tdecl: OkTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true)
    }

    private instantiateErrTypeDecl(ns: NamespaceDeclaration, tdecl: ErrTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private instantiateAPIRejectedTypeDecl(ns: NamespaceDeclaration, tdecl: APIRejectedTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private instantiateAPIFailedTypeDecl(ns: NamespaceDeclaration, tdecl: APIFailedTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private instantiateAPIErrorTypeDecl(ns: NamespaceDeclaration, tdecl: APIErrorTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private instantiateAPISuccessTypeDecl(ns: NamespaceDeclaration, tdecl: APISuccessTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private instantiateSomeTypeDecl(ns: NamespaceDeclaration, tdecl: SomeTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private instantiateMapEntryTypeDecl(ns: NamespaceDeclaration, tdecl: MapEntryTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private instantiateListTypeDecl(ns: NamespaceDeclaration, tdecl: ListTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private instantiateStackTypeDecl(ns: NamespaceDeclaration, tdecl: StackTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private instantiateQueueTypeDecl(ns: NamespaceDeclaration, tdecl: QueueTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private instantiateSetTypeDecl(ns: NamespaceDeclaration, tdecl: SetTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private instantiateMapTypeDecl(ns: NamespaceDeclaration, tdecl: MapTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private instantiateEventListTypeDecl(ns: NamespaceDeclaration, tdecl: EventListTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private instantiateEntityTypeDecl(ns: NamespaceDeclaration, tdecl: EntityTypeDecl) {
        this.file = tdecl.file;
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = this.relations.generateAllFieldBNamesInfo(rcvr, tdecl.fields, this.constraints);

        this.checkAbstractNominalTypeDeclHelper(bnames, rcvr, tdecl, tdecl.fields, true);
        this.file = CLEAR_FILENAME;
    }

    private instantiateOptionTypeDecl(ns: NamespaceDeclaration, tdecl: OptionTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, false);
    }

    private instantiateResultTypeDecl(ns: NamespaceDeclaration, tdecl: ResultTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, false);

        this.constraints.pushConstraintScope(tdecl.terms);
        for(let i = 0; i < tdecl.nestedEntityDecls.length; ++i) {
            const ned = tdecl.nestedEntityDecls[i];
            if(ned instanceof OkTypeDecl) {
                this.checkOkTypeDecl(ns, ned);
            }
            else {
                this.checkErrTypeDecl(ns, ned as ErrTypeDecl);
            }
        }
        this.constraints.popConstraintScope();
    }

    private instantiateAPIResultTypeDecl(ns: NamespaceDeclaration, tdecl: APIResultTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, false);

        this.constraints.pushConstraintScope(tdecl.terms);
        for(let i = 0; i < tdecl.nestedEntityDecls.length; ++i) {
            const ned = tdecl.nestedEntityDecls[i];
            if(ned instanceof APIRejectedTypeDecl) {
                this.checkAPIRejectedTypeDecl(ns, ned);
            }
            else if(ned instanceof APIFailedTypeDecl) {
                this.checkAPIFailedTypeDecl(ns, ned);
            }
            else if(ned instanceof APIErrorTypeDecl) {
                this.checkAPIErrorTypeDecl(ns, ned);
            }
            else {
                this.checkAPISuccessTypeDecl(ns, ned as APISuccessTypeDecl);
            }
        }
        this.constraints.popConstraintScope();
    }

    private instantiateConceptTypeDecl(ns: NamespaceDeclaration, tdecl: ConceptTypeDecl) {
        this.file = tdecl.file;
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = this.relations.generateAllFieldBNamesInfo(rcvr, tdecl.fields, this.constraints);

        this.checkAbstractNominalTypeDeclHelper(bnames, rcvr, tdecl, tdecl.fields, false);
        this.file = CLEAR_FILENAME;
    }

    private instantiateDatatypeMemberEntityTypeDecl(ns: NamespaceDeclaration, parent: DatatypeTypeDecl, tdecl: DatatypeMemberEntityTypeDecl) {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = this.relations.generateAllFieldBNamesInfo(rcvr, tdecl.fields, this.constraints);

        this.checkAbstractNominalTypeDeclHelper(bnames, rcvr, tdecl, tdecl.fields, true);
    }

    private instantiateDatatypeTypeDecl(ns: NamespaceDeclaration, tdecl: DatatypeTypeDecl) {
        this.file = tdecl.file;
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = this.relations.generateAllFieldBNamesInfo(rcvr, tdecl.fields, this.constraints);

        this.checkAbstractNominalTypeDeclHelper(bnames, rcvr, tdecl, tdecl.fields, true);

        for(let i = 0; i < tdecl.associatedMemberEntityDecls.length; ++i) {
            this.checkDatatypeMemberEntityTypeDecl(ns, tdecl, tdecl.associatedMemberEntityDecls[i]);
        }
        this.file = CLEAR_FILENAME;
    }

    private instantiateEventInfo(einfo: TypeSignature) {
        const oksig = this.checkTypeSignature(einfo);
        if(oksig) {
            this.checkError(einfo.sinfo, !this.relations.isEventDataType(einfo), `Event type is not a valid event type -- ${einfo.tkeystr}`);
        }
    }

    private instantiateStatusInfo(sinfo: TypeSignature[]) {
        for(let i = 0; i < sinfo.length; ++i) {
            const oksig = this.checkTypeSignature(sinfo[i]);
            if(oksig) {
                this.checkError(sinfo[i].sinfo, !this.relations.isStatusDataType(sinfo[i]), `Event type is not a valid status type -- ${sinfo[i].tkeystr}`);
            }
        }
    }

    private instantiateEnvironmentVariableInformation(env: EnvironmentVariableInformation[]) {
        for(let i = 0; i < env.length; ++i) {
            assert(false, "Not implemented -- checkEnvironmentVariableInformation");
        }
    }

    private instantiateResourceInformation(res: ResourceInformation[] | "**" | "{}" | "?") {
        if(res === "**" || res === "{}" || res === "?") {
            return;
        }

        for(let i = 0; i < res.length; ++i) {
            assert(false, "Not implemented -- checkResourceInformation");
        }
    }

    private instantiateAPIDecl(adecl: APIDecl) {
        assert(false, "Not implemented -- checkAPIDecl");
    }

    private instantiateTaskDecl(ns: NamespaceDeclaration, tdecl: TaskDecl) {
        this.file = tdecl.file;
        this.checkTemplateTypesOnType(tdecl.sinfo, tdecl.terms);

        if(tdecl.terms.length !== 0) {
            this.constraints.pushConstraintScope(tdecl.terms);
        }

        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = tdecl.fields.map((f) => { return {name: f.name, type: f.declaredType}; });

        //make sure all of the invariants on this typecheck
        this.checkInvariants(bnames, tdecl.invariants);
        this.checkValidates(bnames, tdecl.validates);
        
        this.checkConstMemberDecls(tdecl, tdecl.consts);
        this.checkTypeFunctionDecls(tdecl, tdecl.functions);
        this.checkTaskMethodDecls(tdecl, rcvr, tdecl.selfmethods);
        this.checkTaskActionDecls(tdecl, rcvr, tdecl.actions);

        this.checkMemberFieldDecls(bnames, tdecl.fields);

        if(tdecl.implementsapi !== undefined) {
            assert(false, "Not implemented -- checkTaskDecl implementsapi");
        }
        else {
            if(tdecl.eventsInfo !== undefined) {
                this.checkEventInfo(tdecl.eventsInfo as TypeSignature);
            }
            if(tdecl.statusInfo !== undefined) {
                this.checkStatusInfo(tdecl.statusInfo as TypeSignature[]);
            }
            if(tdecl.envVarRequirementInfo !== undefined) {
                this.checkEnvironmentVariableInformation(tdecl.envVarRequirementInfo as EnvironmentVariableInformation[]);
            }
            if(tdecl.resourceImpactInfo !== undefined) {
                this.checkResourceInformation(tdecl.resourceImpactInfo as ResourceInformation[] | "**" | "{}" | "?");
            }
        }

        if(tdecl.terms.length !== 0) {
            this.constraints.popConstraintScope();
        }
        this.file = CLEAR_FILENAME;
    }

    private instantiateNamespaceConstDecls(cdecls: NamespaceConstDecl[]) {
        for(let i = 0; i < cdecls.length; ++i) {
            const m = cdecls[i];

            this.file = m.file;
            if(this.checkTypeSignature(m.declaredType)) {
                const infertype = this.relations.convertTypeSignatureToTypeInferCtx(m.declaredType, this.constraints);
                const decltype = this.checkExpression(TypeEnvironment.createInitialStdEnv([], m.declaredType, infertype), m.value.exp, m.declaredType);

                this.checkError(m.sinfo, !this.relations.isSubtypeOf(decltype, m.declaredType, this.constraints), `Const initializer does not match declared type -- expected ${m.declaredType.tkeystr} but got ${decltype.tkeystr}`);
            }
            this.file = CLEAR_FILENAME;
        }
    }

    private instantiateNamespaceTypeDecls(ns: NamespaceDeclaration, tdecl: AbstractNominalTypeDecl[]) {
        for(let i = 0; i < tdecl.length; ++i) {
            const tt = tdecl[i];

            if(tt instanceof EnumTypeDecl) {
                this.checkEnumTypeDecl(ns, tt);
            }
            else if(tt instanceof TypedeclTypeDecl) {
                this.checkTypedeclTypeDecl(ns, tt);
            }
            else if(tt instanceof PrimitiveEntityTypeDecl) {
                this.checkPrimitiveEntityTypeDecl(ns, tt);
            }
            else if(tt instanceof OkTypeDecl) {
                this.checkOkTypeDecl(ns, tt);
            }
            else if(tt instanceof ErrTypeDecl) {
                this.checkErrTypeDecl(ns, tt);
            }
            else if(tt instanceof APIRejectedTypeDecl) {
                this.checkAPIRejectedTypeDecl(ns, tt);
            }
            else if(tt instanceof APIFailedTypeDecl) {
                this.checkAPIFailedTypeDecl(ns, tt);
            }
            else if(tt instanceof APIErrorTypeDecl) {
                this.checkAPIErrorTypeDecl(ns, tt);
            }
            else if(tt instanceof APISuccessTypeDecl) {
                this.checkAPISuccessTypeDecl(ns, tt);
            }
            else if(tt instanceof SomeTypeDecl) {
                this.checkSomeTypeDecl(ns, tt);
            }
            else if(tt instanceof MapEntryTypeDecl) {
                this.checkMapEntryTypeDecl(ns, tt);
            }
            else if(tt instanceof ListTypeDecl) {
                this.checkListTypeDecl(ns, tt);
            }
            else if(tt instanceof StackTypeDecl) {
                this.checkStackTypeDecl(ns, tt);
            }
            else if(tt instanceof QueueTypeDecl) {
                this.checkQueueTypeDecl(ns, tt);
            }
            else if(tt instanceof SetTypeDecl) {
                this.checkSetTypeDecl(ns, tt);
            }
            else if(tt instanceof MapTypeDecl) {
                this.checkMapTypeDecl(ns, tt);
            }
            else if(tt instanceof EventListTypeDecl) {
                this.checkEventListTypeDecl(ns, tt);
            }
            else if(tt instanceof EntityTypeDecl) {
                this.checkEntityTypeDecl(ns, tt);
            }
            else if(tt instanceof OptionTypeDecl) {
                this.checkOptionTypeDecl(ns, tt);
            }
            else if(tt instanceof ResultTypeDecl) {
                this.checkResultTypeDecl(ns, tt);
            }
            else if(tt instanceof APIResultTypeDecl) {
                this.checkAPIResultTypeDecl(ns, tt);
            }
            else if(tt instanceof ConceptTypeDecl) {
                this.checkConceptTypeDecl(ns, tt);
            }
            else if(tt instanceof DatatypeTypeDecl) {
                this.checkDatatypeTypeDecl(ns, tt);
            }
            else {
                assert(false, "Unknown type decl kind");
            }
        }
    }

    private instantiateNamespaceDeclaration(decl: NamespaceDeclaration) {
        this.instantiateNamespaceConstDecls(decl.consts);
    }


    static computeInstantiations(assembly: Assembly): AssemblyInstantiationInfo {

        xxxx;
    }
}

export { 
    InstantiationPropagator
};