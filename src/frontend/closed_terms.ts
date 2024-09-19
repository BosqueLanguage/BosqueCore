import assert from "node:assert";

import { AbstractNominalTypeDecl, APIDecl, APIErrorTypeDecl, APIFailedTypeDecl, APIRejectedTypeDecl, APIResultTypeDecl, APISuccessTypeDecl, Assembly, ConceptTypeDecl, ConstMemberDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, EntityTypeDecl, EnumTypeDecl, EnvironmentVariableInformation, FailTypeDecl, EventListTypeDecl, ExplicitInvokeDecl, InvariantDecl, InvokeExample, InvokeExampleDeclFile, InvokeExampleDeclInline, ListTypeDecl, MapEntryTypeDecl, MapTypeDecl, MemberFieldDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, OkTypeDecl, OptionTypeDecl, PostConditionDecl, PreConditionDecl, PrimitiveEntityTypeDecl, QueueTypeDecl, ResourceInformation, ResultTypeDecl, SetTypeDecl, SomeTypeDecl, StackTypeDecl, TaskActionDecl, TaskDecl, TaskMethodDecl, TypedeclTypeDecl, TypeFunctionDecl, ValidateDecl } from "./assembly.js";
import { FunctionInstantiationInfo, MethodInstantiationInfo, NamespaceInstantiationInfo, TypeInstantiationInfo } from "./instantiation_map.js";
import { EListTypeSignature, LambdaTypeSignature, NominalTypeSignature, TemplateNameMapper, TypeSignature, VoidTypeSignature } from "./type.js";
import { AbortStatement, AbstractBodyImplementation, AccessEnumExpression, AccessEnvValueExpression, AccessStaticFieldExpression, AccessVariableExpression, ArgumentValue, AssertStatement, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndExpression, BinLogicIFFExpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, BlockStatement, BodyImplementation, BuiltinBodyImplementation, CallNamespaceFunctionExpression, CallRefSelfExpression, CallRefThisExpression, CallTaskActionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, DebugStatement, EmptyStatement, EnvironmentBracketStatement, EnvironmentUpdateStatement, Expression, ExpressionBodyImplementation, ExpressionTag, IfElifElseStatement, IfElseStatement, IfExpression, IfStatement, ITest, ITestType, LambdaInvokeExpression, LetExpression, LiteralExpressionValue, LiteralTypeDeclValueExpression, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, MatchStatement, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixLiteralKeyAccess, PostfixOp, PostfixOpTag, PredicateUFBodyImplementation, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, ReturnMultiStatement, ReturnSingleStatement, ReturnVoidStatement, SelfUpdateStatement, SpecialConstructorExpression, SpecialConverterExpression, StandardBodyImplementation, Statement, StatementTag, SwitchStatement, SynthesisBodyImplementation, TaskAccessInfoExpression, TaskAllExpression, TaskDashExpression, TaskEventEmitStatement, TaskMultiExpression, TaskRaceExpression, TaskRunExpression, TaskStatusStatement, TaskYieldStatement, ThisUpdateStatement, ValidateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VariableRetypeStatement, VarUpdateStatement, VoidRefCallStatement } from "./body.js";
import { SourceInfo } from "./build_decls.js";

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
    readonly method: ExplicitInvokeDecl;
    readonly instantiation: TypeSignature[];

    readonly mkey: string;

    constructor(type: TypeSignature, mthd: ExplicitInvokeDecl, instantiation: TypeSignature[]) {
        this.type = type;
        this.method = mthd;
        this.instantiation = instantiation;

        this.mkey = `${type.tkeystr}@${mthd.name}${computeTBindsKey(instantiation)}`;
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

    readonly completedInstantiations: Set<string> = new Set<string>();

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
        return this.completedInstantiations.has(tkey) || this.pendingNominalTypeDecls.some((pntd) => pntd.tkey === tkey);
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

    private instantiateAccessVariableExpression(exp: AccessVariableExpression) {
        if(exp.layouttype !== undefined) {
            this.instantiateTypeSignature(exp.layouttype, this.currentMapping);
        }
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
        this.instantiateTypeSignature(exp.constype as TypeSignature, this.currentMapping);
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

        if(exp.trueBindType !== undefined) {
            this.instantiateTypeSignature(exp.trueBindType, this.currentMapping);
        }

        if(exp.trueBindType !== undefined) {
            this.instantiateTypeSignature(exp.trueBindType, this.currentMapping);
        }

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
            case ExpressionTag.AccessVariableExpression: {
                this.instantiateAccessVariableExpression(exp as AccessVariableExpression);
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
        this.instantiateTypeSignature(stmt.actualtype as TypeSignature, this.currentMapping);
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

            if(stmt.trueBindType !== undefined) {
                this.instantiateTypeSignature(stmt.trueBindType, this.currentMapping);
            }

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

            if(stmt.trueBindType !== undefined) {
                this.instantiateTypeSignature(stmt.trueBindType, this.currentMapping);
            }
            if(stmt.falseBindType !== undefined) {
                this.instantiateTypeSignature(stmt.falseBindType, this.currentMapping);
            }

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

    private instantiateNamespaceFunctionDecl(ns: NamespaceDeclaration, fdecl: PendingNamespaceFunction) {
        this.instantiateNamespaceDeclaration(ns);

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

        const cnns = this.currentNSInstantiation as NamespaceInstantiationInfo;
        if(!cnns.functionbinds.has(fdecl.function.name)) {
            cnns.functionbinds.set(fdecl.function.name, new FunctionInstantiationInfo(fdecl.function.terms.length !== 0 ? [] : undefined));
        }

        if(fdecl.function.terms.length !== 0) {
            ((cnns.functionbinds.get(fdecl.function.name) as FunctionInstantiationInfo).binds as TemplateNameMapper[]).push(this.currentMapping as TemplateNameMapper);
            this.currentMapping = undefined;
        }
    }

    private instantiateTypeFunctionDecl(tdecl: AbstractNominalTypeDecl, tfd: PendingTypeFunction) {
        assert(false, "Not implemented -- instantiateTypeFunctionDecl");
    }

    private instantiateMethodDecl(tdecl: AbstractNominalTypeDecl, mdecl: PendingTypeMethod) { 
        //TODO: dont forget to add any virtual or override methods here....

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

    private instantiateAbstractNominalTypeDeclHelper(pdecl: PendingNominalTypeDecl, terms: string[], optfdecls: MemberFieldDecl[] | undefined, optreqtypes: TypeSignature[] | undefined) {
        this.currentMapping = undefined;
        if(terms.length !== 0) {
            let tmap = new Map<string, TypeSignature>();
            terms.forEach((t, ii) => {
                tmap.set(t, pdecl.instantiation[ii])
            });

            this.currentMapping = new TemplateNameMapper([tmap])
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
            bbl.push(new TypeInstantiationInfo(pdecl.tkey, undefined, new Map<string, FunctionInstantiationInfo>(), new Map<string, MethodInstantiationInfo>()));
        }
        else {
            bbl.push(new TypeInstantiationInfo(pdecl.tkey, this.currentMapping as TemplateNameMapper, new Map<string, FunctionInstantiationInfo>(), new Map<string, MethodInstantiationInfo>()));
            this.currentMapping = undefined;
        }
    }

    private instantiateEnumTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateAbstractNominalTypeDeclHelper(pdecl, [], undefined, undefined);
    }

    private instantiateTypedeclTypeDecl(tdecl: TypedeclTypeDecl, pdecl: PendingNominalTypeDecl) {
        let mapping: TemplateNameMapper | undefined = undefined;
        if(tdecl.terms.length !== 0) {
            let tmap = new Map<string, TypeSignature>();
            tdecl.terms.forEach((t, ii) => {
                tmap.set(t.name, pdecl.instantiation[ii])
            });

            mapping = new TemplateNameMapper([tmap])
        }
        
        const etypes = [
            mapping !== undefined ? tdecl.valuetype.remapTemplateBindings(mapping) : tdecl.valuetype
        ];

        this.instantiateAbstractNominalTypeDeclHelper(pdecl, tdecl.terms.map((t) => t.name), undefined, etypes);
    }

    private instantiateInteralSimpleTypeDeclHelper(pdecl: PendingNominalTypeDecl, terms: string[], optreqtypes: TypeSignature[] | undefined) {
        this.instantiateAbstractNominalTypeDeclHelper(pdecl, terms, undefined, optreqtypes);
    }

    private instantiatePrimitiveEntityTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, [], undefined);
    }

    private instantiateOkTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T", "E"], undefined)
    }

    private instantiateFailTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T", "E"], undefined);
    }

    private instantiateAPIRejectedTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T"], undefined);
    }

    private instantiateAPIFailedTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T"], undefined);
    }

    private instantiateAPIErrorTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T"], undefined);
    }

    private instantiateAPISuccessTypeDecl(pdecl: PendingNominalTypeDecl) {
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T"], undefined);
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
            new NominalTypeSignature(tdecl.sinfo, undefined, tdecl.nestedEntityDecls[3], pdecl.instantiation)
        ];
        this.instantiateInteralSimpleTypeDeclHelper(pdecl, ["T"], stypes);
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

    private instantiateTaskDecl(tdecl: TaskDecl, pdecl: PendingNominalTypeDecl) {
        this.currentMapping = undefined;
        if(tdecl.terms.length !== 0) {
            let tmap = new Map<string, TypeSignature>();
            tdecl.terms.forEach((t, ii) => {
                tmap.set(tdecl.name, pdecl.instantiation[ii])
            });

            this.currentMapping = new TemplateNameMapper([tmap])
        }

        this.instantiateProvides(pdecl.type.provides);

        //make sure all of the invariants on this typecheck
        this.instantiateInvariants(pdecl.type.invariants);
        this.instantiateValidates(pdecl.type.validates);
        
        this.instantiateConstMemberDecls(pdecl.type, pdecl.type.consts);

        this.instantiateMemberFieldDecls(tdecl.fields);

        if(tdecl.implementsapi !== undefined) {
            assert(false, "Not implemented -- checkTaskDecl implementsapi");
        }
        else {
            if(tdecl.eventsInfo !== undefined) {
                this.instantiateTypeSignature(tdecl.eventsInfo, this.currentMapping);
            }
            if(tdecl.statusInfo !== undefined) {
                for(let i = 0; i < tdecl.statusInfo.length; ++i) {
                    this.instantiateTypeSignature(tdecl.statusInfo[i], this.currentMapping);
                }
            }
            if(tdecl.envVarRequirementInfo !== undefined) {
                this.instantiateEnvironmentVariableInformation(tdecl.envVarRequirementInfo as EnvironmentVariableInformation[]);
            }
            if(tdecl.resourceImpactInfo !== undefined) {
                this.instantiateResourceInformation(tdecl.resourceImpactInfo as ResourceInformation[] | "**" | "{}" | "?");
            }
        }

        const cnns = this.currentNSInstantiation as NamespaceInstantiationInfo;
        if(!cnns.typebinds.has(pdecl.type.name)) {
            cnns.typebinds.set(pdecl.type.name, []);
        }
        const bbl = cnns.typebinds.get(pdecl.type.name) as TypeInstantiationInfo[];

        if(tdecl.terms.length === 0) {
            bbl.push(new TypeInstantiationInfo(pdecl.tkey, undefined, new Map<string, FunctionInstantiationInfo>(), new Map<string, MethodInstantiationInfo>()));
        }
        else {
            bbl.push(new TypeInstantiationInfo(pdecl.tkey, this.currentMapping as TemplateNameMapper, new Map<string, FunctionInstantiationInfo>(), new Map<string, MethodInstantiationInfo>()));
            this.currentMapping = undefined;
        }
    }

    private instantiateNamespaceConstDecls(cdecls: NamespaceConstDecl[]) {
        for(let i = 0; i < cdecls.length; ++i) {
            const m = cdecls[i];

            this.instantiateTypeSignature(m.declaredType, this.currentMapping);
            this.instantiateExpression(m.value.exp);
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
        else if(tt instanceof APIRejectedTypeDecl) {
            this.instantiateAPIRejectedTypeDecl(pdecl);
        }
        else if(tt instanceof APIFailedTypeDecl) {
            this.instantiateAPIFailedTypeDecl(pdecl);
        }
        else if(tt instanceof APIErrorTypeDecl) {
            this.instantiateAPIErrorTypeDecl(pdecl);
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
        if(this.instantiation.find((nsi) => nsi.ns.emit() === nskey) === undefined) {
            this.instantiation.push(new NamespaceInstantiationInfo(decl.fullnamespace));
        }
        this.currentNSInstantiation = this.instantiation.find((nsi) => nsi.ns.emit() === nskey) as NamespaceInstantiationInfo;

        this.instantiateNamespaceConstDecls(decl.consts);
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
                this.pendingNamespaceFunctions.push(new PendingNamespaceFunction(decl, decl.functions[i], []));
            }
        }

        for(let i = 0; i < decl.typedecls.length; ++i) {
            if(this.shouldInstantiateAsRootType(decl.typedecls[i])) {
                const tsig = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), undefined, decl.typedecls[i], []);
                this.pendingNominalTypeDecls.push(new PendingNominalTypeDecl(tsig.tkeystr, decl.typedecls[i], []));
            }
        }

        for(let i = 0; i < decl.apis.length; ++i) {
            this.instantiateAPIDecl(decl.apis[i]);
        }

        for(let i = 0; i < decl.tasks.length; ++i) {
            if(this.shouldInstantiateAsRootType(decl.typedecls[i])) {
                const tsig = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), undefined, decl.typedecls[i], []);
                this.pendingNominalTypeDecls.push(new PendingNominalTypeDecl(tsig.tkeystr, decl.typedecls[i], []));
            }
        }

        for(let i = 0; i < decl.subns.length; ++i) {
            this. instantiateRootNamespaceDeclaration(decl.subns[i]);
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

    static computeInstantiations(assembly: Assembly, roonts: string): NamespaceInstantiationInfo[] {
        let wellknownTypes = new Map<string, TypeSignature>();
        wellknownTypes.set("Void", new VoidTypeSignature(SourceInfo.implicitSourceInfo()));

        InstantiationPropagator.loadWellKnownType(assembly, "None", wellknownTypes);
        InstantiationPropagator.loadWellKnownType(assembly, "Some", wellknownTypes);
        InstantiationPropagator.loadWellKnownType(assembly, "Bool", wellknownTypes);
        InstantiationPropagator.loadWellKnownType(assembly, "Int", wellknownTypes);
        InstantiationPropagator.loadWellKnownType(assembly, "Nat", wellknownTypes);
        InstantiationPropagator.loadWellKnownType(assembly, "BigInt", wellknownTypes);
        InstantiationPropagator.loadWellKnownType(assembly, "BigNat", wellknownTypes);
        InstantiationPropagator.loadWellKnownType(assembly, "Rational", wellknownTypes);
        InstantiationPropagator.loadWellKnownType(assembly, "Float", wellknownTypes);
        InstantiationPropagator.loadWellKnownType(assembly, "Decimal", wellknownTypes);
        InstantiationPropagator.loadWellKnownType(assembly, "DecimalDegree", wellknownTypes);
        InstantiationPropagator.loadWellKnownType(assembly, "LatLongCoordinate", wellknownTypes);
        InstantiationPropagator.loadWellKnownType(assembly, "Complex", wellknownTypes);

        InstantiationPropagator.loadWellKnownType(assembly, "String", wellknownTypes);
        InstantiationPropagator.loadWellKnownType(assembly, "CString", wellknownTypes);

        InstantiationPropagator.loadWellKnownType(assembly, "Regex", wellknownTypes);
        InstantiationPropagator.loadWellKnownType(assembly, "CRegex", wellknownTypes);

        let iim = new InstantiationPropagator(assembly, wellknownTypes);

        const rootns = assembly.getToplevelNamespace(roonts) as NamespaceDeclaration;
        iim.instantiateRootNamespaceDeclaration(rootns);

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

                    iim.pendingNamespaceFunctions.shift();
                }
                else if(iim.pendingTypeFunctions.length !== 0) {
                    const tfd = iim.pendingTypeFunctions[0];
                    iim.instantiateTypeFunctionDecl((tfd.type as NominalTypeSignature).decl, tfd);

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

                    iim.pendingTypeMethods.shift();
                }
            }
        }

        return iim.instantiation;
    }
}

export { 
    InstantiationPropagator
};