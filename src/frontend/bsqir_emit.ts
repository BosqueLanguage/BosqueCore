import assert from "node:assert";

import { AbstractCollectionTypeDecl, AbstractConceptTypeDecl, AbstractCoreDecl, AbstractDecl, AbstractEntityTypeDecl, AbstractInvokeDecl, AbstractNominalTypeDecl, APIErrorTypeDecl, APIFailedTypeDecl, APIRejectedTypeDecl, APIResultTypeDecl, APISuccessTypeDecl, Assembly, ConceptTypeDecl, ConditionDecl, ConstMemberDecl, ConstructableTypeDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, DeclarationAttibute, EntityTypeDecl, EnumTypeDecl, EventListTypeDecl, ExplicitInvokeDecl, FailTypeDecl, FunctionInvokeDecl, InternalEntityTypeDecl, InvariantDecl, InvokeParameterDecl, ListTypeDecl, MapEntryTypeDecl, MapTypeDecl, MemberFieldDecl, MethodDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, OkTypeDecl, OptionTypeDecl, PostConditionDecl, PreConditionDecl, PrimitiveEntityTypeDecl, QueueTypeDecl, ResultTypeDecl, SetTypeDecl, SomeTypeDecl, StackTypeDecl, TestAssociation, TypedeclTypeDecl, ValidateDecl } from "./assembly.js";
import { FunctionInstantiationInfo, MethodInstantiationInfo, NamespaceInstantiationInfo, TypeInstantiationInfo } from "./instantiation_map.js";
import { SourceInfo } from "./build_decls.js";
import { EListTypeSignature, FullyQualifiedNamespace, LambdaParameterSignature, LambdaTypeSignature, NominalTypeSignature, RecursiveAnnotation, TemplateNameMapper, TemplateTypeSignature, TypeSignature, VoidTypeSignature } from "./type.js";
import { AbortStatement, AbstractBodyImplementation, AccessEnumExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, ArgumentList, ArgumentValue, AssertStatement, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndExpression, BinLogicIFFExpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, BlockStatement, BodyImplementation, BuiltinBodyImplementation, CallNamespaceFunctionExpression, CallRefSelfExpression, CallRefThisExpression, CallRefVariableExpression, CallTaskActionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, CreateDirectExpression, DebugStatement, EmptyStatement, Expression, ExpressionBodyImplementation, ExpressionTag, IfElifElseStatement, IfElseStatement, IfExpression, IfStatement, ITest, KeyCompareEqExpression, KeyCompareLessExpression, LambdaInvokeExpression, LetExpression, LiteralExpressionValue, LiteralNoneExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralTypeDeclValueExpression, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, MatchStatement, NamedArgumentValue, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PositionalArgumentValue, PostfixAccessFromIndex, PostfixAccessFromName, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixLiteralKeyAccess, PostfixOp, PostfixOperation, PostfixOpTag, PostfixProjectFromNames, PredicateUFBodyImplementation, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, RefArgumentValue, ReturnMultiStatement, ReturnSingleStatement, ReturnVoidStatement, SafeConvertExpression, SelfUpdateStatement, SpecialConstructorExpression, SpreadArgumentValue, StandardBodyImplementation, Statement, StatementTag, SwitchStatement, SynthesisBodyImplementation, TaskAllExpression, TaskDashExpression, TaskMultiExpression, TaskRaceExpression, TaskRunExpression, ThisUpdateStatement, ValidateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VariableRetypeStatement, VarUpdateStatement, VoidRefCallStatement } from "./body.js";

class BsqonCodeFormatter {
    private level: number | undefined;

    constructor(iidnt: number | undefined) {
        this.level = iidnt;
    }

    indentPush() {
        if(this.level !== undefined) {
            this.level++;
        }
    }
    
    indentPop() {
        if(this.level !== undefined) {
            this.level--;
        }
    }
    
    nl(ct?: number): string {
        let cc = ct !== undefined ? ct : 1;

        if(cc === 1) {
            return this.level !== undefined ? "\n" : " ";
        }
        else {
            return this.level !== undefined ? "\n".repeat(cc) : " ";
        }
    }

    indent(code: string): string {
        if(this.level === undefined) {
            return " " + code;
        }
        else {
            return "    ".repeat(this.level) + code;
        }
    }
}

class EmitNameManager {
    static resolveNamespaceDecl(assembly: Assembly, ns: FullyQualifiedNamespace): NamespaceDeclaration {
        let curns = assembly.getToplevelNamespace(ns.ns[0]) as NamespaceDeclaration;

        for(let i = 1; i < ns.ns.length; ++i) {
            curns = curns.subns.find((nns) => nns.name === ns.ns[i]) as NamespaceDeclaration;
        }

        return curns as NamespaceDeclaration;
    }

    static generateNamespaceKey(ns: FullyQualifiedNamespace): string {
        return ns.ns.join("::"); //Core is explicit here
    }

    static generateTypeKey(tsig: TypeSignature): string {
        return tsig.tkeystr;
    }

    static generateNamespaceInvokeKey(ns: FullyQualifiedNamespace, name: string): string {
        return `${this.generateNamespaceKey(ns)}::${name}`;
    }

    static generateTypeInvokeKey(tsig: TypeSignature, name: string): string {
        return `${this.generateTypeKey(tsig)}::${name}`;
    }
}

class BSQIREmitter {
    readonly assembly: Assembly;
    readonly asminstantiation: NamespaceInstantiationInfo[];

    readonly generateTestInfo: boolean;
    readonly testfilefilter: string[] | undefined;
    readonly testfilters: TestAssociation[] | undefined;

    //map from files with tests to the list of tests
    readonly testgroups: [string, string[]][] = [];

    mapper: TemplateNameMapper | undefined;

    //Emit state fields
    nsconsts: string[] = [];
    typeconsts: string[] = [];
    
    nsfuncs: string[] = [];
    typefuncs: string[] = [];
    
    absmethods: string[] = [];
    virtmethods: string[] = [];
    overmethods: string[] = [];
    staticmethods: string[] = [];

    enums: string[] = [];
    typedecls: string[] = [];

    primtives: string[] = [];
    constructables: string[] = [];
    collections: string[] = [];

    entities: string[] = [];
    datamembers: string[] = [];

    pconcepts: string[] = [];
    concepts: string[] = [];

    datatypes: string[] = [];

    allfuncs: string[] = [];
    allmethods: string[] = [];
    allvmethods: string[] = [];

    allconcretetypes: string[] = [];
    allabstracttypes: string[] = [];

    constructor(assembly: Assembly, asminstantiation: NamespaceInstantiationInfo[], generateTestInfo: boolean, testfilefilter: string[] | undefined, testfilters: TestAssociation[] | undefined) {
        this.assembly = assembly;
        this.asminstantiation = asminstantiation;

        this.generateTestInfo = generateTestInfo;
        this.testfilefilter = testfilefilter;
        this.testfilters = testfilters;
    }

    private tproc(ttype: TypeSignature): TypeSignature {
        return this.mapper !== undefined ? ttype.remapTemplateBindings(this.getTemplateMapper()) : ttype;
    }

    private getTemplateMapper(): TemplateNameMapper {
        assert(this.mapper !== undefined, "Template mapper is not set");
        return this.mapper;
    }

    private emitSourceInfo(info: SourceInfo): string {
        return `SourceInfo{ line=${info.line}n, column=${info.column}n, pos=${info.pos}n, span=${info.span}n }`;
    }

    private emitRecInfo(recinfo: RecursiveAnnotation): string {
        if(recinfo === "yes") {
            return "RecursiveAnnotation#RecursiveTag";
        }
        else if(recinfo === "no") {
            return "RecursiveAnnotation#NonRecursiveTag";
        }
        else {
            return "RecursiveAnnotation#CondRecursiveTag";
        }
    }

    private emitTypeSignatureBase(ttype: TypeSignature): string {
        return `sinfo=${this.emitSourceInfo(ttype.sinfo)}, tkeystr='${ttype.tkeystr}'<TypeKey>`;
    }

    private emitLambdaParameterSignature(lps: LambdaParameterSignature): string {
        const ptype = this.emitTypeSignature(lps.type);
        return `LambdaParameterSignature{ ptype=${ptype}, isRefParam=${lps.isRefParam}, isRestParam=${lps.isRestParam} }`;
    }

    private emitTypeSignature(ttype: TypeSignature): string {
        const tt = this.tproc(ttype);

        if(tt instanceof VoidTypeSignature) {
            return `VoidTypeSignature{ ${this.emitTypeSignatureBase(tt)} }`;
        }
        else if(tt instanceof NominalTypeSignature) {
            return `NominalTypeSignature{ ${this.emitTypeSignatureBase(tt)} }`;
        }
        else if(tt instanceof EListTypeSignature) {
            const entries = tt.entries.map((et) => this.emitTypeSignature(et)).join(", ");
            return `EListTypeSignature{ ${this.emitTypeSignatureBase(tt)}, entries=List<TypeSignature>{${entries}} }`;
        }
        else if(tt instanceof LambdaTypeSignature) {
            const tsbase = this.emitTypeSignatureBase(tt);
            const recinfo = this.emitRecInfo(tt.recursive);
            const ispred = tt.name === "pred";
            const tparams = tt.params.map((tp) => this.emitLambdaParameterSignature(tp)).join(", ");
            const tret = this.emitTypeSignature(tt.resultType);

            return `LambdaTypeSignature{ ${tsbase}, frecursive=${recinfo}, isPredLambda=${ispred}, params=List<LambdaParameterSignature>{${tparams}}, resultType=${tret} }`;
        }
        else {
            assert(false, "Unknown type signature");
        }
    }

    private emitArgumentValue(arg: ArgumentValue): string {
        const eexp = this.emitExpression(arg.exp);

        if(arg instanceof RefArgumentValue) {
            return `RefArgumentValue{ exp=${eexp} }`;
        }
        else if(arg instanceof PositionalArgumentValue) {
            return `PositionalArgumentValue{ exp=${eexp} }`;
        }
        else if(arg instanceof NamedArgumentValue) {
            return `NamedArgumentValue{ exp=${eexp}, name='${arg.name}'<VarIdentifier> }`;
        }
        else if(arg instanceof SpreadArgumentValue) {
            return `SpreadArgumentValue{ exp=${eexp} }`;
        }
        else {
            assert(false, "Unknown argument value");
        }
    }

    private emitArgumentList(argl: ArgumentList): string {
        const args = argl.args.map((arg) => this.emitArgumentValue(arg)).join(", ");
        return `ArgumentList{ List<ArgumentValue>{${args}} }`;
    }

    private emitInvokeArgumentInfo(name: string, rec: RecursiveAnnotation, args: ArgumentList, shuffleinfo: [number, TypeSignature][], resttype: TypeSignature | undefined, restinfo: [number, boolean, TypeSignature][] | undefined) {
        const sinfocc = shuffleinfo.map((si) => `(|${si[0]}i, ${this.emitTypeSignature(si[1])}|)`).join(", ");
        const resttypecc = resttype !== undefined ? `some(${this.emitTypeSignature(resttype)})` : "none"
        const restinfocc = (restinfo || []).map((ri) => `(|${ri[0]}i, ${ri[1]}, ${this.emitTypeSignature(ri[2])}|)`).join(", ");

        return `InvokeArgumentInfo{ name='${name}'<Identifier>, rec=${this.emitRecInfo(rec)}, args=${this.emitArgumentList(args)}, shuffleinfo=List<(|Int, TypeSignature|)>{${sinfocc}}, resttype=${resttypecc}, restinfo=List<(|Int, Bool, TypeSignature|)>{${restinfocc}} }`;
    }

    private emitITest(itest: ITest): string {
        assert(false, "Not implemented -- ITest");
    }

    private emitExpressionBase(exp: Expression): string {
        return `sinfo=${this.emitSourceInfo(exp.sinfo)}, etype=${this.emitTypeSignature(exp.getType())}`;
    }

    private emitLiteralNoneExpression(exp: LiteralNoneExpression): string {
        return `LiteralNoneExpression{ ${this.emitExpressionBase(exp)} }`;
    }

    private emitLiteralSimpleExpression(exp: LiteralSimpleExpression): string {
        return `LiteralSimpleExpression{ ${this.emitExpressionBase(exp)}, value='${exp.value}' }`;
    }

    private emitLiteralUnicodeRegexExpression(exp: LiteralRegexExpression): string {
        assert(false, "Not implemented -- LiteralRegex");
    }
    
    private emitLiteralCRegexExpression(exp: LiteralRegexExpression): string {
        assert(false, "Not implemented -- LiteralCRegex");
    }
    
    private emitLiteralCStringExpression(exp: LiteralSimpleExpression): string {
        return `LiteralCStringExpression{ ${this.emitExpressionBase(exp)}, value='${exp.value}' }`;
    }

    private emitLiteralStringExpression(exp: LiteralSimpleExpression): string {
        return `LiteralStringExpression{ ${this.emitExpressionBase(exp)}, value='${exp.value}' }`;
    }
 
    private emitLiteralTypeDeclValueExpression(exp: LiteralTypeDeclValueExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const value = this.emitExpression(exp.value);
        const constype = this.emitTypeSignature(exp.constype);

        const ttdecl = (exp.constype as NominalTypeSignature).decl as TypedeclTypeDecl;
        const invchecks = ttdecl.allInvariants.length !== 0 || ttdecl.optofexp !== undefined;

        return `LiteralTypeDeclValueExpression{ ${ebase}, value=${value}, constype=${constype}, invchecks=${invchecks} }`;
    }

    private emitAccessNamespaceConstantExpression(exp: AccessNamespaceConstantExpression): string {
        const ebase = this.emitExpressionBase(exp);
        
        return `AccessNamespaceConstantExpression{ ${ebase}, ns='${exp.ns.emit()}'<>, name='${exp.name}'<Identifier> }`;
    }
    
    private emitAccessStaticFieldExpression(exp: AccessStaticFieldExpression): string {
        assert(false, "Not implemented -- AccessStaticField");
    }
    
    private emitAccessEnumExpression(exp: AccessEnumExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const etype = this.emitTypeSignature(exp.stype);

        return `AccessEnumExpression{ ${ebase}, stype=${etype}, name='${exp.name}' }`;
    }

    private emitAccessVariableExpression(exp: AccessVariableExpression): string {
        if(exp.specialaccess.length === 0) {
            const ebase = this.emitExpressionBase(exp);

            return `AccessVariableExpression{ ${ebase}, vname='${exp.srcname}'<VarIdentifier>, layouttype=${this.emitTypeSignature(exp.layouttype as TypeSignature)} }`;
        }
        else {
            //special access espression is converted to explicit accesses
            assert(false, "Not implemented -- AccessVariableExpressionSpecial");
        }
    }

    private emitConstructorExpressionBase(exp: ConstructorExpression): string {
        return `args=${this.emitArgumentList(exp.args)}`;
    }

    private emitConstructorPrimaryExpressionBase(exp: ConstructorPrimaryExpression): string {
        const cebase = this.emitConstructorExpressionBase(exp);
        const ctype = this.emitTypeSignature(exp.ctype);

        return `${cebase}, ctype=${ctype}`;
    }

    private emitCollectionConstructor(cdecl: AbstractCollectionTypeDecl, exp: ConstructorPrimaryExpression): string {
        assert(false, "Not implemented -- CollectionConstructor");
    }

    private emitSpecialConstructableConstructor(exp: ConstructorPrimaryExpression): string {
        assert(false, "Not implemented -- SpecialConstructableConstructor");
    }

    private emitTypeDeclConstructor(cdecl: TypedeclTypeDecl, exp: ConstructorPrimaryExpression): string {
        const cpee = this.emitConstructorPrimaryExpressionBase(exp);
        const invchecks = cdecl.allInvariants.length !== 0;

        if(cdecl.valuetype.tkeystr !== "CString" && cdecl.valuetype.tkeystr !== "String") {
            return `ConstructorTypeDeclExpression{ ${cpee}, invchecks=${invchecks} }`;
            
        }
        else {
            //TODO: we need to figure out how to encode regex expressions in general and Literals in particular
            assert(false, "Not implemented -- TypeDeclConstructor");
        }
    }

    private emitConstructorStdExpression(cdecl: EntityTypeDecl, exp: ConstructorPrimaryExpression): string {
        const cpee = this.emitConstructorPrimaryExpressionBase(exp);
        const invchecks = cdecl.allInvariants.length !== 0;

        const shuffleinfo = exp.shuffleinfo.map((si) => {
            return `(${si[0]}i, '${si[1]}'<Identifier>, ${this.emitTypeSignature(si[2])})`;
        });
        
        return `ConstructorStdExpression{ ${cpee}, shuffleinfo=List<(|Int, Identifier, TypeSignature|)>{${shuffleinfo}}, invchecks=${invchecks} }`;
    }

    private emitConstructorPrimaryExpression(exp: ConstructorPrimaryExpression): string {
        const ctype = exp.ctype as NominalTypeSignature;
        const decl = ctype.decl;
        if(decl instanceof AbstractCollectionTypeDecl) {
            return this.emitCollectionConstructor(decl, exp);
        }
        else if(decl instanceof ConstructableTypeDecl) {
            return this.emitSpecialConstructableConstructor(exp);
        }
        else if(decl instanceof TypedeclTypeDecl) {
            return this.emitTypeDeclConstructor(decl, exp);
        }
        else {
            return this.emitConstructorStdExpression(decl as EntityTypeDecl, exp);
        }
    }

    private emitConstructorEListExpression(exp: ConstructorEListExpression): string {
        const cebase = this.emitConstructorExpressionBase(exp);

        return `ConstructorEListExpression{ ${cebase} }`;
    }

    private emitConstructorLambdaExpression(exp: ConstructorLambdaExpression): string {
       assert(false, "Not implemented -- ConstructorLambda");
    }

    private emitLetExpression(exp: LetExpression): string {
        assert(false, "Not implemented -- Let");
    }

    private emitLambdaInvokeExpression(exp: LambdaInvokeExpression): string {
        assert(false, "Not implemented -- LambdaInvoke");
    }

    private emitSpecialConstructorExpression(exp: SpecialConstructorExpression): string {
        const ebase = this.emitExpressionBase(exp);

        return `ConstructorPrimarySpecialConstructableExpression{ ${ebase} }`;
    }

    private emitCallNamespaceFunctionExpression(exp: CallNamespaceFunctionExpression): string {
        const ebase = this.emitExpressionBase(exp);

        const cns = EmitNameManager.resolveNamespaceDecl(this.assembly, exp.ns);
        const ffinv = cns.functions.find((f) => f.name === exp.name) as NamespaceFunctionDecl;

        const nskey = EmitNameManager.generateNamespaceKey(exp.ns);
        const ikey = EmitNameManager.generateNamespaceInvokeKey(exp.ns, exp.name);

        const arginfo = this.emitInvokeArgumentInfo(exp.name, ffinv.recursive, exp.args, exp.shuffleinfo, exp.resttype, exp.restinfo);

        return `CallNamespaceFunctionExpression{ ${ebase}, ikey='${ikey}'<InvokeKey>, ns='${nskey}'<NamespaceKey>, arginfo=${arginfo} }`;
    }
    
    private emitCallTypeFunctionExpression(exp: CallTypeFunctionExpression): string {
        //const rtrgt = (this.tproc(exp.resolvedDeclType as TypeSignature) as NominalTypeSignature);

        if(exp.isSpecialCall) {
            assert(false, "Not implemented -- CallTypeFunction Special");
        }
        else {
            assert(false, "Not implemented -- CallTypeFunction");
        }
    }

    private emitLogicActionAndExpression(exp: LogicActionAndExpression): string {
        assert(false, "Not implemented -- LogicActionAnd");
    }
    
    private emitLogicActionOrExpression(exp: LogicActionOrExpression): string {
        assert(false, "Not implemented -- LogicActionOr");
    }
    
    private emitParseAsTypeExpression(exp: ParseAsTypeExpression): string {
        assert(false, "Not implemented -- ParseAsType");
    }

    private emitSafeConvertExpression(exp: SafeConvertExpression): string {
        assert(false, "Not implemented -- SafeConvert");
    }

    private emitCreateDirectExpression(exp: CreateDirectExpression): string {
        assert(false, "Not implemented -- CreateDirect");
    }

    private emitPostfixOperationBase(exp: PostfixOperation): string {
        return `sinfo=${this.emitSourceInfo(exp.sinfo)}, rcvrType=${this.emitTypeSignature(exp.getRcvrType())}, etype=${this.emitTypeSignature(exp.getType())}`;
    }

    private emitPostfixAccessFromName(exp: PostfixAccessFromName): string {
        const opbase = this.emitPostfixOperationBase(exp);
        const declaredInType = this.emitTypeSignature(exp.declaredInType as TypeSignature);
        const ftype = this.emitTypeSignature((exp.fieldDecl as MemberFieldDecl).declaredType);

        return `PostfixAccessFromName{ ${opbase}, declaredInType=${declaredInType}, name='${exp.name}'<Identifier>, ftype=${ftype} }`;
    }

    private emitPostfixProjectFromNames(exp: PostfixProjectFromNames): string {
        assert(false, "Not Implemented -- emitPostfixProjectFromNames");
    }

    private emitPostfixAccessFromIndex(exp: PostfixAccessFromIndex): string {
        const opbase = this.emitPostfixOperationBase(exp);

        return `PostfixAccessFromIndex{ ${opbase}, idx=${exp.idx}n }`;
    }

    private emitPostfixIsTest(exp: PostfixIsTest): string {
        const opbase = this.emitPostfixOperationBase(exp);
        const ttest = this.emitITest(exp.ttest);

        return `PostfixIsTest{ ${opbase}, ttest=${ttest} }`;
    }

    private emitPostfixAsConvert(exp: PostfixAsConvert): string {
        const opbase = this.emitPostfixOperationBase(exp);
        const ttype = this.emitITest(exp.ttest);

        return `PostfixAsConvert{ ${opbase}, ttype=${ttype} }`;
    }

    private emitPostfixAssignFields(exp: PostfixAssignFields): string {
        assert(false, "Not Implemented -- emitPostfixAssignFields");
    }

    private emitResolvedPostfixInvoke(exp: PostfixInvoke): string {
        const opbase = this.emitPostfixOperationBase(exp);

        const rtrgt = (this.tproc(exp.resolvedTrgt as TypeSignature) as NominalTypeSignature);
        const rdecl = exp.resolvedMethod as MethodDecl;

        const tkey = EmitNameManager.generateTypeKey(rtrgt);
        const ikey = EmitNameManager.generateTypeInvokeKey(rtrgt, exp.name);

        const arginfo = this.emitInvokeArgumentInfo(exp.name, rdecl.recursive, exp.args, exp.shuffleinfo, exp.resttype, exp.restinfo);

        return `PostfixInvokeStatic{ ${opbase}, resolvedType='${tkey}'<TypeKey>, resolvedTrgt='${ikey}'<InvokeKey>, arginfo=${arginfo} }`;
    }

    private emitVirtualPostfixInvoke(exp: PostfixInvoke): string {
        assert(false, "Not Implemented -- emitResolvedPostfixInvoke Virtual");
    }

    private emitPostfixInvoke(exp: PostfixInvoke): string {
        if(exp.resolvedTrgt !== undefined) {
            return this.emitResolvedPostfixInvoke(exp);
        }
        else {
            return this.emitVirtualPostfixInvoke(exp);
        }
    }

    private emitPostfixLiteralKeyAccess(exp: PostfixLiteralKeyAccess): string {
        assert(false, "Not Implemented -- emitPostfixLiteralKeyAccess");
    }

    private emitPostfixOp(exp: PostfixOp): string {
        const rootExp = this.emitExpression(exp.rootExp);
        const ops = exp.ops.map((op) => {
            switch(op.tag) {
                case PostfixOpTag.PostfixAccessFromName: {
                    return this.emitPostfixAccessFromName(op as PostfixAccessFromName);
                }
                case PostfixOpTag.PostfixProjectFromNames: {
                    return this.emitPostfixProjectFromNames(op as PostfixProjectFromNames);
                }
                case PostfixOpTag.PostfixAccessFromIndex: {
                    return this.emitPostfixAccessFromIndex(op as PostfixAccessFromIndex);
                }
                case PostfixOpTag.PostfixIsTest: {
                    return this.emitPostfixIsTest(op as PostfixIsTest);
                }
                case PostfixOpTag.PostfixAsConvert: {
                    return this.emitPostfixAsConvert(op as PostfixAsConvert);
                }
                case PostfixOpTag.PostfixAssignFields: {
                    return this.emitPostfixAssignFields(op as PostfixAssignFields);
                }
                case PostfixOpTag.PostfixInvoke: {
                    return this.emitPostfixInvoke(op as PostfixInvoke);
                }
                case PostfixOpTag.PostfixLiteralKeyAccess: {
                    return this.emitPostfixLiteralKeyAccess(op as PostfixLiteralKeyAccess);
                }
                default: {
                    assert(false, "Unknown postfix op");
                }
            }
        });

        return `PostfixOp{ rootExp=${rootExp}, ops=List<PostfixOp>{${ops}} }`;
    }

    private emitPrefixNotOpExpression(exp: PrefixNotOpExpression): string {
        const ebase = this.emitExpressionBase(exp);
        return `PrefixNotOpExpression{ ${ebase}, exp=${this.emitExpression(exp.exp)}, opertype=${this.emitTypeSignature(exp.opertype as TypeSignature)} }`;
    }

    private emitPrefixNegateOrPlusOpExpression(exp: PrefixNegateOrPlusOpExpression): string {
        const ebase = this.emitExpressionBase(exp);

        if(exp.op === "+") {
            return `PrefixPlusOpExpression{ ${ebase}, exp=${this.emitExpression(exp.exp)}, opertype=${this.emitTypeSignature(exp.opertype as TypeSignature)} }`;
        }
        else {
            return `PrefixNegateOpExpression{ ${ebase}, exp=${this.emitExpression(exp.exp)}, opertype=${this.emitTypeSignature(exp.opertype as TypeSignature)} }`;
        }
    }

    private emitBinAddExpression(exp: BinAddExpression): string {
        const ebase = this.emitExpressionBase(exp);
        return `BinAddExpression{ ${ebase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)}, opertype=${this.emitTypeSignature(exp.opertype as TypeSignature)} }`;
    }

    private emitBinSubExpression(exp: BinSubExpression,): string {
        const ebase = this.emitExpressionBase(exp);
        return `BinSubExpression{ ${ebase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)}, opertype=${this.emitTypeSignature(exp.opertype as TypeSignature)} }`;
    }
    
    private emitBinMultExpression(exp: BinMultExpression): string {
        assert(false, "Not implemented -- BinMult");
    }
    
    private emitBinDivExpression(exp: BinDivExpression): string {
        assert(false, "Not implemented -- BinDiv");
    }
    
    private emitBinKeyEqExpression(exp: BinKeyEqExpression): string {
        const kcop = exp.operkind;

        const ebase = this.emitExpressionBase(exp);
        const bkbase = `${ebase}, opertype=${this.emitTypeSignature(exp.opertype as TypeSignature)}`;

        if(kcop === "lhsnone") {
            return `BinKeyEqNoneExpression{ ${bkbase}, exp=${this.emitExpression(exp.rhs)} }`;
        }
        else if(kcop === "rhsnone") {
            return `BinKeyEqNoneExpression{ ${bkbase}, exp=${this.emitExpression(exp.lhs)} }`;
        }
        else if(kcop === "lhskeyeqoption") {
            return `BinKeySomeEqExpression{ ${bkbase}, eqoption=${this.emitExpression(exp.rhs)}, eqval=${this.emitExpression(exp.lhs)} }`;
        }
        else if(kcop === "rhskeyeqoption") {
            return `BinKeySomeEqExpression{ ${bkbase}, eqoption=${this.emitExpression(exp.lhs)}, eqval=${this.emitExpression(exp.rhs)} }`;
        }
        else if(kcop === "stricteq") {
            return `BinKeyEqExpression{ ${bkbase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
        }
        else {
            assert(false, "Unknown key eq kind");
        }
    }

    private emitBinKeyNeqExpression(exp: BinKeyNeqExpression): string {
        const kcop = exp.operkind;

        const ebase = this.emitExpressionBase(exp);
        const bkbase = `${ebase}, opertype=${this.emitTypeSignature(exp.opertype as TypeSignature)}`;

        if(kcop === "lhsnone") {
            return `BinKeyNotEqNoneExpression{ ${bkbase}, exp=${this.emitExpression(exp.rhs)} }`;
        }
        else if(kcop === "rhsnone") {
            return `BinKeyNotEqNoneExpression{ ${bkbase}, exp=${this.emitExpression(exp.lhs)} }`;
        }
        else if(kcop === "lhskeyeqoption") {
            return `BinKeyNotSomeEqExpression{ ${bkbase}, eqoption=${this.emitExpression(exp.rhs)}, eqval=${this.emitExpression(exp.lhs)} }`;
        }
        else if(kcop === "rhskeyeqoption") {
            return `BinKeyNotSomeEqExpression{ ${bkbase}, eqoption=${this.emitExpression(exp.lhs)}, eqval=${this.emitExpression(exp.rhs)} }`;
        }
        else if(kcop === "stricteq") {
            return `BinKeyNotEqExpression{ ${bkbase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
        }
        else {
            assert(false, "Unknown key eq kind");
        }
    }

    private emitKeyCompareEqExpression(exp: KeyCompareEqExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const ktype = this.emitTypeSignature(exp.ktype as TypeSignature);
        const optype = this.emitTypeSignature(exp.optype as TypeSignature);

        return `KeyCmpEqualExpression{ ${ebase}, ktype=${ktype}, optype=${optype} lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }

    private emitKeyCompareLessExpression(exp: KeyCompareLessExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const ktype = this.emitTypeSignature(exp.ktype as TypeSignature);
        const optype = this.emitTypeSignature(exp.optype as TypeSignature);

        return `KeyCmpEqualExpression{ ${ebase}, ktype=${ktype}, optype=${optype} lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }

    private emitNumericEqExpression(exp: NumericEqExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const optype = this.emitTypeSignature(exp.opertype as TypeSignature);

        return `NumericEqExpression{ ${ebase}, opertype=${optype}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }

    private emitNumericNeqExpression(exp: NumericNeqExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const optype = this.emitTypeSignature(exp.opertype as TypeSignature);

        return `NumericNeqExpression{ ${ebase}, opertype=${optype}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }
    
    private emitNumericLessExpression(exp: NumericLessExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const optype = this.emitTypeSignature(exp.opertype as TypeSignature);

        return `NumericLessExpression{ ${ebase}, opertype=${optype}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }
    
    private emitNumericLessEqExpression(exp: NumericLessEqExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const optype = this.emitTypeSignature(exp.opertype as TypeSignature);

        return `NumericLessEqExpression{ ${ebase}, opertype=${optype}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }
    
    private emitNumericGreaterExpression(exp: NumericGreaterExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const optype = this.emitTypeSignature(exp.opertype as TypeSignature);

        return `NumericGreaterExpression{ ${ebase}, opertype=${optype}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }

    private emitNumericGreaterEqExpression(exp: NumericGreaterEqExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const optype = this.emitTypeSignature(exp.opertype as TypeSignature);

        return `NumericGreaterEqExpression{ ${ebase}, opertype=${optype}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }

    private emitBinLogicAndExpression(exp: BinLogicAndExpression): string {
        const ebase = this.emitExpressionBase(exp);
        return `BinLogicAndExpression{ ${ebase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }

    private emitBinLogicOrExpression(exp: BinLogicOrExpression): string {
        const ebase = this.emitExpressionBase(exp);
        return `BinLogicOrExpression{ ${ebase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }

    private emitBinLogicImpliesExpression(exp: BinLogicImpliesExpression): string {
        const ebase = this.emitExpressionBase(exp);
        return `BinLogicImpliesExpression{ ${ebase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }

    private emitBinLogicIFFExpression(exp: BinLogicIFFExpression): string {
        const ebase = this.emitExpressionBase(exp);
        return `BinLogicIFFExpression{ ${ebase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }
    
    private emitMapEntryConstructorExpression(exp: MapEntryConstructorExpression): string {
        assert(false, "Not implemented -- MapEntryConstructor");
    }

    private emitIfExpression(exp: IfExpression): string {
        assert(false, "Not implemented -- IfExpression");
    }

    private emitExpression(exp: Expression): string {
        switch (exp.tag) {
            case ExpressionTag.LiteralNoneExpression: {
                return this.emitLiteralNoneExpression(exp as LiteralNoneExpression);
            }
            case ExpressionTag.LiteralBoolExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralNatExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralIntExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralBigNatExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralBigIntExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralRationalExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralFloatExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDecimalExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDecimalDegreeExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralLatLongCoordinateExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralComplexNumberExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralByteBufferExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUUIDv4Expression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUUIDv7Expression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralSHAContentHashExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralTZDateTimeExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralTAITimeExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralPlainDateExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralPlainTimeExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralLogicalTimeExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralISOTimeStampExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaDateTimeExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaISOTimeStampExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaSecondsExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaLogicalExpression: {
                return this.emitLiteralSimpleExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUnicodeRegexExpression: {
                return this.emitLiteralUnicodeRegexExpression(exp as LiteralRegexExpression);
            }
            case ExpressionTag.LiteralCRegexExpression: {
                return this.emitLiteralCRegexExpression(exp as LiteralRegexExpression);
            }
            case ExpressionTag.LiteralStringExpression: {
                return this.emitLiteralStringExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralCStringExpression: {
                return this.emitLiteralCStringExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralTypeDeclValueExpression: {
                return this.emitLiteralTypeDeclValueExpression(exp as LiteralTypeDeclValueExpression);
            }
            case ExpressionTag.AccessNamespaceConstantExpression: {
                return this.emitAccessNamespaceConstantExpression(exp as AccessNamespaceConstantExpression);
            }
            case ExpressionTag.AccessStaticFieldExpression: {
                return this.emitAccessStaticFieldExpression(exp as AccessStaticFieldExpression);
            }
            case ExpressionTag.AccessEnumExpression: {
                return this.emitAccessEnumExpression(exp as AccessEnumExpression);
            }
            case ExpressionTag.AccessVariableExpression: {
                return this.emitAccessVariableExpression(exp as AccessVariableExpression);
            }
            case ExpressionTag.ConstructorPrimaryExpression: {
                return this.emitConstructorPrimaryExpression(exp as ConstructorPrimaryExpression);
            }
            case ExpressionTag.ConstructorEListExpression: {
                return this.emitConstructorEListExpression(exp as ConstructorEListExpression);
            }
            case ExpressionTag.ConstructorLambdaExpression: {
                return this.emitConstructorLambdaExpression(exp as ConstructorLambdaExpression);
            }
            case ExpressionTag.LetExpression: {
                return this.emitLetExpression(exp as LetExpression);
            }
            case ExpressionTag.LambdaInvokeExpression: {
                return this.emitLambdaInvokeExpression(exp as LambdaInvokeExpression);
            }
            case ExpressionTag.SpecialConstructorExpression: {
                return this.emitSpecialConstructorExpression(exp as SpecialConstructorExpression);
            }
            case ExpressionTag.CallNamespaceFunctionExpression: {
                return this.emitCallNamespaceFunctionExpression(exp as CallNamespaceFunctionExpression);
            }
            case ExpressionTag.CallTypeFunctionExpression: {
                return this.emitCallTypeFunctionExpression(exp as CallTypeFunctionExpression);
            }
            case ExpressionTag.LogicActionAndExpression: {
                return this.emitLogicActionAndExpression(exp as LogicActionAndExpression);
            }
            case ExpressionTag.LogicActionOrExpression: {
                return this.emitLogicActionOrExpression(exp as LogicActionOrExpression);
            }
            case ExpressionTag.ParseAsTypeExpression: {
                return this.emitParseAsTypeExpression(exp as ParseAsTypeExpression);
            }
            case ExpressionTag.SafeConvertExpression: {
                return this.emitSafeConvertExpression(exp as SafeConvertExpression);
            }
            case ExpressionTag.CreateDirectExpression: {
                return this.emitCreateDirectExpression(exp as CreateDirectExpression);
            }
            case ExpressionTag.PostfixOpExpression: {
                return this.emitPostfixOp(exp as PostfixOp);
            }
            case ExpressionTag.PrefixNotOpExpression: {
                return this.emitPrefixNotOpExpression(exp as PrefixNotOpExpression);
            }
            case ExpressionTag.PrefixNegateOrPlusOpExpression: {
                return this.emitPrefixNegateOrPlusOpExpression(exp as PrefixNegateOrPlusOpExpression);
            }
            case ExpressionTag.BinAddExpression: {
                return this.emitBinAddExpression(exp as BinAddExpression);
            }
            case ExpressionTag.BinSubExpression: {
                return this.emitBinSubExpression(exp as BinSubExpression);
            }
            case ExpressionTag.BinMultExpression: {
                return this.emitBinMultExpression(exp as BinMultExpression);
            }
            case ExpressionTag.BinDivExpression: {
                return this.emitBinDivExpression(exp as BinDivExpression);
            }
            case ExpressionTag.BinKeyEqExpression: {
                return this.emitBinKeyEqExpression(exp as BinKeyEqExpression);
            }
            case ExpressionTag.BinKeyNeqExpression: {
                return this.emitBinKeyNeqExpression(exp as BinKeyNeqExpression);
            }
            case ExpressionTag.KeyCompareEqExpression: {
                return this.emitKeyCompareEqExpression(exp as KeyCompareEqExpression);
            }
            case ExpressionTag.KeyCompareLessExpression: {
                return this.emitKeyCompareLessExpression(exp as KeyCompareLessExpression);
            }
            case ExpressionTag.NumericEqExpression: {
                return this.emitNumericEqExpression(exp as NumericEqExpression);
            }
            case ExpressionTag.NumericNeqExpression: {
                return this.emitNumericNeqExpression(exp as NumericNeqExpression);
            }
            case ExpressionTag.NumericLessExpression: {
                return this.emitNumericLessExpression(exp as NumericLessExpression);
            }
            case ExpressionTag.NumericLessEqExpression: {
                return this.emitNumericLessEqExpression(exp as NumericLessEqExpression);
            }
            case ExpressionTag.NumericGreaterExpression: {
                return this.emitNumericGreaterExpression(exp as NumericGreaterExpression);
            }
            case ExpressionTag.NumericGreaterEqExpression: {
                return this.emitNumericGreaterEqExpression(exp as NumericGreaterEqExpression);
            }
            case ExpressionTag.BinLogicAndExpression: {
                return this.emitBinLogicAndExpression(exp as BinLogicAndExpression);
            }
            case ExpressionTag.BinLogicOrExpression: {
                return this.emitBinLogicOrExpression(exp as BinLogicOrExpression);
            }
            case ExpressionTag.BinLogicImpliesExpression: {
                return this.emitBinLogicImpliesExpression(exp as BinLogicImpliesExpression);
            }
            case ExpressionTag.BinLogicIFFExpression: {
                return this.emitBinLogicIFFExpression(exp as BinLogicIFFExpression);
            }
            case ExpressionTag.MapEntryConstructorExpression: {
                return this.emitMapEntryConstructorExpression(exp as MapEntryConstructorExpression);
            }
            case ExpressionTag.IfExpression: {
                return this.emitIfExpression(exp as IfExpression);
            }
            default: {
                assert(exp.tag === ExpressionTag.ErrorExpression, "Unknown expression kind");
                return "[ERROR EXPRESSION]";
            }
        }
    }

    private emitCallRefVariableExpression(exp: CallRefVariableExpression): string {
        assert(false, "Not implemented -- CallRefVariable");
    }

    private emitCallRefThisExpression(exp: CallRefThisExpression): string {
        assert(false, "Not implemented -- CallRefThis");
    }

    private emitCallRefSelfExpression(exp: CallRefSelfExpression): string {
        assert(false, "Not implemented -- CallRefSelf");
    }
    
    private emitCallTaskActionExpression(exp: CallTaskActionExpression): string {
        assert(false, "Not implemented -- CallTaskAction");
    }

    private emitTaskRunExpression(exp: TaskRunExpression): string {
        assert(false, "Not implemented -- TaskRun");
    }

    private emitTaskMultiExpression(exp: TaskMultiExpression): string {
        assert(false, "Not implemented -- TaskMulti");
    }

    private emitTaskDashExpression(exp: TaskDashExpression): string {
        assert(false, "Not implemented -- TaskDash");
    }
    
    private emitTaskAllExpression(exp: TaskAllExpression): string {
        assert(false, "Not implemented -- TaskAll");
    }
    
    private emitTaskRaceExpression(exp: TaskRaceExpression): string {
        assert(false, "Not implemented -- TaskRace");
    }

    private emitExpressionRHS(exp: Expression): string {
        const ttag = exp.tag;

        switch (ttag) {
            case ExpressionTag.CallRefVariableExpression: {
                return this.emitCallRefVariableExpression(exp as CallRefVariableExpression);
            }
            case ExpressionTag.CallRefThisExpression: {
                return this.emitCallRefThisExpression(exp as CallRefThisExpression);
            }
            case ExpressionTag.CallRefSelfExpression: {
                return this.emitCallRefSelfExpression(exp as CallRefSelfExpression);
            }
            case ExpressionTag.CallTaskActionExpression: {
                return this.emitCallTaskActionExpression(exp as CallTaskActionExpression);
            }
            case ExpressionTag.TaskRunExpression: {
                return this.emitTaskRunExpression(exp as TaskRunExpression);
            }
            case ExpressionTag.TaskMultiExpression: {
                return this.emitTaskMultiExpression(exp as TaskMultiExpression);
            }
            case ExpressionTag.TaskDashExpression: {
                return this.emitTaskDashExpression(exp as TaskDashExpression);
            }
            case ExpressionTag.TaskAllExpression: {
                return this.emitTaskAllExpression(exp as TaskAllExpression);
            }
            case ExpressionTag.TaskRaceExpression: {
                return this.emitTaskRaceExpression(exp as TaskRaceExpression);
            }
            default: {
                if(ttag === ExpressionTag.CallNamespaceFunctionExpression) {
                    return this.emitCallNamespaceFunctionExpression(exp as CallNamespaceFunctionExpression);
                }
                else if(ttag === ExpressionTag.CallTypeFunctionExpression) {
                    return this.emitCallTypeFunctionExpression(exp as CallTypeFunctionExpression);
                }
                else if(ttag === ExpressionTag.LambdaInvokeExpression) {
                    return this.emitLambdaInvokeExpression(exp as LambdaInvokeExpression);
                }
                else if(ttag === ExpressionTag.PostfixOpExpression) {
                    return this.emitPostfixOp(exp as PostfixOp);
                }
                else {
                    return this.emitExpression(exp);
                }
            }
        }
    }

    private emitStatementBase(): string {
        return "sinfo=${this.emitSourceInfo(stmt.sinfo)}";
    }

    private emitEmptyStatement(stmt: EmptyStatement): string {
        assert(false, "Should skip empty statement on emit");
    }
    
    private emitVariableDeclarationStatement(stmt: VariableDeclarationStatement): string {
        const sbase = this.emitStatementBase();
        const vtype = this.emitTypeSignature(stmt.vtype);

        return `VariableDeclarationStatement{ ${sbase}, name='${stmt.name}'<Identifier>, vtype=${vtype} }`;
    }
    
    private emitVariableMultiDeclarationStatement(stmt: VariableMultiDeclarationStatement): string {
        assert(false, "Not Implemented -- emitVariableMultiDeclarationStatement");
    }
    
    private emitVariableInitializationStatement(stmt: VariableInitializationStatement): string {
        const sbase = this.emitStatementBase();
        const vtype = this.emitTypeSignature(stmt.vtype);
        const rhsexp = this.emitExpressionRHS(stmt.exp);
        
        return `VariableInitializationStatement{ ${sbase}, name='${stmt.name}'<Identifier>, vtype=${vtype}, exp=${rhsexp} }`;
    }
    
    private emitVariableMultiInitializationStatement(stmt: VariableMultiInitializationStatement): string {
        assert(false, "Not Implemented -- emitVariableMultiInitializationStatement");
    }

    private emitVariableAssignmentStatement(stmt: VariableAssignmentStatement): string {
        const sbase = this.emitStatementBase();
        const vtype = this.emitTypeSignature(stmt.vtype as TypeSignature);
        const rhsexp = this.emitExpressionRHS(stmt.exp);

        return `VariableAssignmentStatement{ ${sbase}, name='${stmt.name}'<Identifier>, vtype=${vtype}, exp=${rhsexp} }`;
    }

    private emitVariableMultiAssignmentStatement(stmt: VariableMultiAssignmentStatement): string {
        assert(false, "Not Implemented -- emitVariableMultiAssignmentStatement");
    }

    private emitVariableRetypeStatement(stmt: VariableRetypeStatement): string {
        assert(false, "Not Implemented -- emitVariableRetypeStatement");
    }

    private emitReturnVoidStatement(stmt: ReturnVoidStatement): string {
        assert(false, "Not Implemented -- emitReturnVoidStatement");
    }

    private emitReturnSingleStatement(stmt: ReturnSingleStatement): string {
        const sbase = this.emitStatementBase();
        const rtype = this.emitTypeSignature(stmt.rtype as TypeSignature);
        const rexp = this.emitExpressionRHS(stmt.value);

        return `ReturnSingleStatement{ ${sbase}, rtype=${rtype}, value=${rexp} }`;
    }

    private emitReturnMultiStatement(stmt: ReturnMultiStatement): string {
        assert(false, "Not Implemented -- emitReturnMultiStatement");
    }

    private emitIfStatement(stmt: IfStatement, fmt: BsqonCodeFormatter): string {
        const sbase = this.emitStatementBase();

        const cond = this.emitExpression(stmt.cond.exp);
        const tblock = this.emitBlockStatement(stmt.trueBlock, fmt);

        if(stmt.binder === undefined) {
            return `IfStatement{ ${sbase}, cond=${cond}, trueBlock=${tblock} }`;
        }
        else {
            assert(false, "Not Implemented -- emitIfStatement with binder");
        }
    }

    private emitIfElseStatement(stmt: IfElseStatement, fmt: BsqonCodeFormatter): string {
        const sbase = this.emitStatementBase();

        const cond = this.emitExpression(stmt.cond.exp);
        const tblock = this.emitBlockStatement(stmt.trueBlock, fmt);
        const fblock = this.emitBlockStatement(stmt.falseBlock, fmt);

        if(stmt.binder === undefined) {
            return `IfElseStatement{ ${sbase}, cond=${cond}, trueBlock=${tblock}, falseBlock=${fblock} }`;
        }
        else {
            assert(false, "Not Implemented -- emitIfElseStatement with binder");
        }
    }

    private emitIfElifElseStatement(stmt: IfElifElseStatement, fmt: BsqonCodeFormatter): string {  
        assert(false, "Not Implemented -- emitIfElifElseStatement");
    }

    private emitSwitchStatement(stmt: SwitchStatement, fmt: BsqonCodeFormatter): string {
        assert(false, "Not Implemented -- emitSwitchStatement");
    }

    private emitMatchStatement(stmt: MatchStatement, fmt: BsqonCodeFormatter): string {
        assert(false, "Not Implemented -- emitMatchStatement");
    }

    private emitAbortStatement(stmt: AbortStatement): string {
        const sbase = this.emitStatementBase();
        return `AbortStatement{ ${sbase} }`;
    }

    private emitAssertStatement(stmt: AssertStatement): string {
        const sbase = this.emitStatementBase();
        const cond = this.emitExpression(stmt.cond);

        return `AssertStatement{ ${sbase}, cond=${cond} }`;
    }

    private emitValidateStatement(stmt: ValidateStatement): string {
        const sbase = this.emitStatementBase();
        const cond = this.emitExpression(stmt.cond);
        const dtag = stmt.diagnosticTag !== undefined ? `some('${stmt.diagnosticTag}')` : "none";

        return `ValidateStatement{ ${sbase}, cond=${cond}, diagnosticTag=${dtag} }`;
    }

    private emitDebugStatement(stmt: DebugStatement): string {
        assert(false, "Should skip debug statement on emit");
    }

    private emitVoidRefCallStatement(stmt: VoidRefCallStatement): string {
        assert(false, "Not Implemented -- emitVoidRefCallStatement");
    }

    private emitVarUpdateStatement(stmt: VarUpdateStatement): string {
        assert(false, "Not Implemented -- emitVarUpdateStatement");
    }

    private emitThisUpdateStatement(stmt: ThisUpdateStatement): string {
        assert(false, "Not Implemented -- emitThisUpdateStatement");
    }

    private emitSelfUpdateStatement(stmt: SelfUpdateStatement): string {
        assert(false, "Not implemented -- SelfUpdate");
    }

    private emitStatementArray(stmts: Statement[], fmt: BsqonCodeFormatter): string[] {
        let stmtstrs: string[] = [];

        fmt.indentPush();
        for(let i = 0; i < stmts.length; ++i) {
            const stmti = stmts[i];
            const sstr = fmt.indent(this.emitStatement(stmti, fmt));

            stmtstrs.push(sstr);
            stmtstrs.push(fmt.nl());
        }
        fmt.indentPop();

        return stmtstrs;
    }

    private emitBlockStatement(stmt: BlockStatement, fmt: BsqonCodeFormatter): string {
        const stmts = this.emitStatementArray(stmt.statements.filter((stmt) => !((stmt instanceof EmptyStatement) || (stmt instanceof DebugStatement))), fmt);
        return ["BlockStatement{", `isScoping=${stmt.isScoping},`, fmt.nl(), "List<Statement>{", ...stmts, fmt.indent("}}")].join("");
    }

    private emitStatement(stmt: Statement, fmt: BsqonCodeFormatter): string {
        switch(stmt.tag) {
            case StatementTag.EmptyStatement: {
                return this.emitEmptyStatement(stmt as EmptyStatement);
            }
            case StatementTag.VariableDeclarationStatement: {
                return this.emitVariableDeclarationStatement(stmt as VariableDeclarationStatement);
            }
            case StatementTag.VariableMultiDeclarationStatement: {
                return this.emitVariableMultiDeclarationStatement(stmt as VariableMultiDeclarationStatement);
            }
            case StatementTag.VariableInitializationStatement: {
                return this.emitVariableInitializationStatement(stmt as VariableInitializationStatement);
            }
            case StatementTag.VariableMultiInitializationStatement: {
                return this.emitVariableMultiInitializationStatement(stmt as VariableMultiInitializationStatement);
            }
            case StatementTag.VariableAssignmentStatement: {
                return this.emitVariableAssignmentStatement(stmt as VariableAssignmentStatement);
            }
            case StatementTag.VariableMultiAssignmentStatement: {
                return this.emitVariableMultiAssignmentStatement(stmt as VariableMultiAssignmentStatement);
            }
            case StatementTag.VariableRetypeStatement: {
                return this.emitVariableRetypeStatement(stmt as VariableRetypeStatement);
            }
            case StatementTag.ReturnVoidStatement: {
                return this.emitReturnVoidStatement(stmt as ReturnVoidStatement);
            }
            case StatementTag.ReturnSingleStatement: {
                return this.emitReturnSingleStatement(stmt as ReturnSingleStatement);
            }
            case StatementTag.ReturnMultiStatement: {
                return this.emitReturnMultiStatement(stmt as ReturnMultiStatement);
            }
            case StatementTag.IfStatement: {
                return this.emitIfStatement(stmt as IfStatement, fmt);
            }
            case StatementTag.IfElseStatement: {
                return this.emitIfElseStatement(stmt as IfElseStatement, fmt);
            }
            case StatementTag.IfElifElseStatement: {
                return this.emitIfElifElseStatement(stmt as IfElifElseStatement, fmt);
            }
            case StatementTag.SwitchStatement: {
                return this.emitSwitchStatement(stmt as SwitchStatement, fmt);
            }
            case StatementTag.MatchStatement: {
                return this.emitMatchStatement(stmt as MatchStatement, fmt);
            }
            case StatementTag.AbortStatement: {
                return this.emitAbortStatement(stmt as AbortStatement);
            }
            case StatementTag.AssertStatement: {
                return this.emitAssertStatement(stmt as AssertStatement);
            }
            case StatementTag.ValidateStatement: {
                return this.emitValidateStatement(stmt as ValidateStatement);
            }
            case StatementTag.DebugStatement: {
                return this.emitDebugStatement(stmt as DebugStatement);
            }
            case StatementTag.VoidRefCallStatement: {
                return this.emitVoidRefCallStatement(stmt as VoidRefCallStatement);
            }
            case StatementTag.VarUpdateStatement: {
                return this.emitVarUpdateStatement(stmt as VarUpdateStatement);
            }
            case StatementTag.ThisUpdateStatement: {
                return this.emitThisUpdateStatement(stmt as ThisUpdateStatement);
            }
            case StatementTag.SelfUpdateStatement: {
                return this.emitSelfUpdateStatement(stmt as SelfUpdateStatement);
            }
            case StatementTag.BlockStatement: {
                return this.emitBlockStatement(stmt as BlockStatement, fmt);
            }
            default: {
                assert(stmt.tag === StatementTag.ErrorStatement, `Unknown statement kind -- ${stmt.tag}`);

                return "[ERROR STATEMENT]";
            }
        }
    }

    private emitBodyImplementation(body: BodyImplementation, fmt: BsqonCodeFormatter): string {
        if(body instanceof AbstractBodyImplementation) {
            return "AbstractBodyImplementation { }";
        }
        else if(body instanceof PredicateUFBodyImplementation) {
            return "PredicateUFBodyImplementation { }";
        }
        else if(body instanceof BuiltinBodyImplementation) {
            return `BuiltinBodyImplementation { '${body.builtin}' }`;
        }
        else if(body instanceof SynthesisBodyImplementation) {
            return "SynthesisBodyImplementation { }";
        }
        else if(body instanceof ExpressionBodyImplementation) {
            return `ExpressionBodyImplementation { ${this.emitExpression(body.exp)} }`;
        }
        else if(body instanceof StandardBodyImplementation) {
            const stmts = this.emitStatementArray(body.statements, fmt);
            return ["StandardBodyImplementation {", fmt.nl(), "List<Statement>{", ...stmts, fmt.indent("}}")].join("");
        }
        else {
            assert(false, "Unknown body implementation kind");
        }
    }

    private testEmitEnabled(fdecl: NamespaceFunctionDecl): boolean {
        if(!this.generateTestInfo) {
            return false;
        }

        if(this.testfilefilter === undefined && this.testfilters === undefined) {
            return true;
        }

        let matchfile = false;
        if(this.testfilefilter !== undefined) {
            matchfile = this.testfilefilter.some((ff) => fdecl.file.endsWith(ff));
        }

        let matchfilter = false;
        if(this.testfilters !== undefined) {
            const assoc = fdecl.tassoc;

            matchfilter = assoc !== undefined && this.testfilters.some((tmatch) => assoc.some((asc) => asc.isMatchWith(tmatch)));
        }

        return matchfile || matchfilter;
    }

    private emitAbstractDeclBase(decl: AbstractDecl, nskey: string): string {
        return `file='${decl.file}', sinfo=${this.emitSourceInfo(decl.sinfo)}, declaredInNS='${nskey}'<NamespaceKey>`;
    }

    private emitConditionDeclBase(decl: ConditionDecl, nskey: string, exp: Expression): string {
        const dbase = this.emitAbstractDeclBase(decl, nskey);
        const dtag = decl.diagnosticTag !== undefined ? `some('${decl.diagnosticTag}')` : "none";

        return `${dbase}, diagnosticTag=${dtag}, exp=${this.emitExpression(exp)}`;
    }


    private emitPreConditionDecl(decl: PreConditionDecl, nskey: string): string {
        const cbase = this.emitConditionDeclBase(decl, nskey, decl.exp);
        return `PreConditionDecl{ ${cbase}, issoft=${decl.issoft} }`;
    }

    private emitPostConditionDecl(decl: PostConditionDecl, nskey: string): string {
        const cbase = this.emitConditionDeclBase(decl, nskey, decl.exp);
        return `PostConditionDecl{ ${cbase}, issoft=${decl.issoft} }`;
    }

    private emitInvariantDecl(decl: InvariantDecl, nskey: string): string {
        const cbase = this.emitConditionDeclBase(decl, nskey, decl.exp.exp);
        return `InvariantDecl{ ${cbase} }`;
    }

    private emitValidateDecl(decl: ValidateDecl, nskey: string): string {
        const cbase = this.emitConditionDeclBase(decl, nskey, decl.exp.exp);
        return `ValidateDecl{ ${cbase} }`;
    }

    private emitDeclarationAttibuteBase(att: DeclarationAttibute, nskey: string): string {
        const tags = att.tags.map((t) => `(${this.emitTypeSignature(t.enumType)}, '${t.tag}')`);
        const text = att.text !== undefined ? `some('${att.text}')` : "none";

        return `DeclarationAttibute{name='${att.name}'<Identifier>, tags=List<(|TypeSignature, CString|)>{ ${tags.join(", ")} }, text=${text} }`;
    }

    private emitAbstractCoreDecl(decl: AbstractCoreDecl, nskey: string): string {
        const dbase = this.emitAbstractDeclBase(decl, nskey);
        const atts = decl.attributes.map((att) => this.emitDeclarationAttibuteBase(att, nskey));

        return `${dbase}, attributes=List<DeclarationAttibute>{ ${atts.join(", ")} }, name='${decl.name}'<Identifier>`;
    }

    private emitInvokeParameterDecl(pdecl: InvokeParameterDecl): string {
        const ptype = this.emitTypeSignature(pdecl.type);
        const defaultval = pdecl.optDefaultValue !== undefined ? `some(${this.emitExpression(pdecl.optDefaultValue.exp)})` : "none";

        return `InvokeParameterDecl{ name='${pdecl.name}'<Identifier>, ptype=${ptype}, defaultval=${defaultval}, isRefParam=${pdecl.isRefParam}, isRestParam=${pdecl.isRestParam} }`;
    }

    private emitAbstractInvokeDecl(decl: AbstractInvokeDecl, nskey: string, ikey: string, fmt: BsqonCodeFormatter): string {
        const dbase = this.emitAbstractCoreDecl(decl, nskey);

        const isrecursive = this.emitRecInfo(decl.recursive);
        const params = decl.params.map((p) => this.emitInvokeParameterDecl(p));
        const resultType = this.emitTypeSignature(decl.resultType);

        const body = this.emitBodyImplementation(decl.body, fmt);

        return `${dbase}, ikey='${ikey}'<InvokeKey>, irecursive=${isrecursive}, params=List<InvokeParameterDecl>{ ${params.join(", ")} }, resultType=${resultType}, body=${body}`;
    }

    private emitExplicitInvokeDecl(decl: ExplicitInvokeDecl, nskey: string, ikey: string, fmt: BsqonCodeFormatter): string {
        const ibase = this.emitAbstractInvokeDecl(decl, nskey, ikey, fmt);

        const preconds = decl.preconditions.map((p) => this.emitPreConditionDecl(p, nskey)).join(", ");
        const postconds = decl.postconditions.map((p) => this.emitPostConditionDecl(p, nskey)).join(", ");

        return `${ibase}, preconditions=List<PreConditionDecl>{ ${preconds}}, postconditions=List<PostConditionDecl>{ ${postconds} }`;
    }

    private emitFKindTag(fkind: "function" | "predicate" | "errtest" | "chktest" | "example"): string {
        if(fkind === "function") {
            return "FunctionDeclKindTag#Function";
        }
        else if(fkind === "predicate") {
            return "FunctionDeclKindTag#Predicate";
        }
        else if(fkind === "errtest") {
            return "FunctionDeclKindTag#ErrorTest";
        }
        else if(fkind === "chktest") {
            return "FunctionDeclKindTag#CheckTest";
        }
        else {
            return "FunctionDeclKindTag#Example";
        }
    }

    private emitFunctionDecl(ns: FullyQualifiedNamespace, fdecl: FunctionInvokeDecl, optenclosingtype: [NominalTypeSignature, TemplateNameMapper | undefined] | undefined, optmapping: TemplateNameMapper | undefined, fmt: BsqonCodeFormatter) {
        const omap = this.mapper;
        if(optmapping !== undefined) {
            this.mapper = TemplateNameMapper.tryMerge(optenclosingtype !== undefined ? optenclosingtype[1] : undefined, optmapping);
        }

        const nskey = EmitNameManager.generateNamespaceKey(ns);
        if(optenclosingtype !== undefined) {
            const ikey =  EmitNameManager.generateTypeInvokeKey(optenclosingtype[0], fdecl.name);
            const ibase = this.emitExplicitInvokeDecl(fdecl, nskey, ikey, fmt);
            this.mapper = omap;

            this.typefuncs.push(`'${ikey}'<InvokeKey> => TypeFunctionDecl{ ${ibase} }`)
            this.allfuncs.push(`'${ikey}'<InvokeKey>`);
        }
        else {
            const ftag = (fdecl as NamespaceFunctionDecl).fkind;
            if(ftag === "function" || ftag === "predicate" || this.testEmitEnabled(fdecl as NamespaceFunctionDecl)) {
                const ikey = EmitNameManager.generateNamespaceInvokeKey(ns, fdecl.name);
                const ibase = this.emitExplicitInvokeDecl(fdecl, nskey, ikey, fmt);
                this.mapper = omap;
            
                this.nsfuncs.push(`'${ikey}'<InvokeKey> => NamespaceFunctionDecl{ ${ibase}, fkind=${this.emitFKindTag((fdecl as NamespaceFunctionDecl).fkind)} }`);
                this.allfuncs.push(`'${ikey}'<InvokeKey>`);
            }
        }
    }

    private emitFunctionDecls(ns: FullyQualifiedNamespace, optenclosingtype: [NominalTypeSignature, TemplateNameMapper | undefined] | undefined, fdecls: [FunctionInvokeDecl, FunctionInstantiationInfo | undefined][], fmt: BsqonCodeFormatter) {
        for(let i = 0; i < fdecls.length; ++i) {
            const fdecl = fdecls[i][0];
            const fii = fdecls[i][1]; 

            if(fii !== undefined) {
                if(fii.binds === undefined) {
                    this.emitFunctionDecl(ns, fdecl, optenclosingtype, undefined, fmt);
                }
                else {
                    for(let j = 0; j < fii.binds.length; ++j) {
                        this.emitFunctionDecl(ns, fdecl, optenclosingtype, fii.binds[j], fmt);
                    }
                }
            }
        }
    }

    private emitMethodDecl(ns: FullyQualifiedNamespace, rcvrtype: [NominalTypeSignature, TemplateNameMapper | undefined], mdecl: MethodDecl, optmapping: TemplateNameMapper | undefined, fmt: BsqonCodeFormatter): string {
        const omap = this.mapper;
        if(optmapping !== undefined) {
            this.mapper = TemplateNameMapper.tryMerge(rcvrtype[1], optmapping);
        }

        //TODO: handle emit here...

        this.mapper = omap;

        assert(false, "Not implemented -- emitMethodDecl");
    }

    private emitMethodDecls(ns: FullyQualifiedNamespace, rcvr: [NominalTypeSignature, TemplateNameMapper | undefined], mdecls: [MethodDecl, MethodInstantiationInfo | undefined][], fmt: BsqonCodeFormatter): string[] {
        let decls: string[] = [];

        for(let i = 0; i < mdecls.length; ++i) {
            const mdecl = mdecls[i][0];
            const mii = mdecls[i][1];

            if(mii !== undefined) {
                if(mii.binds === undefined) {
                    const bsqondecl = this.emitMethodDecl(ns, rcvr, mdecl, undefined, fmt);
                    decls.push(bsqondecl);
                }
                else {
                    for(let j = 0; j < mii.binds.length; ++j) {
                        const bsqondecl = this.emitMethodDecl(ns, rcvr, mdecl, mii.binds[j], fmt);
                        decls.push(bsqondecl);
                    }
                }
            }
        }

        return decls;
    }

    private emitConstMemberDecls(ns: FullyQualifiedNamespace, declInType: NominalTypeSignature, decls: ConstMemberDecl[]) {
        for(let i = 0; i < decls.length; ++i) {
            const dd = decls[i];

            const dbase = this.emitAbstractCoreDecl(dd, EmitNameManager.generateNamespaceKey(ns));
            const intype = this.emitTypeSignature(declInType);
            const dtype = this.emitTypeSignature(dd.declaredType);
            const value = this.emitExpression(dd.value.exp);

            this.typeconsts.push(`ConstMemberDecl{ ${dbase}, declaredInType=${intype}, declaredType=${dtype}, value=${value} }`);
        }
    }

    private static generateRcvrForNominalAndBinds(ntype: AbstractNominalTypeDecl, binds: TemplateNameMapper | undefined, implicitbinds: string[] | undefined): NominalTypeSignature {
        if(binds === undefined) {
            return new NominalTypeSignature(ntype.sinfo, undefined, ntype, []);
        }
        else {
            const tbinds = implicitbinds !== undefined ? implicitbinds.map((bb) => binds.resolveTemplateMapping(new TemplateTypeSignature(SourceInfo.implicitSourceInfo(), bb))) : ntype.terms.map((tt) => binds.resolveTemplateMapping(new TemplateTypeSignature(SourceInfo.implicitSourceInfo(), tt.name)));
            return new NominalTypeSignature(ntype.sinfo, undefined, ntype, tbinds);
        }
    }

    private emitMemberFieldDecl(ns: FullyQualifiedNamespace, enclosingtype: TypeSignature, fdecl: MemberFieldDecl): string {
        const dbase = this.emitAbstractCoreDecl(fdecl, EmitNameManager.generateNamespaceKey(ns));

        const declin = this.emitTypeSignature(enclosingtype);
        const decltype = this.emitTypeSignature(fdecl.declaredType);
        const defaultValue = fdecl.defaultValue !== undefined ? `some(${this.emitExpression(fdecl.defaultValue.exp)})` : "none";

        return `MemberFieldDecl{ ${dbase}, declaredInType=${declin}, declaredType=${decltype}, defaultValue=${defaultValue}, isSpecialAccess=${fdecl.isSpecialAccess} }`;
    }

    private emitSaturatedFieldInfo(sfield: {name: string, type: TypeSignature, hasdefault: boolean, containingtype: NominalTypeSignature}): string {
        return `SaturatedFieldInfo{ containingtype=${this.emitTypeSignature(sfield.containingtype)}, name='${sfield.name}'<Identifier>, type=${this.emitTypeSignature(sfield.type)}, hasdefault=${sfield.hasdefault} }`;
    }
    
    private emitSaturatedInvariantInfo(invariants: {containingtype: NominalTypeSignature, file: string, sinfo: SourceInfo, tag: string | undefined}): string {
        return `SaturatedInvariantInfo{ containingtype=${this.emitTypeSignature(invariants.containingtype)}, file='${invariants.file}', sinfo=${this.emitSourceInfo(invariants.sinfo)}, tag=${invariants.tag !== undefined ? `some('${invariants.tag}')` : "none"} }`;
    }

    private emitAbstractNominalTypeDeclBase(ns: FullyQualifiedNamespace, tsig: NominalTypeSignature, tdecl: AbstractNominalTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): string {
        const tbase = this.emitAbstractDeclBase(tdecl, EmitNameManager.generateNamespaceKey(ns));

        const tkey = EmitNameManager.generateTypeKey(tsig);

        const invariants = tdecl.invariants.map((inv) => this.emitInvariantDecl(inv, EmitNameManager.generateNamespaceKey(ns))).join(", ");
        const validates = tdecl.validates.map((val) => this.emitValidateDecl(val, EmitNameManager.generateNamespaceKey(ns))).join(", ");

        this.emitConstMemberDecls(ns, tsig, tdecl.consts);

        const [absmethods, virtmethods, overmethods, staticmethods] = this.emitMethodDecls(ns, [tsig, instantiation.binds], tdecl.methods.map((md) => [md, instantiation.methodbinds.get(md.name)]), fmt);

        const provides = tdecl.saturatedProvides.map((sp) => this.emitTypeSignature(sp)).join(", ");
        const bfields = tdecl.saturatedBFieldInfo.map((sb) => this.emitSaturatedFieldInfo(sb)).join(", ");

        const allInvariants = tdecl.allInvariants.map((ai) => this.emitSaturatedInvariantInfo(ai)).join(", ");
        const allValidates = tdecl.allValidates.map((av) => this.emitSaturatedInvariantInfo(av)).join(", ");

        return `${tbase}, tkey='${tkey}'<TypeKey>, invariants=List<InvariantDecl>{ ${invariants} }, validates=List<ValidateDecl>{ ${validates} }, absmethods=List<InvokeKey>{ ${absmethods} }, virtmethods=List<InvokeKey>{ ${virtmethods} }, overmethods=List<InvokeKey>{ ${overmethods} }, staticmethods=List<InvokeKey>{ ${staticmethods} }, saturatedProvides=List<NominalTypeSignature>{ ${provides} }, saturatedBFieldInfo=List<SaturatedFieldInfo>{ ${bfields} }, allInvariants=List<SaturatedInvariantInfo>{ ${allInvariants} }, allValidates=List<SaturatedInvariantInfo>{ ${allValidates} }`;
    }

    private emitAbstractEntityTypeDeclBase(ns: FullyQualifiedNamespace, tsig: NominalTypeSignature, tdecl: AbstractEntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): string {
        return this.emitAbstractNominalTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);
    }

    private emitEnumTypeDecl(ns: FullyQualifiedNamespace, tdecl: EnumTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        const tbase = this.emitAbstractNominalTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        const fields = tdecl.members.map((mname) => `'${mname}'`).join(", ");
        return [`${EmitNameManager.generateTypeKey(tsig)}<TypeKey>`, `EnumTypeDecl{ ${tbase}, members=List<CString>{ ${fields} } }`];
    }

    private emitTypedeclTypeDecl(ns: FullyQualifiedNamespace, tdecl: TypedeclTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        const tbase = this.emitAbstractNominalTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        return [`${EmitNameManager.generateTypeKey(tsig)}<TypeKey>`, `TypedeclTypeDecl{ ${tbase}, valuetype=${this.emitTypeSignature(tdecl.valuetype)} }`];
    }

    private emitTypedeclStringOfTypeDecl(ns: FullyQualifiedNamespace, tdecl: TypedeclTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        const tbase = this.emitAbstractNominalTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);
    
        return [`${EmitNameManager.generateTypeKey(tsig)}<TypeKey>`, `TypedeclStringOfTypeDecl{ ${tbase}, valuetype=${this.emitTypeSignature(tdecl.valuetype)}, ofexp=${this.emitExpression((tdecl.optofexp as LiteralExpressionValue).exp)} }`];
    }

    private emitInternalEntityTypeDeclBase(ns: FullyQualifiedNamespace, tsig: NominalTypeSignature, tdecl: InternalEntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): string {
        return this.emitAbstractEntityTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);
    }

    private emitPrimitiveEntityTypeDecl(ns: FullyQualifiedNamespace, tdecl: PrimitiveEntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        const ibase = this.emitInternalEntityTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        return [`${EmitNameManager.generateTypeKey(tsig)}<TypeKey>`, `PrimitiveEntityTypeDecl{ ${ibase} }`];
    }

    private emitOkTypeDecl(ns: FullyQualifiedNamespace, tdecl: OkTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T", "E"]);
        const ibase = this.emitInternalEntityTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        return [`${EmitNameManager.generateTypeKey(tsig)}<TypeKey>`, `OkTypeDecl{ ${ibase}, oktype=${this.emitTypeSignature(tsig.alltermargs[0])}, failtype=${this.emitTypeSignature(tsig.alltermargs[1])} }`];
    }

    private emitFailTypeDecl(ns: FullyQualifiedNamespace, tdecl: FailTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T", "E"]);
        const ibase = this.emitInternalEntityTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        return [`${EmitNameManager.generateTypeKey(tsig)}<TypeKey>`, `FailTypeDecl{ ${ibase}, oktype=${this.emitTypeSignature(tsig.alltermargs[0])}, failtype=${this.emitTypeSignature(tsig.alltermargs[1])} }`];
    }

    private emitAPIRejectedTypeDecl(ns: FullyQualifiedNamespace, tdecl: APIRejectedTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        assert(false, "Not implemented -- emitAPIRejectedTypeDecl");
    }

    private emitAPIFailedTypeDecl(ns: FullyQualifiedNamespace, tdecl: APIFailedTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        assert(false, "Not implemented -- emitAPIFailedTypeDecl");
    }

    private emitAPIErrorTypeDecl(ns: FullyQualifiedNamespace, tdecl: APIErrorTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        assert(false, "Not implemented -- emitAPIErrorTypeDecl");
    }

    private emitAPISuccessTypeDecl(ns: FullyQualifiedNamespace, tdecl: APISuccessTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        assert(false, "Not implemented -- emitAPISuccessTypeDecl");
    }

    private emitSomeTypeDecl(ns: FullyQualifiedNamespace, tdecl: SomeTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        const ibase = this.emitInternalEntityTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        return [`${EmitNameManager.generateTypeKey(tsig)}<TypeKey>`, `SomeTypeDecl{ ${ibase}, oftype=${this.emitTypeSignature(tsig.alltermargs[0])} }`];
    }

    private emitMapEntryTypeDecl(ns: FullyQualifiedNamespace, tdecl: MapEntryTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        assert(false, "Not implemented -- emitMapEntryTypeDecl");
    }

    private emitListTypeDecl(ns: FullyQualifiedNamespace, tdecl: ListTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const ibase = this.emitInternalEntityTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        return [`${EmitNameManager.generateTypeKey(tsig)}<TypeKey>`, `ListTypeDecl{ ${ibase}, oftype=${this.emitTypeSignature(tsig.alltermargs[0])} }`];
    }

    private emitStackTypeDecl(ns: FullyQualifiedNamespace, tdecl: StackTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        assert(false, "Not implemented -- emitStackTypeDecl");
    }

    private emitQueueTypeDecl(ns: FullyQualifiedNamespace, tdecl: QueueTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        assert(false, "Not implemented -- emitQueueTypeDecl");
    }

    private emitSetTypeDecl(ns: FullyQualifiedNamespace, tdecl: SetTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        assert(false, "Not implemented -- emitSetTypeDecl");
    }

    private emitMapTypeDecl(ns: FullyQualifiedNamespace, tdecl: MapTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        assert(false, "Not implemented -- emitMapTypeDecl");
    }

    private emitEventListTypeDecl(ns: FullyQualifiedNamespace, tdecl: EventListTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        assert(false, "Not implemented -- emitEventListTypeDecl");
    }

    private emitEntityTypeDecl(ns: FullyQualifiedNamespace, tdecl: EntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const ibase = this.emitAbstractEntityTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);
        
        const mfields = tdecl.fields.map((f) => this.emitMemberFieldDecl(ns, tsig, f)).join(", ");
        return [`${EmitNameManager.generateTypeKey(tsig)}<TypeKey>`, `EntityTypeDecl{ ${ibase}, fields=List<MemberFieldDecl>{ ${mfields} } }`];
    }

    private emitAbstractConceptTypeDeclBase(ns: FullyQualifiedNamespace, tsig: NominalTypeSignature, tdecl: AbstractConceptTypeDecl, instantiation: TypeInstantiationInfo, subtypes: TypeSignature[], fmt: BsqonCodeFormatter): string {
        const ccbase = this.emitAbstractNominalTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        const tss = subtypes.map((st) => this.emitTypeSignature(st)).join(", ");
        return `AbstractConceptTypeDecl{ ${ccbase}, subtypes=List<NominalTypeSignature>{ ${tss} } }`;
    }

    private emitOptionTypeDecl(ns: FullyQualifiedNamespace, tdecl: OptionTypeDecl, instantiation: TypeInstantiationInfo, subtypes: TypeSignature[], fmt: BsqonCodeFormatter): [string, string] {
        const tsig = BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const ibase = this.emitAbstractConceptTypeDeclBase(ns, tsig, tdecl, instantiation, subtypes, fmt);

        const oftype = this.emitTypeSignature(tsig.alltermargs[0]);

        const somedecl = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Some") as AbstractNominalTypeDecl;
        const sometype = new NominalTypeSignature(tdecl.sinfo, undefined, somedecl, tsig.alltermargs);

        return [`${EmitNameManager.generateTypeKey(tsig)}<TypeKey>`, `OptionTypeDecl{ ${ibase}, oftype=${oftype}, sometype=${this.emitTypeSignature(sometype)} }`];
    }

    private emitResultTypeDecl(ns: FullyQualifiedNamespace, tdecl: ResultTypeDecl, instantiation: TypeInstantiationInfo, subtypes: TypeSignature[], fmt: BsqonCodeFormatter): [string, string] {
        assert(false, "Not implemented -- emitResultTypeDecl");
    }

    private emitAPIResultTypeDecl(ns: FullyQualifiedNamespace, tdecl: APIResultTypeDecl, instantiation: TypeInstantiationInfo, subtypes: TypeSignature[], fmt: BsqonCodeFormatter): [string, string] {
        assert(false, "Not implemented -- emitAPIResultTypeDecl");
    }

    private emitConceptTypeDecl(ns: FullyQualifiedNamespace, tdecl: ConceptTypeDecl, instantiation: TypeInstantiationInfo, subtypes: TypeSignature[], fmt: BsqonCodeFormatter): [string, string] {
        const tsig = BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const ibase = this.emitAbstractConceptTypeDeclBase(ns, tsig, tdecl, instantiation, subtypes, fmt);

        const fields = tdecl.fields.map((f) => this.emitMemberFieldDecl(ns, tsig, f)).join(", ");
        return [`${EmitNameManager.generateTypeKey(tsig)}<TypeKey>`, `ConceptTypeDecl{ ${ibase}, fields=List<MemberFieldDecl>{ ${fields} } }`];
    }

    private emitDatatypeMemberEntityTypeDecl(ns: FullyQualifiedNamespace, tdecl: DatatypeMemberEntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const ibase = this.emitAbstractEntityTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        const fields = tdecl.fields.map((f) => this.emitMemberFieldDecl(ns, tsig, f)).join(", ");
        const parenttype = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl.parentTypeDecl, tsig.alltermargs);

        return [`${EmitNameManager.generateTypeKey(tsig)}<TypeKey>`, `DatatypeMemberEntityTypeDecl{ ${ibase}, fields=List<MemberFieldDecl>{ ${fields} }, parentTypeDecl=${this.emitTypeSignature(parenttype)} }`];
    }

    private emitDatatypeTypeDecl(ns: FullyQualifiedNamespace, tdecl: DatatypeTypeDecl, instantiation: TypeInstantiationInfo, subtypes: TypeSignature[], fmt: BsqonCodeFormatter): [string, string] {
        const tsig = BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const ibase = this.emitAbstractConceptTypeDeclBase(ns, tsig, tdecl, instantiation, subtypes, fmt);

        const fields = tdecl.fields.map((f) => this.emitMemberFieldDecl(ns, tsig, f)).join(", ");
        const associatedMemberEntityDecls = tdecl.associatedMemberEntityDecls.map((dd) => this.emitTypeSignature(new NominalTypeSignature(dd.sinfo, undefined, dd, tsig.alltermargs))).join(", ");

        return [`${EmitNameManager.generateTypeKey(tsig)}<TypeKey>`, `DatatypeTypeDecl{ ${ibase}, fields=List<MemberFieldDecl>{ ${fields} }, associatedMemberEntityDecls=List<NominalTypeSignature>{ ${associatedMemberEntityDecls} } }`];
    }

    private emitNamespaceConstDecls(ns: FullyQualifiedNamespace, decls: NamespaceConstDecl[], fmt: BsqonCodeFormatter) {
        for(let i = 0; i < decls.length; ++i) {
            const dd = decls[i];

            const dbase = this.emitAbstractCoreDecl(dd, EmitNameManager.generateNamespaceKey(ns));
            const dtype = this.emitTypeSignature(dd.declaredType);
            const value = this.emitExpression(dd.value.exp);

            this.nsconsts.push(`NamespaceConstDecl{ ${dbase}, declaredType=${dtype}, value=${value} }`);
        }
    }

    private emitNamespaceTypeDecls(ns: NamespaceDeclaration, tdecl: AbstractNominalTypeDecl[], asminstantiation: NamespaceInstantiationInfo, fmt: BsqonCodeFormatter)  {
        for(let i = 0; i < tdecl.length; ++i) {
            const tt = tdecl[i];
            const iinsts = asminstantiation.typebinds.get(tt.name);
            if(iinsts === undefined) {
                continue;
            }
            
            for(let j = 0; j < iinsts.length; ++j) {
                const instantiation = iinsts[j];

                this.mapper = instantiation.binds;

                const subtypes: TypeSignature[] = this.getSubtypes(tt, instantiation.binds);

                if(tt instanceof EnumTypeDecl) {
                    const [tkey, decl] = this.emitEnumTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.enums.push(decl);
                }
                else if(tt instanceof TypedeclTypeDecl) {
                    if(tt.optofexp === undefined) {
                        const [tkey, decl] = this.emitTypedeclTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                        this.allconcretetypes.push(tkey);
                        this.typedecls.push(decl);
                    }
                    else {
                        const [tkey, decl] = this.emitTypedeclStringOfTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                        this.allconcretetypes.push(tkey);
                        this.typedecls.push(decl);
                    }
                }
                else if(tt instanceof PrimitiveEntityTypeDecl) {
                    const [tkey, decl] = this.emitPrimitiveEntityTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.primtives.push(decl);
                }
                else if(tt instanceof OkTypeDecl) {
                    const [tkey, decl] = this.emitOkTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.constructables.push(decl);
                }
                else if(tt instanceof FailTypeDecl) {
                    const [tkey, decl] = this.emitFailTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.constructables.push(decl);
                }
                else if(tt instanceof APIRejectedTypeDecl) {
                    const [tkey, decl] = this.emitAPIRejectedTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.constructables.push(decl);
                }
                else if(tt instanceof APIFailedTypeDecl) {
                    const [tkey, decl] = this.emitAPIFailedTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.constructables.push(decl);
                }
                else if(tt instanceof APIErrorTypeDecl) {
                    const [tkey, decl] = this.emitAPIErrorTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.constructables.push(decl);
                }
                else if(tt instanceof APISuccessTypeDecl) {
                    const [tkey, decl] = this.emitAPISuccessTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.constructables.push(decl);
                }
                else if(tt instanceof SomeTypeDecl) {
                    const [tkey, decl] = this.emitSomeTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.constructables.push(decl);
                }
                else if(tt instanceof MapEntryTypeDecl) {
                    const [tkey, decl] = this.emitMapEntryTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.constructables.push(decl);
                }
                else if(tt instanceof ListTypeDecl) {
                    const [tkey, decl] = this.emitListTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.collections.push(decl);
                }
                else if(tt instanceof StackTypeDecl) {
                    const [tkey, decl] = this.emitStackTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.collections.push(decl);
                }
                else if(tt instanceof QueueTypeDecl) {
                    const [tkey, decl] = this.emitQueueTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.collections.push(decl);
                }
                else if(tt instanceof SetTypeDecl) {
                    const [tkey, decl] = this.emitSetTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.collections.push(decl);
                }
                else if(tt instanceof MapTypeDecl) {
                    const [tkey, decl] = this.emitMapTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.collections.push(decl);
                }
                else if(tt instanceof EventListTypeDecl) {
                    const [tkey, decl] = this.emitEventListTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.collections.push(decl);
                }
                else if(tt instanceof EntityTypeDecl) {
                    const [tkey, decl] = this.emitEntityTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.entities.push(decl);
                }
                else if(tt instanceof OptionTypeDecl) {
                    const [tkey, decl] = this.emitOptionTypeDecl(ns.fullnamespace, tt, instantiation, subtypes, fmt);
                    this.allabstracttypes.push(tkey);
                    this.pconcepts.push(decl);
                }
                else if(tt instanceof ResultTypeDecl) {
                    const [tkey, decl] = this.emitResultTypeDecl(ns.fullnamespace, tt, instantiation, subtypes, fmt);
                    this.allabstracttypes.push(tkey);
                    this.pconcepts.push(decl);
                }
                else if(tt instanceof APIResultTypeDecl) {
                    const [tkey, decl] = this.emitAPIResultTypeDecl(ns.fullnamespace, tt, instantiation, subtypes, fmt);
                    this.allabstracttypes.push(tkey);
                    this.pconcepts.push(decl);
                }
                else if(tt instanceof ConceptTypeDecl) {
                    const [tkey, decl] = this.emitConceptTypeDecl(ns.fullnamespace, tt, instantiation, subtypes, fmt);
                    this.allabstracttypes.push(tkey);
                    this.concepts.push(decl);
                }
                else if(tt instanceof DatatypeMemberEntityTypeDecl) {
                    const [tkey, decl] = this.emitDatatypeMemberEntityTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.datamembers.push(decl);
                }
                else if(tt instanceof DatatypeTypeDecl) {
                    const [tkey, decl] = this.emitDatatypeTypeDecl(ns.fullnamespace, tt, instantiation, subtypes, fmt);
                    this.allabstracttypes.push(tkey);
                    this.datatypes.push(decl);
                }
                else {
                    assert(false, "Unknown type decl kind");
                }

                this.mapper = undefined;
            }
        }
    }

    private emitNamespaceDeclaration(decl: NamespaceDeclaration, asminstantiation: NamespaceInstantiationInfo, aainsts: NamespaceInstantiationInfo[], fmt: BsqonCodeFormatter) {
        for(let i = 0; i < decl.subns.length; ++i) {
            const subdecl = decl.subns[i];
            const nsii = aainsts.find((ai) => ai.ns.emit() === subdecl.fullnamespace.emit());
            
            if(nsii !== undefined) {
                this.emitNamespaceDeclaration(decl.subns[i], nsii, aainsts, fmt);
            }
        }

        this.emitNamespaceConstDecls(decl.fullnamespace, decl.consts, fmt);

        this.emitFunctionDecls(decl.fullnamespace, undefined, decl.functions.map((fd) => [fd, asminstantiation.functionbinds.get(fd.name)]), fmt);
        
        this.emitNamespaceTypeDecls(decl, decl.typedecls, asminstantiation, fmt);
    }

    private computeSubtypes() {
        //
        //TODO: this is a NOP we need to implement this -- walk all namespaces/types/instantiations and build an inverse map that we lookup below
        //
    }

    private getSubtypes(tt: AbstractNominalTypeDecl, binds: TemplateNameMapper | undefined): TypeSignature[] {
        return [];    
    }

    static emitAssembly(assembly: Assembly, asminstantiation: NamespaceInstantiationInfo[]): string {
        const emitter = new BSQIREmitter(assembly, asminstantiation, false, undefined, undefined);
        emitter.computeSubtypes();

        //emit each of the assemblies
        for(let i = 0; i < assembly.toplevelNamespaces.length; ++i) {
            const nsdecl = assembly.toplevelNamespaces[i];
            const nsii = asminstantiation.find((ai) => ai.ns.emit() === nsdecl.fullnamespace.emit());
            
            if(nsii !== undefined) {
                emitter.emitNamespaceDeclaration(nsdecl, nsii, asminstantiation, new BsqonCodeFormatter(0));
            }
        }

        let fmt = new BsqonCodeFormatter(4);

        return "Assembly{\n" +
            fmt.indent(`List<NamespaceConstDecl>{ ${emitter.nsconsts.join(", ")} },\n`) +
            fmt.indent(`List<ConstMemberDecl>{ ${emitter.typeconsts.join(", ")} },\n`) +

            fmt.indent(`Map<InvokeKey, NamespaceFunctionDecl>{ ${emitter.nsfuncs.join(", ")} },\n`) +
            fmt.indent(`Map<InvokeKey, TypeFunctionDecl>{ ${emitter.typefuncs.join(", ")} },\n`) +
            
            fmt.indent(`Map<InvokeKey, MethodDeclAbstract>{ ${emitter.absmethods.join(", ")} },\n`) +
            fmt.indent(`Map<InvokeKey, MethodDeclVirtual>{ ${emitter.virtmethods.join(", ")} },\n`) +
            fmt.indent(`Map<InvokeKey, MethodDeclOverride>{ ${emitter.overmethods.join(", ")} },\n`) +
            fmt.indent(`Map<InvokeKey, MethodDeclStatic>{ ${emitter.staticmethods.join(", ")} },\n`) +
            
            fmt.indent(`Map<TypeKey, EnumTypeDecl>{ ${emitter.enums.join(", ")} },\n`) +
            fmt.indent(`Map<TypeKey, TypedeclTypeDecl>{ ${emitter.typedecls.join(", ")} },\n`) +
            fmt.indent(`Map<TypeKey, PrimitiveEntityTypeDecl>{ ${emitter.primtives.join(", ")} },\n`) +
            fmt.indent(`Map<TypeKey, ConstructableTypeDecl>{ ${emitter.constructables.join(", ")} },\n`) +
            fmt.indent(`Map<TypeKey, CollectionTypeDecl>{ ${emitter.collections.join(", ")} },\n`) +
            fmt.indent(`Map<TypeKey, EntityTypeDecl>{ ${emitter.entities.join(", ")} },\n`) +
            fmt.indent(`Map<TypeKey, DatatypeMemberEntityTypeDecl>{ ${emitter.datamembers.join(", ")} },\n`) +
            
            fmt.indent(`Map<TypeKey, PrimitiveConceptTypeDecl>{ ${emitter.pconcepts.join(", ")} },\n`) +
            fmt.indent(`Map<TypeKey, ConceptTypeDecl>{ ${emitter.concepts.join(", ")} },\n`) +
            fmt.indent(`Map<TypeKey, DatatypeTypeDecl>{ ${emitter.datatypes.join(", ")} },\n`) +
            
            fmt.indent(`List<InvokeKey>{ ${emitter.allfuncs.join(", ")} },\n`) +
            fmt.indent(`List<InvokeKey>{ ${emitter.allmethods.join(", ")} },\n`) +
            fmt.indent(`List<InvokeKey>{ ${emitter.allvmethods.join(", ")} },\n`) +
            
            fmt.indent(`List<TypeKey>{ ${emitter.allconcretetypes.join(", ")} },\n`) +
            fmt.indent(`List<TypeKey>{ ${emitter.allabstracttypes.join(", ")} }\n`) +
        "}";
    }
}

export {
    BSQIREmitter
};
