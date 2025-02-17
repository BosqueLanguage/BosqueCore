import assert from "node:assert";

import { AbstractCollectionTypeDecl, Assembly, ConstructableTypeDecl, EntityTypeDecl, FunctionInvokeDecl, MemberFieldDecl, MethodDecl, NamespaceDeclaration, NamespaceFunctionDecl, TestAssociation, TypedeclTypeDecl } from "./assembly.js";
import { NamespaceInstantiationInfo } from "./instantiation_map.js";
import { BuildLevel, SourceInfo } from "./build_decls.js";
import { EListTypeSignature, FullyQualifiedNamespace, LambdaParameterSignature, LambdaTypeSignature, NominalTypeSignature, RecursiveAnnotation, TemplateNameMapper, TypeSignature, VoidTypeSignature } from "./type.js";
import { AbortStatement, AccessEnumExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, ArgumentList, ArgumentValue, AssertStatement, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndExpression, BinLogicIFFExpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, BlockStatement, BodyImplementation, CallNamespaceFunctionExpression, CallRefSelfExpression, CallRefThisExpression, CallRefVariableExpression, CallTaskActionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, CreateDirectExpression, DebugStatement, EmptyStatement, Expression, ExpressionTag, IfElifElseStatement, IfElseStatement, IfExpression, IfStatement, ITest, KeyCompareEqExpression, KeyCompareLessExpression, LambdaInvokeExpression, LetExpression, LiteralNoneExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralTypeDeclValueExpression, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, MatchStatement, NamedArgumentValue, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PositionalArgumentValue, PostfixAccessFromIndex, PostfixAccessFromName, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixLiteralKeyAccess, PostfixOp, PostfixOperation, PostfixOpTag, PostfixProjectFromNames, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, RefArgumentValue, ReturnMultiStatement, ReturnSingleStatement, ReturnVoidStatement, SafeConvertExpression, SelfUpdateStatement, SpecialConstructorExpression, SpreadArgumentValue, Statement, StatementTag, SwitchStatement, TaskAllExpression, TaskDashExpression, TaskMultiExpression, TaskRaceExpression, TaskRunExpression, ThisUpdateStatement, ValidateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VariableRetypeStatement, VarUpdateStatement, VoidRefCallStatement } from "./body.js";

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
    readonly mode: "release" | "debug";
    readonly buildlevel: BuildLevel;

    readonly generateTestInfo: boolean;
    readonly testfilefilter: string[] | undefined;
    readonly testfilters: TestAssociation[] | undefined;

    //map from files with tests to the list of tests
    readonly testgroups: [string, string[]][] = [];

    mapper: TemplateNameMapper | undefined;

    constructor(assembly: Assembly, asminstantiation: NamespaceInstantiationInfo[], mode: "release" | "debug", buildlevel: BuildLevel, generateTestInfo: boolean, testfilefilter: string[] | undefined, testfilters: TestAssociation[] | undefined) {
        this.assembly = assembly;
        this.asminstantiation = asminstantiation;

        this.mode = mode;
        this.buildlevel = buildlevel;

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
        xxxx;
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

    private emitFunctionDecl(fdecl: FunctionInvokeDecl, optenclosingtype: [NominalTypeSignature, TemplateNameMapper | undefined] | undefined, optmapping: TemplateNameMapper | undefined, fmt: BsqonCodeFormatter): string {
        const omap = this.mapper;
        if(optmapping !== undefined) {
            this.mapper = TemplateNameMapper.tryMerge(optenclosingtype !== undefined ? optenclosingtype[1] : undefined, optmapping);
        }

        const sig = this.emitExplicitInvokeFunctionDeclSignature(fdecl);

        let initializers: string[] = [];
        let preconds: string[] = [];
        let refsaves: string[] = [];
        const ensures = this.checkExplicitFunctionInvokeDeclMetaData(fdecl, initializers, preconds, refsaves);

        let resf: string | undefined = undefined;
        let resfimpl: string | undefined = undefined;
        if(ensures.length !== 0) {
            //TODO: we will need to handle ref params here too
            assert(fdecl.params.every((p) => !p.isRefParam), "Not implemented -- checkEnsuresRefParams");

            const resb = [...ensures.map((e) => fmt.indent(e)), fmt.indent("return $return;")].join(fmt.nl());

            let [resf, rss] = fdecl instanceof NamespaceFunctionDecl ? EmitNameManager.generateOnCompleteDeclarationNameForNamespaceFunction(this.getCurrentNamespace(), fdecl as NamespaceFunctionDecl, optmapping) : [EmitNameManager.generateOnCompleteDeclarationNameForTypeFunction(fdecl as TypeFunctionDecl, optmapping), true];
            const decl = `(${fdecl.params.map((p) => p.name).join(", ")}, $return)${rss ? " => " : " "}{${fmt.nl()}${resb}${fmt.nl()}${fmt.indent("}")}`;
            if(fdecl instanceof NamespaceFunctionDecl || optmapping !== undefined) {
                resfimpl = `${resf}${decl}`;
            }
            else {
                resfimpl = `${resf} { value: ${decl} }`;
            }
        }

        const optrefv = fdecl.params.find((p) => p.isRefParam);
        const body = this.emitBodyImplementation(fdecl.body, false, initializers, preconds, refsaves, optrefv !== undefined ? optrefv.name : undefined, resf, fmt);
        this.mapper = omap;

        const [nf, nss] = fdecl instanceof NamespaceFunctionDecl ? EmitNameManager.generateDeclarationNameForNamespaceFunction(this.getCurrentNamespace(), fdecl as NamespaceFunctionDecl, optmapping) : [EmitNameManager.generateDeclarationNameForTypeFunction(fdecl as TypeFunctionDecl, optmapping), true];
        const decl = `${sig}${nss ? " => " : " "}${body}`;
        let bdecl: string;
        if(fdecl instanceof NamespaceFunctionDecl || optmapping !== undefined) {
            bdecl = `${nf}${decl}`;
        }
        else {
            bdecl = `${nf} { value: ${decl} }`;
        }
        
        if(fdecl instanceof NamespaceFunctionDecl) {
            if(fdecl.fkind === "errtest" || fdecl.fkind === "chktest" || fdecl.fkind === "example") {
                this.emitTestCallForFunctionDecl(fdecl);
            }
        }

        return {body: bdecl, resfimpl: resfimpl};
    }

    private emitFunctionDecls(optenclosingtype: [NominalTypeSignature, TemplateNameMapper | undefined] | undefined, fdecls: [FunctionInvokeDecl, FunctionInstantiationInfo | undefined][], fmt: JSCodeFormatter): string[] {
        let decls: string[] = [];
        let tests: string[] = [];

        for(let i = 0; i < fdecls.length; ++i) {
            const fdecl = fdecls[i][0];
            const fii = fdecls[i][1]; 
    
            this.currentfile = fdecl.file;

            if(fii !== undefined) {
                if(fii.binds === undefined) {
                    const {body, resfimpl} = this.emitFunctionDecl(fdecl, optenclosingtype, undefined, fmt);
            
                    if(resfimpl !== undefined) {
                        decls.push(resfimpl);
                    }
                    decls.push(body);
                
                    tests.push(...tests);
                }
                else {
                    fmt.indentPush();
                    let idecls: string[] = []
                    for(let j = 0; j < fii.binds.length; ++j) {
                        const {body, resfimpl} = this.emitFunctionDecl(fdecl, optenclosingtype, fii.binds[j], fmt);
            
                        if(resfimpl !== undefined) {
                            idecls.push(fmt.indent(resfimpl));
                        }
                        idecls.push(fmt.indent(body));

                        tests.push(...tests);
                    }
                    fmt.indentPop();

                    if(fdecl instanceof NamespaceFunctionDecl) {
                        if(this.getCurrentNamespace().isTopNamespace()) {
                            const fobj = `export const ${fdecl.name} = {${fmt.nl()}${idecls.map((dd) => dd).join("," + fmt.nl())}${fmt.nl()}${fmt.indent("}")}`;
                            decls.push(fobj);
                        }
                        else {
                            const fobj = `${fdecl.name}: {${fmt.nl()}${idecls.map((dd) => dd).join("," + fmt.nl())}${fmt.nl()}${fmt.indent("}")}`;
                            decls.push(fobj);
                        }
                    }
                    else {
                        const fobj = `${fdecl.name}: { value: {${fmt.nl()}${idecls.map((dd) => dd).join("," + fmt.nl())}${fmt.nl()}${fmt.indent("}")} }`;
                        decls.push(fobj);                      
                    }
                }
            }
        }

        return decls;
    }
}

export {
    BSQIREmitter
};
