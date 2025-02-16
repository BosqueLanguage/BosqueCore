import assert from "node:assert";

import { AbstractCollectionTypeDecl, AbstractNominalTypeDecl, Assembly, ConstructableTypeDecl, EntityTypeDecl, ListTypeDecl, MapTypeDecl, MethodDecl, NamespaceDeclaration, NamespaceFunctionDecl, PrimitiveEntityTypeDecl, TestAssociation, TypedeclTypeDecl } from "./assembly.js";
import { NamespaceInstantiationInfo } from "./instantiation_map.js";
import { BuildLevel, SourceInfo } from "./build_decls.js";
import { EListTypeSignature, FullyQualifiedNamespace, LambdaParameterSignature, LambdaTypeSignature, NominalTypeSignature, RecursiveAnnotation, TemplateNameMapper, TypeSignature, VoidTypeSignature } from "./type.js";
import { AccessEnumExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, ArgumentList, ArgumentValue, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinMultExpression, BinSubExpression, CallNamespaceFunctionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, CreateDirectExpression, Expression, ITest, LambdaInvokeExpression, LetExpression, LiteralNoneExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralTypeDeclValueExpression, LogicActionAndExpression, LogicActionOrExpression, NamedArgumentValue, ParseAsTypeExpression, PositionalArgumentValue, PostfixAccessFromIndex, PostfixAccessFromName, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixLiteralKeyAccess, PostfixOp, PostfixOperation, PostfixOpTag, PostfixProjectFromNames, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, RefArgumentValue, SpecialConstructorExpression, SpreadArgumentValue } from "./body.js";


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

    currentfile: string | undefined;
    currentns: NamespaceDeclaration | undefined;

    mapper: TemplateNameMapper | undefined;
    optrefreturn: string | undefined = undefined;
    returncompletecall: string | undefined = undefined;

    bindernames: Set<string> = new Set();

    constructor(assembly: Assembly, asminstantiation: NamespaceInstantiationInfo[], mode: "release" | "debug", buildlevel: BuildLevel, generateTestInfo: boolean, testfilefilter: string[] | undefined, testfilters: TestAssociation[] | undefined) {
        this.assembly = assembly;
        this.asminstantiation = asminstantiation;

        this.mode = mode;
        this.buildlevel = buildlevel;

        this.generateTestInfo = generateTestInfo;
        this.testfilefilter = testfilefilter;
        this.testfilters = testfilters;

        this.currentfile = undefined;
        this.currentns = undefined;
    }

    private tproc(ttype: TypeSignature): TypeSignature {
        return this.mapper !== undefined ? ttype.remapTemplateBindings(this.getTemplateMapper()) : ttype;
    }

    private getCurrentNamespace(): NamespaceDeclaration {
        assert(this.currentns !== undefined, "Current namespace is not set");
        return this.currentns;
    }

    private getCurrentINNS(): string {
        assert(this.currentns !== undefined, "Current namespace is not set");
        return '"' + this.currentns.fullnamespace.ns.join("::") + '"';
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

    private emitArgumentListSinglePositional(exp: Expression): string {
        const arg = `PositionalArgumentValue{ exp=${this.emitExpression(exp)} }`
        return `ArgumentList{ List<ArgumentValue>{${arg}} }`;
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
            xxxx;
            const opcheck = cdecl.optofexp !== undefined ? `some(${this.emitExpression(cdecl.optofexp.exp)}` : "none";
            return `ConstructorTypeDeclStringExpression{ ${cpee}, invchecks=${invchecks}, opcheck=${opcheck} }`;
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

        const sinfocc = exp.shuffleinfo.map((si) => `(|${si[0]}i, ${this.emitTypeSignature(si[1])}|)`).join(", ");
        const resttypecc = exp.resttype !== undefined ? `some(this.emitTypeSignature(exp.resttype))` : "none"
        const restinfocc = (exp.restinfo || []).map((ri) => `(|${ri[0]}i, ${ri[1]}, ${this.emitTypeSignature(ri[2])}|)`).join(", ");

        return `CallNamespaceFunctionExpression{ ${ebase}, ikey='${ikey}'<InvokeKey>, ns='${nskey}'<NamespaceKey>, name='${ffinv.name}'<Identifier>, rec=${this.emitRecInfo(exp.rec)}, args=${this.emitArgumentList(exp.args)}, shuffleinfo=List<(|Int, TypeSignature|)>{${sinfocc}}, resttype=${resttypecc}, restinfo=List<(|Int, Bool, TypeSignature|)>{${restinfocc}} }`;
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

        xxxx;
        return `PostfixAccessFromName{ ${opbase}, declaredInType=${declaredInType}, name='${exp.name}'<Identifier> }`;
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
        const rtrgt = (this.tproc(exp.resolvedTrgt as TypeSignature) as NominalTypeSignature);
        
        //TODO: same as emitCallTypeFunctionExpression

        assert(false, "Not Implemented -- emitResolvedPostfixInvoke");
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
                    assert(op.tag === PostfixOpTag.PostfixError, "Unknown postfix op");
                }
            }
        });

        return `PostfixOp{ rootExp=${rootExp}, ops=List<PostfixOp>{${ops}} }`;
    }

    private emitPrefixNotOpExpression(exp: PrefixNotOpExpression): string {
        const optype = this.tproc(exp.opertype as TypeSignature);

        if(EmitNameManager.isPrimitiveType(optype)) {
            const ebase = this.emitExpressionBase(exp);
            return `PrefixNotOpExpression{ ${ebase}, exp=${this.emitExpression(exp.exp)}, opertype=${this.emitTypeSignature(optype)} }`;
        }
        else {
            const tdecl = ((optype as NominalTypeSignature).decl as TypedeclTypeDecl);
            const vtype = tdecl.valuetype;

            const vvexp = `TypeDeclPrimitiveFieldAccessExpression{ sinfo=${this.emitSourceInfo(exp.sinfo)}, etype=${vtype}, exp=${this.emitExpression(exp.exp)} }`;
            const nexp = `PrefixNotOpExpression{ sinfo=${this.emitSourceInfo(exp.sinfo)}, etype=${vtype}, exp=${vvexp}, opertype=${this.emitTypeSignature(vtype)} }`;
            const wrexp = `ConstructorTypeDeclExpression{ sinfo=${this.emitSourceInfo(exp.sinfo)}, etype=${optype}, args=ArgumentList{ List<ArgumentValue>{PositionalArgumentValue{ exp=${nexp} }} }, invchecks=${tdecl.invariants.length !== 0} }`;
            
            return wrexp;
        }
    }

    private emitPrefixNegateOrPlusOpExpression(exp: PrefixNegateOrPlusOpExpression): string {
        if(exp.op === "+") {
            return this.emitExpression(exp.exp);
        }
        else {
            const optype = this.tproc(exp.opertype as TypeSignature);
            
            if(EmitNameManager.isPrimitiveType(optype)) {
                const ebase = this.emitExpressionBase(exp);
                return `PrefixNegateOrPlusOpExpression{ sinfo=${ebase}, exp=${this.emitExpression(exp.exp)}, opertype=${this.emitTypeSignature(optype)} }`;
            }
            else {
                assert(false, "Not implemented -- PrefixNegateOrPlusOpExpression on typedecl (unwrap/wrap)");
            }
        }
    }

    private emitBinAddExpression(exp: BinAddExpression): string {
        const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
        const etype = this.tproc(exp.getType());

        let ccepr = "";
        if(!EmitNameManager.isPrimitiveType(etype)) {
            ccepr = `, ${EmitNameManager.generateAccessorForTypedeclTypeConstructor(this.getCurrentNamespace(), etype as NominalTypeSignature)}`;
        }

        return `_$add.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)}${ccepr})`;
    }

    private emitBinSubExpression(exp: BinSubExpression,): string {
        const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
        const etype = this.tproc(exp.getType());

        let ccepr = "";
        if(!EmitNameManager.isPrimitiveType(etype)) {
            ccepr = `, ${EmitNameManager.generateAccessorForTypedeclTypeConstructor(this.getCurrentNamespace(), etype as NominalTypeSignature)}`;
        }

        return `_$sub.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)}${ccepr})`;
    }
    
    private emitBinMultExpression(exp: BinMultExpression): string {
        const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
        const etype = this.tproc(exp.getType());

        let ccepr = "";
        if(!EmitNameManager.isPrimitiveType(etype)) {
            ccepr = `, ${EmitNameManager.generateAccessorForTypedeclTypeConstructor(this.getCurrentNamespace(), etype as NominalTypeSignature)}`;
        }

        return `_$mult.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)}${ccepr})`;
    }
    
    private emitBinDivExpression(exp: BinDivExpression): string {
        const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
        const etype = this.tproc(exp.getType());

        let ccepr = "";
        if(!EmitNameManager.isPrimitiveType(etype)) {
            ccepr = `, ${EmitNameManager.generateAccessorForTypedeclTypeConstructor(this.getCurrentNamespace(), etype as NominalTypeSignature)}`;
        }

        return `_$div.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)}${ccepr})`;
    }
    
    private emitBinKeyEqExpression(exp: BinKeyEqExpression): string {
        const kcop = exp.operkind;

        if(kcop === "lhsnone") {
            return `${this.emitExpression(exp.rhs, false)}._$isNone()`;
        }
        else if(kcop === "rhsnone") {
            return `${this.emitExpression(exp.lhs, false)}._$isNone()`;
        }
        else if(kcop === "lhskeyeqoption") {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fkeqopt.${optype}(${this.emitExpression(exp.rhs, true)}, ${this.emitExpression(exp.lhs, true)})`;
        }
        else if(kcop === "rhskeyeqoption") {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fkeqopt.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
        }
        else if(kcop === "stricteq") {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fkeq.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
        }
        else {
            assert(false, "Unknown key eq kind");
        }
    }

    private emitBinKeyNeqExpression(exp: BinKeyNeqExpression, toplevel: boolean): string {
        const kcop = exp.operkind;

        if(kcop === "lhsnone") {
            return `${this.emitExpression(exp.rhs, false)}._$isNotNone()`;
        }
        else if(kcop === "rhsnone") {
            return `${this.emitExpression(exp.lhs, false)}._$isNotNone()`;
        }
        else if(kcop === "lhskeyeqoption") {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fkneqopt.${optype}(${this.emitExpression(exp.rhs, true)}, ${this.emitExpression(exp.lhs, true)})`;
        }
        else if(kcop === "rhskeyeqoption") {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fkneqopt.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
        }
        else if(kcop === "stricteq") {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fkneq.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
        }
        else {
            assert(false, "Unknown key eq kind");
        }
    }

    private emitKeyCompareEqExpression(exp: KeyCompareEqExpression, toplevel: boolean): string {
        const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.optype as TypeSignature));
        return `_$fkeq.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
    }

    private emitKeyCompareLessExpression(exp: KeyCompareLessExpression, toplevel: boolean): string {
        const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.optype as TypeSignature));
        return `_$fkless.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
    }

    private emitNumericEqExpression(exp: NumericEqExpression, toplevel: boolean): string {
        if(EmitNameManager.isPrimitiveType(this.tproc(exp.lhs.getType() as TypeSignature))) {
            const eexp = `${this.emitExpression(exp.lhs, false)} === ${this.emitExpression(exp.rhs, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fnumeq.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;            
        }
    }

    private emitNumericNeqExpression(exp: NumericNeqExpression, toplevel: boolean): string {
        if(EmitNameManager.isPrimitiveType(this.tproc(exp.lhs.getType() as TypeSignature))) {
            const eexp = `${this.emitExpression(exp.lhs, false)} !== ${this.emitExpression(exp.rhs, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `(!_$fnumeq.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)}))`;
        }
    }
    
    private emitNumericLessExpression(exp: NumericLessExpression, toplevel: boolean): string {
        if(EmitNameManager.isPrimitiveType(this.tproc(exp.lhs.getType() as TypeSignature))) {
            const eexp = `${this.emitExpression(exp.lhs, false)} < ${this.emitExpression(exp.rhs, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fnumless.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
        }
    }
    
    private emitNumericLessEqExpression(exp: NumericLessEqExpression, toplevel: boolean): string {
        if(EmitNameManager.isPrimitiveType(this.tproc(exp.lhs.getType() as TypeSignature))) {
            const eexp = `${this.emitExpression(exp.lhs, false)} <= ${this.emitExpression(exp.rhs, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fnumlesseq.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
        }
    }
    
    private emitNumericGreaterExpression(exp: NumericGreaterExpression, toplevel: boolean): string {
        if(EmitNameManager.isPrimitiveType(this.tproc(exp.lhs.getType() as TypeSignature))) {
            const eexp = `${this.emitExpression(exp.lhs, false)} > ${this.emitExpression(exp.rhs, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fnumless.${optype}(${this.emitExpression(exp.rhs, true)}, ${this.emitExpression(exp.lhs, true)})`;
        }
    }

    private emitNumericGreaterEqExpression(exp: NumericGreaterEqExpression, toplevel: boolean): string {
        if(EmitNameManager.isPrimitiveType(this.tproc(exp.lhs.getType() as TypeSignature))) {
            const eexp = `${this.emitExpression(exp.lhs, false)} >= ${this.emitExpression(exp.rhs, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fnumlesseq.${optype}(${this.emitExpression(exp.rhs, true)}, ${this.emitExpression(exp.lhs, true)})`;
        }
    }

    private emitBinLogicAndExpression(exp: BinLogicAndExpression, toplevel: boolean): string {
        let ee1 = this.emitExpression(exp.lhs, !exp.purebool);
        let ee2 = this.emitExpression(exp.rhs, !exp.purebool);

        if(!exp.purebool) {
            ee1 = `_$bval${ee1}`;
            ee2 = `_$bval${ee2}`;
        }
        
        const eexp = `${ee1} && ${ee2}`;
        return !toplevel && exp.purebool ? `(${eexp})` : eexp;
    }

    private emitBinLogicOrExpression(exp: BinLogicOrExpression, toplevel: boolean): string {
        let ee1 = this.emitExpression(exp.lhs, !exp.purebool);
        let ee2 = this.emitExpression(exp.rhs, !exp.purebool);

        if(!exp.purebool) {
            ee1 = `_$bval${ee1}`;
            ee2 = `_$bval${ee2}`;
        }

        const eexp = `${ee1} || ${ee2}`;
        return !toplevel && exp.purebool ? `(${eexp})` : eexp;
    }

    private emitBinLogicImpliesExpression(exp: BinLogicImpliesExpression, toplevel: boolean): string {
        let ee1 = this.emitExpression(exp.lhs, !exp.purebool);
        let ee2 = this.emitExpression(exp.rhs, !exp.purebool);

        if(!exp.purebool) {
            ee1 = `_$bval${ee1}`;
            ee2 = `_$bval${ee2}`;
        }

        const eeexp = `!${ee1} || ${ee2}`;
        return !toplevel && exp.purebool ? `(${eeexp})` : eeexp;
    }

    private emitBinLogicIFFExpression(exp: BinLogicIFFExpression, toplevel: boolean): string {
        let ee1 = this.emitExpression(exp.lhs, !exp.purebool);
        let ee2 = this.emitExpression(exp.rhs, !exp.purebool);

        if(!exp.purebool) {
            ee1 = `_$bval${ee1}`;
            ee2 = `_$bval${ee2}`;
        }

        const eexp = `${ee1} === ${ee2}`;
        return !toplevel && exp.purebool ? `(${eexp})` : eexp;
    }
    
    private emitMapEntryConstructorExpression(exp: MapEntryConstructorExpression): string {
        let ekey = this.emitExpression(exp.kexp, true);
        let evalue = this.emitExpression(exp.vexp, true);

        const cname = EmitNameManager.generateAccessorForSpecialTypeConstructor(this.getCurrentNamespace(), this.tproc(exp.ctype as TypeSignature) as NominalTypeSignature);
        return `${cname}(${ekey}, ${evalue})`;
    }

    private emitExpression(exp: Expression): string {
        xxxx;
    }
}

export {
    BSQIREmitter
};
