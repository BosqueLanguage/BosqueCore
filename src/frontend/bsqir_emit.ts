import assert from "node:assert";

import { AbstractCollectionTypeDecl, AbstractConceptTypeDecl, AbstractCoreDecl, AbstractDecl, AbstractEntityTypeDecl, AbstractInvokeDecl, AbstractNominalTypeDecl, APIErrorTypeDecl, APIFailedTypeDecl, APIRejectedTypeDecl, APIResultTypeDecl, APISuccessTypeDecl, Assembly, ConceptTypeDecl, ConditionDecl, ConstMemberDecl, ConstructableTypeDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, DeclarationAttibute, EntityTypeDecl, EnumTypeDecl, EventListTypeDecl, ExplicitInvokeDecl, FailTypeDecl, FunctionInvokeDecl, InternalEntityTypeDecl, InvariantDecl, InvokeParameterDecl, ListTypeDecl, MapEntryTypeDecl, MapTypeDecl, MemberFieldDecl, MethodDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, OkTypeDecl, OptionTypeDecl, PostConditionDecl, PreConditionDecl, PrimitiveEntityTypeDecl, QueueTypeDecl, ResultTypeDecl, SetTypeDecl, SomeTypeDecl, StackTypeDecl, TestAssociation, TypedeclTypeDecl, ValidateDecl } from "./assembly.js";
import { FunctionInstantiationInfo, MethodInstantiationInfo, NamespaceInstantiationInfo, TypeInstantiationInfo } from "./instantiation_map.js";
import { SourceInfo } from "./build_decls.js";
import { EListTypeSignature, FullyQualifiedNamespace, LambdaParameterSignature, LambdaTypeSignature, NominalTypeSignature, RecursiveAnnotation, TemplateNameMapper, TemplateTypeSignature, TypeSignature, VoidTypeSignature } from "./type.js";
import { AbortStatement, AbstractBodyImplementation, AccessEnumExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, ArgumentList, ArgumentValue, AssertStatement, BinAddExpression, BinderInfo, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndExpression, BinLogicIFFExpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, BlockStatement, BodyImplementation, BuiltinBodyImplementation, CallNamespaceFunctionExpression, CallRefSelfExpression, CallRefThisExpression, CallRefVariableExpression, CallTaskActionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, CreateDirectExpression, DebugStatement, EmptyStatement, Expression, ExpressionBodyImplementation, ExpressionTag, IfElifElseStatement, IfElseStatement, IfExpression, IfStatement, ITest, ITestFail, ITestNone, ITestOk, ITestSome, ITestType, KeyCompareEqExpression, KeyCompareLessExpression, LambdaInvokeExpression, LetExpression, LiteralExpressionValue, LiteralNoneExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralTypeDeclValueExpression, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, MatchStatement, NamedArgumentValue, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PositionalArgumentValue, PostfixAccessFromIndex, PostfixAccessFromName, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixLiteralKeyAccess, PostfixOp, PostfixOperation, PostfixOpTag, PostfixProjectFromNames, PredicateUFBodyImplementation, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, RefArgumentValue, ReturnMultiStatement, ReturnSingleStatement, ReturnVoidStatement, SafeConvertExpression, SelfUpdateStatement, SpecialConstructorExpression, SpreadArgumentValue, StandardBodyImplementation, Statement, StatementTag, SwitchStatement, SynthesisBodyImplementation, TaskAllExpression, TaskDashExpression, TaskMultiExpression, TaskRaceExpression, TaskRunExpression, ThisUpdateStatement, ValidateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VariableRetypeStatement, VarUpdateStatement, VoidRefCallStatement } from "./body.js";

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

    formatListOf(prestr: string, l: string[], poststr: string): string {
        if(l.length === 0) {
            return `${this.indent(prestr)} ${poststr}`;
        }
        else {
            this.indentPush();
            const vstr = l.map((v) => this.indent(v));
            this.indentPop();

            return `${this.indent(prestr)}${this.nl()}${vstr.join(",\n")}${this.nl()}${this.indent(poststr)}`;
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
         if(!(tsig instanceof LambdaTypeSignature)) {
            return tsig.tkeystr;
        }
        else {
            return `${tsig.name}(${tsig.params.map((pp) => pp.emit()).join(", ")})->${tsig.resultType.tkeystr}`;
        }
    }

    static generateTermPostfixForInvoke(terms: TypeSignature[]): string {
        if(terms.length === 0) {
            return "";
        }
        else {
            return `<${terms.map((t) => t.tkeystr).join(", ")}>`;
        }
    }

    static generateNamespaceInvokeKey(ns: FullyQualifiedNamespace, name: string, terms: TypeSignature[]): string {
        return `${this.generateNamespaceKey(ns)}::${name}${this.generateTermPostfixForInvoke(terms)}`;
    }

    static generateTypeInvokeKey(tsig: TypeSignature, name: string, terms: TypeSignature[]): string {
        return `${this.generateTypeKey(tsig)}::${name}${this.generateTermPostfixForInvoke(terms)}`;
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

    subtypemap: Map<string, string[]> = new Map<string, string[]>();
    typegraph: Map<string, string[]> = new Map<string, string[]>();

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
        return `BSQAssembly::SourceInfo{ line=${info.line}n, column=${info.column}n, pos=${info.pos}n, span=${info.span}n }`;
    }

    private emitRecInfo(recinfo: RecursiveAnnotation): string {
        if(recinfo === "yes") {
            return "BSQAssembly::RecursiveAnnotation#RecursiveTag";
        }
        else if(recinfo === "no") {
            return "BSQAssembly::RecursiveAnnotation#NonRecursiveTag";
        }
        else {
            return "BSQAssembly::RecursiveAnnotation#CondRecursiveTag";
        }
    }

    private static uniqueifyChildrenHelper(cl: string[]): string[] {
        const result: string[] = [];

        for(let i = 0; i < cl.length; ++i) {
            if(!result.includes(cl[i])) {
                result.push(cl[i]);
            }
        }

        return result;
    }

    private emitChildrenTypes(ttype: TypeSignature): string[] {
        const tt = this.tproc(ttype);

        if(tt instanceof NominalTypeSignature) {
            return [EmitNameManager.generateTypeKey(tt)];
        }
        else if(tt instanceof EListTypeSignature) {
            return BSQIREmitter.uniqueifyChildrenHelper(tt.entries.flatMap((et) => this.emitChildrenTypes(et)));
        }
        else {
            assert(false, "Unknown type signature " + ttype.tkeystr);
        }
    }

    private emitChildrenTypesForAll(ttype: TypeSignature[]): string[] {
        return BSQIREmitter.uniqueifyChildrenHelper(ttype.flatMap((tt) => this.emitChildrenTypes(tt)));
    }

    private emitTypeSignatureBase(ttype: TypeSignature): string {
        return `sinfo=${this.emitSourceInfo(ttype.sinfo)}, tkeystr='${EmitNameManager.generateTypeKey(ttype)}'<TypeKey>`;
    }

    private emitLambdaParameterSignature(lps: LambdaParameterSignature): string {
        const ptype = this.emitTypeSignature(lps.type);
        return `BSQAssembly::LambdaParameterSignature{ pname='${lps.name || "_"}'<BSQAssembly::Identifier>, ptype=${ptype}, isRefParam=${lps.isRefParam}, isRestParam=${lps.isRestParam} }`;
    }

    private emitTypeSignature(ttype: TypeSignature): string {
        const tt = this.tproc(ttype);

        if(tt instanceof VoidTypeSignature) {
            return `BSQAssembly::VoidTypeSignature{ ${this.emitTypeSignatureBase(tt)} }`;
        }
        else if(tt instanceof NominalTypeSignature) {
            return `BSQAssembly::NominalTypeSignature{ ${this.emitTypeSignatureBase(tt)} }`;
        }
        else if(tt instanceof EListTypeSignature) {
            const entries = tt.entries.map((et) => this.emitTypeSignature(et)).join(", ");
            return `BSQAssembly::EListTypeSignature{ ${this.emitTypeSignatureBase(tt)}, entries=List<BSQAssembly::TypeSignature>{${entries}} }`;
        }
        else if(tt instanceof LambdaTypeSignature) {
            const tsbase = this.emitTypeSignatureBase(tt);
            const recinfo = this.emitRecInfo(tt.recursive);
            const ispred = tt.name === "pred";
            const tparams = tt.params.map((tp) => this.emitLambdaParameterSignature(tp)).join(", ");
            const tret = this.emitTypeSignature(tt.resultType);

            return `BSQAssembly::LambdaTypeSignature{ ${tsbase}, frecursive=${recinfo}, isPredLambda=${ispred}, params=List<BSQAssembly::LambdaParameterSignature>{${tparams}}, resultType=${tret} }`;
        }
        else {
            assert(false, "Unknown type signature " + ttype.tkeystr);
        }
    }

    private emitArgumentValue(arg: ArgumentValue): string {
        const eexp = this.emitExpression(arg.exp);

        if(arg instanceof RefArgumentValue) {
            return `BSQAssembly::RefArgumentValue{ exp=${eexp} }`;
        }
        else if(arg instanceof PositionalArgumentValue) {
            return `BSQAssembly::PositionalArgumentValue{ exp=${eexp} }`;
        }
        else if(arg instanceof NamedArgumentValue) {
            return `BSQAssembly::NamedArgumentValue{ exp=${eexp}, name='${arg.name}'<BSQAssembly::VarIdentifier> }`;
        }
        else if(arg instanceof SpreadArgumentValue) {
            return `BSQAssembly::SpreadArgumentValue{ exp=${eexp} }`;
        }
        else {
            assert(false, "Unknown argument value");
        }
    }

    private emitArgumentList(argl: ArgumentList): string {
        const args = argl.args.map((arg) => this.emitArgumentValue(arg)).join(", ");
        return `BSQAssembly::ArgumentList{ List<BSQAssembly::ArgumentValue>{${args}} }`;
    }

    private emitInvokeArgumentInfo(name: string, rec: RecursiveAnnotation, args: ArgumentList, shuffleinfo: [number, TypeSignature][], resttype: TypeSignature | undefined, restinfo: [number, boolean, TypeSignature][] | undefined) {
        const sinfocc = shuffleinfo.map((si) => {
            const iidx = si[0] !== -1 ? `some(${si[0]}n)` : "none";
            return `(|${iidx}, ${this.emitTypeSignature(si[1])}|)`
        }).join(", ");

        const restinfocc = (restinfo || []).map((ri) => {
            return `(|${ri[0]}n, ${ri[1]}, ${this.emitTypeSignature(ri[2])}|)`
        }).join(", ");

        const resttypecc = resttype !== undefined ? `some(${this.emitTypeSignature(resttype)})` : "none"
        
        return `BSQAssembly::InvokeArgumentInfo{ name='${name}'<BSQAssembly::Identifier>, rec=${this.emitRecInfo(rec)}, args=${this.emitArgumentList(args)}, shuffleinfo=List<(|Option<Nat>, BSQAssembly::TypeSignature|)>{${sinfocc}}, resttype=${resttypecc}, restinfo=List<(|Nat, Bool, BSQAssembly::TypeSignature|)>{${restinfocc}} }`;
    }

    private emitBinderInfo(binder: BinderInfo): string {
        return `BSQAssembly::BinderInfo{ srcname='${binder.srcname}'<BSQAssembly::VarIdentifier>, refineonfollow=${binder.refineonfollow} }`;
    }

    private emitITestGeneral(itest: ITest): string {
        return `isnot=${itest.isnot}`;
    }

    private emitITestType(itest: ITestType): string {
        return `BSQAssembly::ITestType{ ${this.emitITestGeneral(itest)}, ttype=${this.emitTypeSignature(itest.ttype)} }`;
    }

    private emitITestNone(itest: ITestNone): string {
        return `BSQAssembly::ITestNone{ ${this.emitITestGeneral(itest)} }`;
    }

    private emitITestSome(itest: ITestSome): string {
        return `BSQAssembly::ITestSome{ ${this.emitITestGeneral(itest)} }`;
    }

    private emitITestOk(itest: ITestOk): string {
        return `BSQAssembly::ITestOk{ ${this.emitITestGeneral(itest)} }`;
    }

    private emitITestFail(itest: ITestFail): string {
        return `BSQAssembly::ITestFail{ ${this.emitITestGeneral(itest)} }`;
    }

    private emitITest(itest: ITest): string {
        if(itest instanceof ITestType) {
            return this.emitITestType(itest);
        }
        else if(itest instanceof ITestNone) {
            return this.emitITestNone(itest);
        }
        else if(itest instanceof ITestSome) {
            return this.emitITestSome(itest);
        }
        else if(itest instanceof ITestOk) {
            return this.emitITestOk(itest);
        }
        else if(itest instanceof ITestFail) {
            return this.emitITestFail(itest);
        }
        else {
            assert(false, "Unknown ITest");
        }
    }

    private emitExpressionBase(exp: Expression): string {
        return `sinfo=${this.emitSourceInfo(exp.sinfo)}, etype=${this.emitTypeSignature(exp.getType())}`;
    }

    private emitLiteralNoneExpression(exp: LiteralNoneExpression): string {
        return `BSQAssembly::LiteralNoneExpression{ ${this.emitExpressionBase(exp)} }`;
    }

    private emitLiteralSimpleExpression(exp: LiteralSimpleExpression): string {
        return `BSQAssembly::LiteralSimpleExpression{ ${this.emitExpressionBase(exp)}, value='${exp.value}' }`;
    }

    private emitLiteralUnicodeRegexExpression(exp: LiteralRegexExpression): string {
        assert(false, "Not implemented -- LiteralRegex");
    }
    
    private emitLiteralCRegexExpression(exp: LiteralRegexExpression): string {
        assert(false, "Not implemented -- LiteralCRegex");
    }
    
    private emitLiteralCCharExpression(exp: LiteralSimpleExpression): string {
        return `BSQAssembly::LiteralCCharExpression{ ${this.emitExpressionBase(exp)}, value=${exp.value} }`
    }

    private emitLiteralUnicodeCharExpression(exp: LiteralSimpleExpression): string {
        return `BSQAssembly::LiteralUnicodeCharExpression{ ${this.emitExpressionBase(exp)}, value=${exp.value} }`
    }

    private emitLiteralCStringExpression(exp: LiteralSimpleExpression): string {
        return `BSQAssembly::LiteralCStringExpression{ ${this.emitExpressionBase(exp)}, value=${exp.value} }`;
    }

    private emitLiteralStringExpression(exp: LiteralSimpleExpression): string {
        return `BSQAssembly::LiteralStringExpression{ ${this.emitExpressionBase(exp)}, value=${exp.value} }`;
    }
 
    private emitLiteralTypeDeclValueExpression(exp: LiteralTypeDeclValueExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const value = this.emitExpression(exp.value);
        const constype = this.emitTypeSignature(exp.constype);

        return `BSQAssembly::LiteralTypeDeclValueExpression{ ${ebase}, value=${value}, constype=${constype} }`;
    }

    private emitAccessNamespaceConstantExpression(exp: AccessNamespaceConstantExpression): string {
        const ebase = this.emitExpressionBase(exp);
        
        return `BSQAssembly::AccessNamespaceConstantExpression{ ${ebase}, ns='${exp.ns.emit()}'<BSQAssembly::NamespaceKey>, name='${exp.name}'<BSQAssembly::Identifier> }`;
    }
    
    private emitAccessStaticFieldExpression(exp: AccessStaticFieldExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const stype = this.emitTypeSignature(exp.stype);
        const name = exp.name;
        const resolvedDeclType = this.emitTypeSignature(this.tproc(exp.resolvedDeclType as TypeSignature));
        
        return `BSQAssembly::AccessStaticFieldExpression{ ${ebase}, stype=${stype}, name='${name}'<BSQAssembly::Identifier>, resolvedDeclType=${resolvedDeclType}}`;
    }
    
    private emitAccessEnumExpression(exp: AccessEnumExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const etype = this.emitTypeSignature(exp.stype);

        return `BSQAssembly::AccessEnumExpression{ ${ebase}, stype=${etype}, name='${exp.name}' }`;
    }

    private emitAccessVariableExpression(exp: AccessVariableExpression): string {
        const ebase = this.emitExpressionBase(exp);

        if(exp.specialaccess.length === 0) {
            if(!exp.isCaptured) {
                return `BSQAssembly::AccessVariableExpression{ ${ebase}, vname='${exp.srcname}'<BSQAssembly::VarIdentifier>, layouttype=${this.emitTypeSignature(exp.layouttype as TypeSignature)} }`;
            }
            else {
                return `BSQAssembly::AccessCapturedVariableExpression{ ${ebase}, vname='${exp.srcname}'<BSQAssembly::VarIdentifier>, layouttype=${this.emitTypeSignature(exp.layouttype as TypeSignature)} }`;
            }
        }
        else {
            let eexp: string;
            let ctype: TypeSignature;
            if(!exp.isCaptured) {
                eexp = `BSQAssembly::AccessVariableExpression{ ${ebase}, vname='${exp.srcname}'<BSQAssembly::VarIdentifier>, layouttype=${this.emitTypeSignature(exp.layouttype as TypeSignature)} }`;
                ctype = exp.layouttype as TypeSignature;
            }
            else {
                eexp = `BSQAssembly::AccessCapturedVariableExpression{ ${ebase}, vname='${exp.srcname}'<BSQAssembly::VarIdentifier>, layouttype=${this.emitTypeSignature(exp.layouttype as TypeSignature)} }`;
                ctype = exp.layouttype as TypeSignature;
            }

            for(let i = 0; i < exp.specialaccess.length; ++i) {
                const acc = exp.specialaccess[i];
                
                if(acc.specialaccess !== undefined) {
                    const dd = (ctype as NominalTypeSignature).decl;
                    if(dd instanceof OptionTypeDecl) {
                        const somedecl = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Some") as SomeTypeDecl
                        const sometype = new NominalTypeSignature(ctype.sinfo, undefined, somedecl, (ctype as NominalTypeSignature).alltermargs);
                        const oftype = (ctype as NominalTypeSignature).alltermargs[0];

                        eexp = `BSQAssembly::CoerceNarrowTypeExpression{ sinfo=${this.emitSourceInfo(exp.sinfo)}, etype=${this.emitTypeSignature(sometype)}, exp=${eexp}, srctype=${this.emitTypeSignature(ctype)}, trgttype=${this.emitTypeSignature(sometype)} }`;
                        eexp = `BSQAssembly::PostfixOp{ sinfo=${this.emitSourceInfo(exp.sinfo)}, etype=${this.emitTypeSignature(oftype)}, rootExp=${eexp}, ops=List<BSQAssembly::PostfixOperation>{ BSQAssembly::PostfixAccessSomeValue{ sinfo=${this.emitSourceInfo(exp.sinfo)}, baseType=${this.emitTypeSignature(sometype)} } } }`;
                    }
                    else {
                        if(acc.specialaccess === "value") {
                            assert(false, "NOT IMPLEMENTED -- AccessVariableExpression OkTypeDecl");
                        }
                        else {
                            assert(false, "NOT IMPLEMENTED -- AccessVariableExpression FailTypeDecl");
                        }
                    }
                }
                else {
                    eexp = `BSQAssembly::CoerceNarrowTypeExpression{ sinfo=${this.emitSourceInfo(exp.sinfo)}, etype=${this.emitTypeSignature(acc.ttype)}, exp=${eexp}, srctype=${this.emitTypeSignature(ctype)}, trgttype=${this.emitTypeSignature(acc.ttype)} }`;
                }

                ctype = acc.ttype;
            }

            return eexp;
        }
    }

    private emitConstructorExpressionBase(exp: ConstructorExpression): string {
        const ebase = this.emitExpressionBase(exp);
        return `${ebase}, args=${this.emitArgumentList(exp.args)}`;
    }

    private emitConstructorPrimaryExpressionBase(exp: ConstructorPrimaryExpression): string {
        const cebase = this.emitConstructorExpressionBase(exp);
        const ctype = this.emitTypeSignature(exp.ctype);

        return `${cebase}, ctype=${ctype}`;
    }

    private emitCollectionConstructor(cdecl: AbstractCollectionTypeDecl, exp: ConstructorPrimaryExpression): string {
        if(cdecl instanceof ListTypeDecl) {
            const cpee = this.emitConstructorPrimaryExpressionBase(exp);
            const elemtype = this.emitTypeSignature(exp.elemtype as TypeSignature);
            return `BSQAssembly::ConstructorPrimaryListExpression{ ${cpee}, elemtype=${elemtype} }`;
        }
        else {
            assert(false, "Not implemented -- CollectionConstructor of Map");
        }
    }

    private emitSpecialConstructableConstructor(exp: ConstructorPrimaryExpression): string {
        assert(false, "Not implemented -- SpecialConstructableConstructor");
    }

    private emitTypeDeclConstructor(cdecl: TypedeclTypeDecl, exp: ConstructorPrimaryExpression): string {
        const cpee = this.emitConstructorPrimaryExpressionBase(exp);

        if(cdecl.valuetype.tkeystr !== "CString" && cdecl.valuetype.tkeystr !== "String") {
            return `BSQAssembly::ConstructorTypeDeclExpression{ ${cpee} }`;
            
        }
        else {
            //TODO: we need to figure out how to encode regex expressions in general and Literals in particular
            assert(false, "Not implemented -- TypeDeclConstructor");
        }
    }

    private emitConstructorStdExpression(cdecl: EntityTypeDecl, exp: ConstructorPrimaryExpression): string {
        const cpee = this.emitConstructorPrimaryExpressionBase(exp);

        const shuffleinfo = exp.shuffleinfo.map((si) => {
            const iidx = si[0] !== -1 ? `some(${si[0]}n)` : "none";
            return `(|${iidx}, '${si[1]}'<BSQAssembly::Identifier>, ${this.emitTypeSignature(si[2])}|)`;
        });

         // ConstructorStdExpression provides Expression (not AbstractDecl), so we need to emit fullns explicitly
        let cstrns = exp.ctype.tkeystr.split('::').map(e => `'${e}'`);
        
        // Last element is entity name, we cannot properly look this up as fullns is for resolving namespaces
        if(cstrns.length >= 1) {
            cstrns.pop();
        }
        const fmt_cstrns = `fullns = List<CString>{${cstrns.join(', ')}}`;
        return `BSQAssembly::ConstructorStdExpression{ ${cpee}, shuffleinfo=List<(|Option<Nat>, BSQAssembly::Identifier, BSQAssembly::TypeSignature|)>{${shuffleinfo}}, ${fmt_cstrns} }`;
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

        return `BSQAssembly::ConstructorEListExpression{ ${cebase} }`;
    }

    private emitConstructorLambdaExpression(exp: ConstructorLambdaExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const bdecl = this.emitBodyImplementation(exp.invoke.body, new BsqonCodeFormatter(undefined));

        return `BSQAssembly::ConstructorLambdaExpression{ ${ebase}, body=${bdecl} }`;
    }

    private emitLetExpression(exp: LetExpression): string {
        assert(false, "Not implemented -- Let");
    }

    private emitLambdaInvokeExpression(exp: LambdaInvokeExpression): string {
        const ebase = this.emitExpressionBase(exp);

        const lambda = exp.lambda as LambdaTypeSignature;
        const shuffle = lambda.params.map((lp, ii) => [ii, lp.type] as [number, TypeSignature]);
        const argsinfo = this.emitInvokeArgumentInfo(exp.name, lambda.recursive, exp.args, shuffle, exp.resttype, exp.restinfo);

        return `BSQAssembly::LambdaInvokeExpression{ ${ebase}, isCapturedLambda=${exp.isCapturedLambda}, lambda=${this.emitTypeSignature(exp.lambda as TypeSignature)}, fname='${exp.name}'<BSQAssembly::Identifier>, argsinfo=${argsinfo} }`;
    }

    private emitSpecialConstructorExpression(exp: SpecialConstructorExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const cbase = `ctype=${this.emitTypeSignature(exp.constype as TypeSignature)}, args=${this.emitArgumentList(new ArgumentList([new PositionalArgumentValue(exp.arg)]))}`;
        const targs = (exp.constype as NominalTypeSignature).alltermargs;

        if(exp.rop === "some") {
            return `BSQAssembly::ConstructorPrimarySpecialSomeExpression{ ${ebase}, ${cbase}, ofttype=${this.emitTypeSignature(targs[0])}}`;
        }
        else if (exp.rop === "ok") {
            return `BSQAssembly::ConstructorPrimarySpecialOkExpression{ ${ebase}, ${cbase} ofttype=${this.emitTypeSignature(targs[0])}, ofetype=${this.emitTypeSignature(targs[1])} }`;
        }
        else {
            return `BSQAssembly::ConstructorPrimarySpecialFailExpression{ ${ebase}, ${cbase}, ofttype=${this.emitTypeSignature(targs[0])}, ofetype=${this.emitTypeSignature(targs[1])} }`;
        }
    }

    private emitCallNamespaceFunctionExpression(exp: CallNamespaceFunctionExpression): string {        
        const ebase = this.emitExpressionBase(exp);

        const cns = EmitNameManager.resolveNamespaceDecl(this.assembly, exp.ns);
        const ffinv = cns.functions.find((f) => f.name === exp.name) as NamespaceFunctionDecl;

        const nskey = EmitNameManager.generateNamespaceKey(exp.ns);
        const ikey = EmitNameManager.generateNamespaceInvokeKey(exp.ns, exp.name, exp.terms.map((t) => this.tproc(t)));

        const arginfo = this.emitInvokeArgumentInfo(exp.name, ffinv.recursive, exp.args, exp.shuffleinfo, exp.resttype, exp.restinfo);

        // CallNSExprs provide expression (not AbstractDecl), so we need to emit fullns explicitly
        const cstrns = exp.ns.ns.map(e => `'${e}'`).join(", ");
        const fmt_cstrns = `fullns = List<CString>{${cstrns}}`;


        return `BSQAssembly::CallNamespaceFunctionExpression{ ${ebase}, ikey='${ikey}'<BSQAssembly::InvokeKey>, ns='${nskey}'<BSQAssembly::NamespaceKey>, ${fmt_cstrns}, argsinfo=${arginfo} }`;
    }
   
    private emitCallTypeFunctionExpression(exp: CallTypeFunctionExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const ikey = EmitNameManager.generateTypeInvokeKey(exp.ttype, exp.name, exp.terms);
        const ttype = this.emitTypeSignature(exp.ttype);
        const resolvedDeclType = this.emitTypeSignature((this.tproc(exp.resolvedDeclType as TypeSignature)) as NominalTypeSignature);
       
        if(exp.isSpecialCall) {
            assert(false, "Not implemented -- CallTypeFunction Special");
        }
        else {
            const argsinfo = this.emitInvokeArgumentInfo(exp.name, exp.rec, exp.args, exp.shuffleinfo, exp.resttype, exp.restinfo); 
            return `BSQAssembly::CallTypeFunctionExpression{ ${ebase}, ikey='${ikey}'<BSQAssembly::InvokeKey>, ttype=${ttype}, resolvedDeclType=${resolvedDeclType}, argsinfo=${argsinfo}}`;
        }
    }

    private emitLogicActionAndExpression(exp: LogicActionAndExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const args = exp.args.map((arg) => this.emitExpression(arg)).join(", ");

        return `BSQAssembly::LogicActionAndExpression{ ${ebase}, args = List<BSQAssembly::Expression>{${args}} }`
    }
    
    private emitLogicActionOrExpression(exp: LogicActionOrExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const args = exp.args.map((arg) => this.emitExpression(arg)).join(", ");

        return `BSQAssembly::LogicActionOrExpression{ ${ebase}, args = List<BSQAssembly::Expression>{${args}} }`
    }
    
    private emitParseAsTypeExpression(exp: ParseAsTypeExpression): string {
        assert(false, "Not implemented -- ParseAsType");
    }

    private emitSafeConvertExpression(exp: SafeConvertExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const expr = this.emitExpression(exp.exp);
        const srctype = this.emitTypeSignature(exp.srctype);
        const trgttype = this.emitTypeSignature(exp.trgttype);

        return `BSQAssembly::SafeConvertExpression{ ${ebase}, exp=${expr}, srctype=${srctype}, trgttype=${trgttype}}`;
    }

    private emitCreateDirectExpression(exp: CreateDirectExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const expr = this.emitExpression(exp.exp);
        const srctype = this.emitTypeSignature(exp.srctype as NominalTypeSignature);
        const trgttype = this.emitTypeSignature(exp.trgttype as NominalTypeSignature);

        return `BSQAssembly::CreateDirectExpression{ ${ebase}, exp=${expr}, srctype=${srctype}, trgttype=${trgttype} }`
    }

    private emitPostfixOperationBase(exp: PostfixOperation): string {
        return `sinfo=${this.emitSourceInfo(exp.sinfo)}, baseType=${this.emitTypeSignature(exp.getRcvrType())}`;
    }

    private emitPostfixAccessFromName(exp: PostfixAccessFromName): string {
        const opbase = this.emitPostfixOperationBase(exp);
        const declaredInType = this.emitTypeSignature(exp.declaredInType as TypeSignature);
        const ftype = this.emitTypeSignature((exp.fieldDecl as MemberFieldDecl).declaredType);

        return `BSQAssembly::PostfixAccessFromName{ ${opbase}, declaredInType=${declaredInType}, name='${exp.name}'<BSQAssembly::Identifier>, ftype=${ftype} }`;
    }

    private emitPostfixProjectFromNames(exp: PostfixProjectFromNames): string {
        assert(false, "Not Implemented -- emitPostfixProjectFromNames");
    }

    private emitPostfixAccessFromIndex(exp: PostfixAccessFromIndex): string {
        const opbase = this.emitPostfixOperationBase(exp);

        return `BSQAssembly::PostfixAccessFromIndex{ ${opbase}, idx='${exp.idx}' }`;
    }

    private emitPostfixIsTest(exp: PostfixIsTest): string {
        const opbase = this.emitPostfixOperationBase(exp);
        const ttest = this.emitITest(exp.ttest);

        return `BSQAssembly::PostfixIsTest{ ${opbase}, ttest=${ttest} }`;
    }

    private emitPostfixAsConvert(exp: PostfixAsConvert): string {
        const opbase = this.emitPostfixOperationBase(exp);
        const ttype = this.emitITest(exp.ttest);

        return `BSQAssembly::PostfixAsConvert{ ${opbase}, ttest=${ttype} }`;
    }

    private emitPostfixAssignFields(exp: PostfixAssignFields): string {
        assert(false, "Not Implemented -- emitPostfixAssignFields");
    }

    private emitResolvedPostfixInvoke(exp: PostfixInvoke): string {
        const opbase = this.emitPostfixOperationBase(exp);

        const rtrgt = (this.tproc(exp.resolvedTrgt as TypeSignature) as NominalTypeSignature);
        const rdecl = exp.resolvedMethod as MethodDecl;

        const tsig = this.emitTypeSignature(rtrgt);
        const ikey = EmitNameManager.generateTypeInvokeKey(rtrgt, exp.name, exp.terms.map((t) => this.tproc(t)));

        const arginfo = this.emitInvokeArgumentInfo(exp.name, rdecl.recursive, exp.args, exp.shuffleinfo, exp.resttype, exp.restinfo);

        return `BSQAssembly::PostfixInvokeStatic{ ${opbase},  resolvedType=${tsig}, resolvedTrgt='${ikey}'<BSQAssembly::InvokeKey>, argsinfo=${arginfo} }`;
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

        const ebase = this.emitExpressionBase(exp); 
        return `BSQAssembly::PostfixOp{ ${ebase}, rootExp=${rootExp}, ops=List<BSQAssembly::PostfixOperation>{${ops}} }`;
    }

    private emitPrefixNotOpExpression(exp: PrefixNotOpExpression): string {
        const ebase = this.emitExpressionBase(exp);
        return `BSQAssembly::PrefixNotOpExpression{ ${ebase}, exp=${this.emitExpression(exp.exp)}, opertype=${this.emitTypeSignature(exp.opertype as TypeSignature)} }`;
    }

    private emitPrefixNegateOrPlusOpExpression(exp: PrefixNegateOrPlusOpExpression): string {
        const ebase = this.emitExpressionBase(exp);

        if(exp.op === "+") {
            return `BSQAssembly::PrefixPlusOpExpression{ ${ebase}, exp=${this.emitExpression(exp.exp)}, opertype=${this.emitTypeSignature(exp.opertype as TypeSignature)} }`;
        }
        else {
            return `BSQAssembly::PrefixNegateOpExpression{ ${ebase}, exp=${this.emitExpression(exp.exp)}, opertype=${this.emitTypeSignature(exp.opertype as TypeSignature)} }`;
        }
    }

    private emitBinAddExpression(exp: BinAddExpression): string {
        const ebase = this.emitExpressionBase(exp);
        return `BSQAssembly::BinAddExpression{ ${ebase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)}, opertype=${this.emitTypeSignature(exp.opertype as TypeSignature)} }`;
    }

    private emitBinSubExpression(exp: BinSubExpression,): string {
        const ebase = this.emitExpressionBase(exp);
        return `BSQAssembly::BinSubExpression{ ${ebase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)}, opertype=${this.emitTypeSignature(exp.opertype as TypeSignature)} }`;
    }
    
    private emitBinMultExpression(exp: BinMultExpression): string {
        const ebase = this.emitExpressionBase(exp);
        return `BSQAssembly::BinMultExpression{ ${ebase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)}, opertype=${this.emitTypeSignature(exp.opertype as TypeSignature)} }`;
    }
    
    private emitBinDivExpression(exp: BinDivExpression): string {
        const ebase = this.emitExpressionBase(exp);
        return `BSQAssembly::BinDivExpression{ ${ebase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)}, opertype=${this.emitTypeSignature(exp.opertype as TypeSignature)} }`;
    }
    
    private emitBinKeyEqExpression(exp: BinKeyEqExpression): string {
        const kcop = exp.operkind;

        const ebase = this.emitExpressionBase(exp);
        const bkbase = `${ebase}, opertype=${this.emitTypeSignature(exp.opertype as TypeSignature)}`;

        if(kcop === "lhsnone") {
            return `BSQAssembly::BinKeyEqNoneExpression{ ${bkbase}, exp=${this.emitExpression(exp.rhs)} }`;
        }
        else if(kcop === "rhsnone") {
            return `BSQAssembly::BinKeyEqNoneExpression{ ${bkbase}, exp=${this.emitExpression(exp.lhs)} }`;
        }
        else if(kcop === "lhskeyeqoption") {
            return `BSQAssembly::BinKeySomeEqExpression{ ${bkbase}, eqoption=${this.emitExpression(exp.rhs)}, eqval=${this.emitExpression(exp.lhs)} }`;
        }
        else if(kcop === "rhskeyeqoption") {
            return `BSQAssembly::BinKeySomeEqExpression{ ${bkbase}, eqoption=${this.emitExpression(exp.lhs)}, eqval=${this.emitExpression(exp.rhs)} }`;
        }
        else if(kcop === "stricteq") {
            return `BSQAssembly::BinKeyEqExpression{ ${bkbase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
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
            return `BSQAssembly::BinKeyNotEqNoneExpression{ ${bkbase}, exp=${this.emitExpression(exp.rhs)} }`;
        }
        else if(kcop === "rhsnone") {
            return `BSQAssembly::BinKeyNotEqNoneExpression{ ${bkbase}, exp=${this.emitExpression(exp.lhs)} }`;
        }
        else if(kcop === "lhskeyeqoption") {
            return `BSQAssembly::BinKeyNotSomeEqExpression{ ${bkbase}, eqoption=${this.emitExpression(exp.rhs)}, eqval=${this.emitExpression(exp.lhs)} }`;
        }
        else if(kcop === "rhskeyeqoption") {
            return `BSQAssembly::BinKeyNotSomeEqExpression{ ${bkbase}, eqoption=${this.emitExpression(exp.lhs)}, eqval=${this.emitExpression(exp.rhs)} }`;
        }
        else if(kcop === "stricteq") {
            return `BSQAssembly::BinKeyNotEqExpression{ ${bkbase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
        }
        else {
            assert(false, "Unknown key eq kind");
        }
    }

    private emitKeyCompareEqExpression(exp: KeyCompareEqExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const ktype = this.emitTypeSignature(exp.ktype as TypeSignature);
        const optype = this.emitTypeSignature(exp.optype as TypeSignature);

        return `BSQAssembly::KeyCmpEqualExpression{ ${ebase}, ktype=${ktype}, optype=${optype}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }

    private emitKeyCompareLessExpression(exp: KeyCompareLessExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const ktype = this.emitTypeSignature(exp.ktype as TypeSignature);
        const optype = this.emitTypeSignature(exp.optype as TypeSignature);

        return `BSQAssembly::KeyCmpEqualExpression{ ${ebase}, ktype=${ktype}, optype=${optype}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }

    private emitNumericEqExpression(exp: NumericEqExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const optype = this.emitTypeSignature(exp.opertype as TypeSignature);

        return `BSQAssembly::NumericEqExpression{ ${ebase}, opertype=${optype}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }

    private emitNumericNeqExpression(exp: NumericNeqExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const optype = this.emitTypeSignature(exp.opertype as TypeSignature);

        return `BSQAssembly::NumericNeqExpression{ ${ebase}, opertype=${optype}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }
    
    private emitNumericLessExpression(exp: NumericLessExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const optype = this.emitTypeSignature(exp.opertype as TypeSignature);

        return `BSQAssembly::NumericLessExpression{ ${ebase}, opertype=${optype}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }
    
    private emitNumericLessEqExpression(exp: NumericLessEqExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const optype = this.emitTypeSignature(exp.opertype as TypeSignature);

        return `BSQAssembly::NumericLessEqExpression{ ${ebase}, opertype=${optype}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }
    
    private emitNumericGreaterExpression(exp: NumericGreaterExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const optype = this.emitTypeSignature(exp.opertype as TypeSignature);

        return `BSQAssembly::NumericGreaterExpression{ ${ebase}, opertype=${optype}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }

    private emitNumericGreaterEqExpression(exp: NumericGreaterEqExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const optype = this.emitTypeSignature(exp.opertype as TypeSignature);

        return `BSQAssembly::NumericGreaterEqExpression{ ${ebase}, opertype=${optype}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }

    private emitBinLogicAndExpression(exp: BinLogicAndExpression): string {
        const ebase = this.emitExpressionBase(exp);
        return `BSQAssembly::BinLogicAndExpression{ ${ebase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }

    private emitBinLogicOrExpression(exp: BinLogicOrExpression): string {
        const ebase = this.emitExpressionBase(exp);
        return `BSQAssembly::BinLogicOrExpression{ ${ebase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }

    private emitBinLogicImpliesExpression(exp: BinLogicImpliesExpression): string {
        const ebase = this.emitExpressionBase(exp);
        return `BSQAssembly::BinLogicImpliesExpression{ ${ebase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }

    private emitBinLogicIFFExpression(exp: BinLogicIFFExpression): string {
        const ebase = this.emitExpressionBase(exp);
        return `BSQAssembly::BinLogicIFFExpression{ ${ebase}, lhs=${this.emitExpression(exp.lhs)}, rhs=${this.emitExpression(exp.rhs)} }`;
    }
    
    private emitMapEntryConstructorExpression(exp: MapEntryConstructorExpression): string {
        assert(false, "Not implemented -- MapEntryConstructor");
    }

    private emitIfExpression(exp: IfExpression): string {
        const ebase = this.emitExpressionBase(exp);
        const texp = this.emitExpression(exp.test.exp);
        const thenexp = this.emitExpression(exp.trueValue);
        const elseexp = this.emitExpression(exp.falseValue);

        const ifbase = `${ebase}, texp=${texp}, thenexp=${thenexp}, elseexp=${elseexp}`;

        if(exp.test.itestopt === undefined) {
            return `BSQAssembly::IfSimpleExpression{ ${ifbase} }`;
        }
        else {
            let itest = this.emitITest(exp.test.itestopt);
            if(exp.binder === undefined) {
                return `BSQAssembly::IfTestExpression{ ${ifbase}, itest=${itest} }`;
            }
            else {
                const binder = this.emitBinderInfo(exp.binder);
                return `BSQAssembly::IfBinderExpression{ ${ifbase}, itest=${itest}, binder=${binder} }`;
            }
        }
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
            case ExpressionTag.LiteralCCharExpression: {
                return this.emitLiteralCCharExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUnicodeCharExpression: {
                return this.emitLiteralUnicodeCharExpression(exp as LiteralSimpleExpression);
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

    private emitStatementBase(stmt: Statement): string {
        return `sinfo=${this.emitSourceInfo(stmt.sinfo)}`;
    }

    private emitEmptyStatement(stmt: EmptyStatement): string {
        assert(false, "Should skip empty statement on emit");
    }
    
    private emitVariableDeclarationStatement(stmt: VariableDeclarationStatement): string {
        const sbase = this.emitStatementBase(stmt);
        const vtype = this.emitTypeSignature(stmt.vtype);

        return `BSQAssembly::VariableDeclarationStatement{ ${sbase}, name='${stmt.name}'<BSQAssembly::Identifier>, vtype=${vtype} }`;
    }
    
    private emitVariableMultiDeclarationStatement(stmt: VariableMultiDeclarationStatement): string {
        assert(false, "Not Implemented -- emitVariableMultiDeclarationStatement");
    }
    
    private emitVariableInitializationStatement(stmt: VariableInitializationStatement): string {
        const sbase = this.emitStatementBase(stmt);
        const vtype = this.emitTypeSignature(stmt.actualtype as TypeSignature);
        const rhsexp = this.emitExpressionRHS(stmt.exp);
        
        return `BSQAssembly::VariableInitializationStatement{ ${sbase}, name='${stmt.name}'<BSQAssembly::Identifier>, vtype=${vtype}, exp=${rhsexp} }`;
    }
    
    private emitVariableMultiInitializationStatement(stmt: VariableMultiInitializationStatement): string {
        assert(false, "Not Implemented -- emitVariableMultiInitializationStatement");
    }

    private emitVariableAssignmentStatement(stmt: VariableAssignmentStatement): string {
        const sbase = this.emitStatementBase(stmt);
        const vtype = this.emitTypeSignature(stmt.vtype as TypeSignature);
        const rhsexp = this.emitExpressionRHS(stmt.exp);

        return `BSQAssembly::VariableAssignmentStatement{ ${sbase}, name='${stmt.name}'<BSQAssembly::Identifier>, vtype=${vtype}, exp=${rhsexp} }`;
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
        const sbase = this.emitStatementBase(stmt);
        const rtype = this.emitTypeSignature(stmt.rtype as TypeSignature);
        const rexp = this.emitExpressionRHS(stmt.value);

        return `BSQAssembly::ReturnSingleStatement{ ${sbase}, rtype=${rtype}, value=${rexp} }`;
    }

    private emitReturnMultiStatement(stmt: ReturnMultiStatement): string {
        assert(false, "Not Implemented -- emitReturnMultiStatement");
    }

    private emitIfStatement(stmt: IfStatement, fmt: BsqonCodeFormatter): string {
        const sbase = this.emitStatementBase(stmt);

        const cond = this.emitExpression(stmt.cond.exp);
        const tblock = this.emitBlockStatement(stmt.trueBlock, fmt);

        const ibase = `${sbase}, texp=${cond}, trueBlock=${tblock}`;

        if(stmt.cond.itestopt === undefined) {
            return `BSQAssembly::IfSimpleStatement{ ${ibase} }`;
        }
        else {
            if(stmt.binder === undefined) {
                return `BSQAssembly::IfTestStatement{ ${ibase}, itest=${this.emitITest(stmt.cond.itestopt)} }`;
            }
            else {
                const binder = this.emitBinderInfo(stmt.binder);
                return `BSQAssembly::IfBinderStatement{ ${ibase}, itest=${this.emitITest(stmt.cond.itestopt)}, binder=${binder} }`;
            }
        }
    }

    private emitIfElseStatement(stmt: IfElseStatement, fmt: BsqonCodeFormatter): string {
        const sbase = this.emitStatementBase(stmt);

        const cond = this.emitExpression(stmt.cond.exp);
        const tblock = this.emitBlockStatement(stmt.trueBlock, fmt);
        const fblock = this.emitBlockStatement(stmt.falseBlock, fmt);

        const ibase = `${sbase}, texp=${cond}, trueBlock=${tblock}, falseBlock=${fblock}`;

        if(stmt.cond.itestopt === undefined) {
            return `BSQAssembly::IfElseSimpleStatement{ ${ibase} }`;
        }
        else {
            if(stmt.binder === undefined) {
                return `BSQAssembly::IfElseTestStatement{ ${ibase}, itest=${this.emitITest(stmt.cond.itestopt)} }`;
            }
            else {
                const binder = this.emitBinderInfo(stmt.binder);
                return `BSQAssembly::IfElseBinderStatement{ ${ibase}, itest=${this.emitITest(stmt.cond.itestopt)}, binder=${binder} }`;
            }
        }
    }

    private emitIfElifElseStatement(stmt: IfElifElseStatement, fmt: BsqonCodeFormatter): string {  
        const sbase = this.emitStatementBase(stmt);
        let firstcond = stmt.condflow[0];
        let ifcond: string = this.emitExpression(firstcond.cond);
        let ifflow: string = this.emitBlockStatement(firstcond.block, fmt);

        const condflow = stmt.condflow.slice(1).map((elif) => {
            const cond = this.emitExpression(elif.cond);
            const block = this.emitBlockStatement(elif.block, fmt);

            return `(|${cond}, ${block}|)`;  
        }).join(", ");
        const elseflow = this.emitBlockStatement(stmt.elseflow, fmt);
        
        return [`BSQAssembly::IfElifElseStatement{ ${sbase}, ifcond = ${ifcond}, ifflow = ${ifflow}, elseflow=${elseflow}, `, fmt.nl(), `condflow = List<(|BSQAssembly::Expression, BSQAssembly::BlockStatement|)>{ ${condflow} }}`].join("");
    }

    private emitSwitchStatement(stmt: SwitchStatement, fmt: BsqonCodeFormatter): string {
        const sbase = this.emitStatementBase(stmt);
        const sval = this.emitExpression(stmt.sval);
        const switchflow = stmt.switchflow.slice(1).map((e) => {
            const cond = e.lval !== undefined ? `some(${this.emitExpression(e.lval.exp)})` : "none";
            const body = this.emitBlockStatement(e.value, fmt);
            return `(|${cond}, ${body}|)`;
        }).join(", ");
        const mustExhaustive = stmt.mustExhaustive;
        const optypes = stmt.optypes.map((op) => this.emitTypeSignature(op)).join(", ");

        return [`BSQAssembly::SwitchStatement{${sbase}, sval=${sval},`, fmt.nl()+fmt.indent(""),`switchflow=List<(|Option<BSQAssembly::Expression>, BSQAssembly::BlockStatement|)>{${switchflow}},`, fmt.nl()+fmt.indent(""), `mustExhaustive=${mustExhaustive},`, fmt.nl()+fmt.indent(""), `optypes=List<BSQAssembly::TypeSignature>{${optypes}}}`].join("");
    }

    private emitMatchStatement(stmt: MatchStatement, fmt: BsqonCodeFormatter): string {
        const sbase = this.emitStatementBase(stmt);
        const sval = this.emitExpression(stmt.sval[0]);
        const bindInfo = (stmt.sval[1] != undefined) ? `some(${this.emitBinderInfo(stmt.sval[1])})` : "none";
        const matchflow = stmt.matchflow.slice(1).map((e) => {
            const cond = e.mtype !== undefined ? `some(${this.emitTypeSignature(e.mtype)})` : "none";
            const body = this.emitBlockStatement(e.value, fmt);
            return `(|${cond}, ${body}|)`;
        }).join(", ");
        const mustExhaustive = stmt.mustExhaustive;

        const finalop = stmt.matchflow[stmt.matchflow.length-1];
        const implicitfinalop = stmt.implicitFinalType !== undefined ? stmt.implicitFinalType : finalop.mtype;
        const implicitFinalType = (implicitfinalop !== undefined) ? this.emitTypeSignature(implicitfinalop) : assert(false, "No final type signature found in match statement");

        return [`BSQAssembly::MatchStatement{${sbase}, sval=${sval}, bindInfo=${bindInfo},`, fmt.nl()+fmt.indent(""), `matchflow=List<(|Option<BSQAssembly::TypeSignature>, BSQAssembly::BlockStatement|)>{${matchflow}},`, fmt.nl()+fmt.indent(""), `mustExhaustive=${mustExhaustive}, implicitFinalType=${implicitFinalType}}`].join("");
    }

    private emitAbortStatement(stmt: AbortStatement): string {
        const sbase = this.emitStatementBase(stmt);
        return `BSQAssembly::AbortStatement{ ${sbase} }`;
    }

    private emitAssertStatement(stmt: AssertStatement): string {
        const sbase = this.emitStatementBase(stmt);
        const cond = this.emitExpression(stmt.cond);

        return `BSQAssembly::AssertStatement{ ${sbase}, cond=${cond} }`;
    }

    private emitValidateStatement(stmt: ValidateStatement): string {
        const sbase = this.emitStatementBase(stmt);
        const cond = this.emitExpression(stmt.cond);
        const dtag = stmt.diagnosticTag !== undefined ? `some('${stmt.diagnosticTag}')` : "none";

        return `BSQAssembly::ValidateStatement{ ${sbase}, cond=${cond}, diagnosticTag=${dtag} }`;
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
            const sstr = this.emitStatement(stmti, fmt);

            stmtstrs.push(sstr);
        }
        fmt.indentPop();

        return stmtstrs;
    }

    private emitBlockStatement(stmt: BlockStatement, fmt: BsqonCodeFormatter): string {
        const sbase = this.emitStatementBase(stmt);
        const stmts = this.emitStatementArray(stmt.statements.filter((stmt) => !((stmt instanceof EmptyStatement) || (stmt instanceof DebugStatement))), fmt).join(`, `);
        return ["BSQAssembly::BlockStatement{", sbase, `,isScoping=${stmt.isScoping},`, fmt.nl()+fmt.indent(""),"statements=List<BSQAssembly::Statement>{", stmts, "}}"].join("");
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
            return "BSQAssembly::AbstractBodyImplementation { }";
        }
        else if(body instanceof PredicateUFBodyImplementation) {
            return "BSQAssembly::PredicateUFBodyImplementation { }";
        }
        else if(body instanceof BuiltinBodyImplementation) {
            let binds = this.mapper !== undefined ? this.mapper.computeBindingSet().map(ee => `(|'${ee[0]}', ${this.emitTypeSignature(ee[1])}|)`).join(", ") : ''
            return `BSQAssembly::BuiltinBodyImplementation { '${body.builtin}', List<(|CString, BSQAssembly::TypeSignature|)>{${binds}} }`;
        }
        else if(body instanceof SynthesisBodyImplementation) {
            return "BSQAssembly::SynthesisBodyImplementation { }";
        }
        else if(body instanceof ExpressionBodyImplementation) {
            return `BSQAssembly::ExpressionBodyImplementation { ${this.emitExpression(body.exp)} }`;
        }
        else if(body instanceof StandardBodyImplementation) {
            const stmts = this.emitStatementArray(body.statements, fmt);
            const bbody = fmt.formatListOf("List<BSQAssembly::Statement>{", stmts, "}");
            return `BSQAssembly::StandardBodyImplementation {${fmt.nl()}${bbody}}`;
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
        let fullns = nskey.split('::').map(e => `'${e}'`).join(", ");
        return `file="${decl.file}", sinfo=${this.emitSourceInfo(decl.sinfo)}, fullns = List<CString>{${fullns}}, declaredInNS='${nskey}'<BSQAssembly::NamespaceKey>`;
    }

    private emitConditionDeclBase(decl: ConditionDecl, nskey: string, label: string, exp: Expression): string {
        const dbase = this.emitAbstractDeclBase(decl, nskey);
        const dtag = decl.diagnosticTag !== undefined ? `some('${decl.diagnosticTag}')` : "none";

        return `${dbase}, diagnosticTag=${dtag}, ikey='${label}'<BSQAssembly::InvokeKey>, exp=${this.emitExpression(exp)}`;
    }


    private emitPreConditionDecl(decl: PreConditionDecl, nskey: string, ikey: string, ii: number): string {
        const cbase = this.emitConditionDeclBase(decl, nskey, ikey + "_$_precond" + ii.toString(), decl.exp);
        return `BSQAssembly::PreConditionDecl{ ${cbase}, issoft=${decl.issoft} }`;
    }

    private emitPostConditionDecl(decl: PostConditionDecl, nskey: string, ikey: string, ii: number): string {
        const cbase = this.emitConditionDeclBase(decl, nskey, ikey + "_$_postcond" + ii.toString(), decl.exp);
        return `BSQAssembly::PostConditionDecl{ ${cbase}, issoft=${decl.issoft} }`;
    }

    private emitInvariantDecl(decl: InvariantDecl, nskey: string, tkey: string, ii: number): string {
        const cbase = this.emitConditionDeclBase(decl, nskey, tkey + "_$_invariant" + ii.toString(), decl.exp.exp);
        return `BSQAssembly::InvariantDecl{ ${cbase} }`;
    }

    private emitValidateDecl(decl: ValidateDecl, nskey: string, tkey: string, ii: number): string {
        const cbase = this.emitConditionDeclBase(decl, nskey, tkey + "_$_validate" + ii.toString(), decl.exp.exp);
        return `BSQAssembly::ValidateDecl{ ${cbase} }`;
    }

    private emitDeclarationAttibuteBase(att: DeclarationAttibute, nskey: string): string {
        const tags = att.tags.map((t) => `(${this.emitTypeSignature(t.enumType)}, '${t.tag}')`);
        const text = att.text !== undefined ? `some('${att.text}')` : "none";

        return `BSQAssembly::DeclarationAttibute{name='${att.name}'<BSQAssembly::Identifier>, tags=List<(|BSQAssembly::TypeSignature, CString|)>{ ${tags.join(", ")} }, text=${text} }`;
    }

    private emitAbstractCoreDecl(decl: AbstractCoreDecl, nskey: string, fmt: BsqonCodeFormatter): string {
        const dbase = this.emitAbstractDeclBase(decl, nskey);
        const atts = decl.attributes.map((att) => this.emitDeclarationAttibuteBase(att, nskey));

        const nn = `name='${decl.name}'<BSQAssembly::Identifier>`;
        return `${dbase}, attributes=List<BSQAssembly::DeclarationAttibute>{ ${atts.join(", ")} },${fmt.nl() + fmt.indent(nn)}`;
    }

    private emitInvokeParameterDecl(pdecl: InvokeParameterDecl): string {
        const ptype = this.emitTypeSignature(pdecl.type);
        const defaultval = pdecl.optDefaultValue !== undefined ? `some(${this.emitExpression(pdecl.optDefaultValue.exp)})` : "none";

        return `BSQAssembly::InvokeParameterDecl{ pname='${pdecl.name}'<BSQAssembly::Identifier>, ptype=${ptype}, defaultval=${defaultval}, isRefParam=${pdecl.isRefParam}, isRestParam=${pdecl.isRestParam} }`;
    }

    private emitAbstractInvokeDecl(decl: AbstractInvokeDecl, nskey: string, ikey: string, fmt: BsqonCodeFormatter): string {
        const dbase = this.emitAbstractCoreDecl(decl, nskey, fmt);

        const ikeystr = `ikey='${ikey}'<BSQAssembly::InvokeKey>`;
        const isrecursive = `irecursive=${this.emitRecInfo(decl.recursive)}`;
        const params = `params=List<BSQAssembly::InvokeParameterDecl>{ ${decl.params.map((p) => this.emitInvokeParameterDecl(p))} }`;
        const resultType = `resultType=${this.emitTypeSignature(decl.resultType)}`;

        const body = this.emitBodyImplementation(decl.body, fmt);
        const bodystr = `body=${body}`;

        return `${dbase},${fmt.nl() + fmt.indent(ikeystr)}, ${isrecursive},${fmt.nl() + fmt.indent(params)},${fmt.nl() + fmt.indent(resultType)},${fmt.nl() + fmt.indent(bodystr)}`;
    }

    private emitExplicitInvokeDecl(decl: ExplicitInvokeDecl, nskey: string, ikey: string, fmt: BsqonCodeFormatter): string {
        const ibase = this.emitAbstractInvokeDecl(decl, nskey, ikey, fmt);

        const preconds = decl.preconditions.map((p, ii) => this.emitPreConditionDecl(p, nskey, ikey, ii)).join(", ");
        const postconds = decl.postconditions.map((p, ii) => this.emitPostConditionDecl(p, nskey, ikey, ii)).join(", ");

        const conds = `preconditions=List<BSQAssembly::PreConditionDecl>{ ${preconds} }, postconditions=List<BSQAssembly::PostConditionDecl>{ ${postconds} }`;
        return `${ibase},${fmt.nl() + fmt.indent(conds)}`;
    }

    private emitFKindTag(fkind: "function" | "predicate" | "errtest" | "chktest" | "example"): string {
        if(fkind === "function") {
            return "BSQAssembly::FunctionDeclKindTag#Function";
        }
        else if(fkind === "predicate") {
            return "BSQAssembly::FunctionDeclKindTag#Predicate";
        }
        else if(fkind === "errtest") {
            return "BSQAssembly::FunctionDeclKindTag#ErrorTest";
        }
        else if(fkind === "chktest") {
            return "BSQAssembly::FunctionDeclKindTag#CheckTest";
        }
        else {
            return "BSQAssembly::FunctionDeclKindTag#Example";
        }
    }

    private emitFunctionDecl(ns: FullyQualifiedNamespace, fdecl: FunctionInvokeDecl, optenclosingtype: [NominalTypeSignature, TemplateNameMapper | undefined] | undefined, optmapping: TemplateNameMapper | undefined, fmt: BsqonCodeFormatter) {
        const omap = this.mapper;
        if(optmapping !== undefined) {
            this.mapper = TemplateNameMapper.tryMerge(optenclosingtype !== undefined ? optenclosingtype[1] : undefined, optmapping);
        }
    
        const nskey = EmitNameManager.generateNamespaceKey(ns);

        if(optenclosingtype !== undefined) {
            const ikey =  EmitNameManager.generateTypeInvokeKey(optenclosingtype[0], fdecl.name, fdecl.terms.map((tt) => this.tproc(new TemplateTypeSignature(SourceInfo.implicitSourceInfo(), tt.name))));
            const ibase = this.emitExplicitInvokeDecl(fdecl, nskey, ikey, fmt);
            this.mapper = omap;

            const typeUpdatedNsKey = `${nskey}::${ikey.split("::").slice(0,-1).join("::")}`;
            const typeUpdatedIKey = `${nskey}::${ikey}`;
            let cstrns = typeUpdatedNsKey.split('::').map(e => `'${e}'`);

            this.typefuncs.push(`'${ikey}'<BSQAssembly::InvokeKey> => BSQAssembly::TypeFunctionDecl{ ${ibase}, completens=List<CString>{${cstrns}}, completeikey='${typeUpdatedIKey}'<BSQAssembly::InvokeKey>}`);
            this.allfuncs.push(`'${ikey}'<BSQAssembly::InvokeKey>`);        
        }
        else {
            const ftag = (fdecl as NamespaceFunctionDecl).fkind;
            if(ftag === "function" || ftag === "predicate" || this.testEmitEnabled(fdecl as NamespaceFunctionDecl)) {
                const ikey = EmitNameManager.generateNamespaceInvokeKey(ns, fdecl.name, fdecl.terms.map((tt) => this.tproc(new TemplateTypeSignature(SourceInfo.implicitSourceInfo(), tt.name))));

                fmt.indentPush();
                const ibase = this.emitExplicitInvokeDecl(fdecl, nskey, ikey, fmt);
                const fkind = fmt.indent(`fkind=${this.emitFKindTag((fdecl as NamespaceFunctionDecl).fkind)}`);

                this.mapper = omap;
                fmt.indentPop();
                
                if(ns.ns.length > 6) { 
                    assert(false, "Not Implemented -- Namespace nesting of depth > 6");
                }

                this.nsfuncs.push(`'${ikey}'<BSQAssembly::InvokeKey> => BSQAssembly::NamespaceFunctionDecl{ ${ibase}, ${fmt.nl()}${fkind}${fmt.nl() + fmt.indent("}")}`);
                this.allfuncs.push(`'${ikey}'<BSQAssembly::InvokeKey>`);
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

    private emitMethodDecl(ns: FullyQualifiedNamespace, optenclosingtype: [NominalTypeSignature, TemplateNameMapper | undefined], mdecl: MethodDecl, optmapping: TemplateNameMapper | undefined, fmt: BsqonCodeFormatter): string {
        const omap = this.mapper;
        if(optmapping !== undefined) {
            this.mapper = TemplateNameMapper.tryMerge(optenclosingtype[1], optmapping);
        }

        fmt.indentPush();
        let ret: string = "";

        const nskey = EmitNameManager.generateNamespaceKey(ns);
        const ikey = EmitNameManager.generateTypeInvokeKey(optenclosingtype[0], mdecl.name, mdecl.terms.map((tt) => this.tproc(new TemplateTypeSignature(SourceInfo.implicitSourceInfo(), tt.name))));

        const ibase = this.emitExplicitInvokeDecl(mdecl, nskey, ikey, fmt);
        const isThisRef = fmt.indent(`isThisRef=${mdecl.isThisRef}`);
        const oftype = fmt.indent(`ofrcvrtype=${this.emitTypeSignature(optenclosingtype[0])}`);
        fmt.indentPop();

        const isstatic = mdecl.attributes.every((att) => att.name !== "abstract" && att.name !== "virtual" && att.name !== "override");
        if(isstatic) {
            ret = `'${ikey}'<BSQAssembly::InvokeKey>`;
            this.allmethods.push(ret); 
            this.staticmethods.push(`'${ikey}'<BSQAssembly::InvokeKey> => BSQAssembly::MethodDeclStatic{ ${ibase},${fmt.nl()}${isThisRef},${fmt.nl()}${oftype}${fmt.nl() + fmt.indent("}")}`);
        }
        else {
            assert(false, "Not Implemented -- Abstract, Virtual, and Override methods");
        }
        this.mapper = omap;

        return ret;
    }

    private emitMethodDecls(ns: FullyQualifiedNamespace, optenclosingtype: [NominalTypeSignature, TemplateNameMapper | undefined], mdecls: [MethodDecl, MethodInstantiationInfo | undefined][], fmt: BsqonCodeFormatter): [string[], string[], string[], string[]] {
        let decls: string[] = [];

        for(let i = 0; i < mdecls.length; ++i) {
            const mdecl = mdecls[i][0];
            const mii = mdecls[i][1];

            if(mii !== undefined) {
                if(mii.binds === undefined) {
                    const bsqondecl = this.emitMethodDecl(ns, optenclosingtype, mdecl, undefined, fmt);
                    decls.push(bsqondecl);
                }
                else {
                    for(let j = 0; j < mii.binds.length; ++j) {
                        const bsqondecl = this.emitMethodDecl(ns, optenclosingtype, mdecl, mii.binds[j], fmt);
                        decls.push(bsqondecl);
                    }
                }
            }
        }

        //
        //TODO: need to split these up based on the kind of method (abstract, virtual, override, static)
        //

        return [[], [], [], decls];
    }

    private emitConstMemberDecls(ns: FullyQualifiedNamespace, declInType: NominalTypeSignature, decls: ConstMemberDecl[]) {
        for(let i = 0; i < decls.length; ++i) {
            const dd = decls[i];

            const dbase = this.emitAbstractCoreDecl(dd, EmitNameManager.generateNamespaceKey(ns), new BsqonCodeFormatter(undefined));
            const intype = this.emitTypeSignature(declInType);
            const dtype = this.emitTypeSignature(dd.declaredType);
            const value = this.emitExpression(dd.value.exp);

            this.typeconsts.push(`BSQAssembly::ConstMemberDecl{ ${dbase}, declaredInType=${intype}, declaredType=${dtype}, value=${value} }`);
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
        const dbase = this.emitAbstractCoreDecl(fdecl, EmitNameManager.generateNamespaceKey(ns), new BsqonCodeFormatter(undefined));

        const declin = this.emitTypeSignature(enclosingtype);
        const decltype = this.emitTypeSignature(fdecl.declaredType);
        const defaultValue = fdecl.defaultValue !== undefined ? `some(${this.emitExpression(fdecl.defaultValue.exp)})` : "none";

        return `BSQAssembly::MemberFieldDecl{ ${dbase}, declaredInType=${declin}, declaredType=${decltype}, defaultValue=${defaultValue}, isSpecialAccess=${fdecl.isSpecialAccess} }`;
    }

    private emitSaturatedFieldInfo(sfield: {name: string, type: TypeSignature, hasdefault: boolean, containingtype: NominalTypeSignature}): string {
        return `BSQAssembly::SaturatedFieldInfo{ declaredInType=${this.emitTypeSignature(sfield.containingtype)}, fname='${sfield.name}'<Identifier>, ftype=${this.emitTypeSignature(sfield.type)}, hasdefault=${sfield.hasdefault} }`;
    }
    
    private emitSaturatedInvariantInfo(invariants: {containingtype: NominalTypeSignature, ii: number, file: string, sinfo: SourceInfo, tag: string | undefined}): string {
        const ikey = EmitNameManager.generateTypeKey(invariants.containingtype) + "_$_invariant" + invariants.ii.toString()
        return `BSQAssembly::SaturatedInvariantInfo{ ikey='${ikey}'<BSQAssembly::InvokeKey>, declaredInType=${this.emitTypeSignature(invariants.containingtype)}, file="${invariants.file}", sinfo=${this.emitSourceInfo(invariants.sinfo)}, tag=${invariants.tag !== undefined ? `some('${invariants.tag}')` : "none"} }`;
    }

    private emitAbstractNominalTypeDeclBase(ns: FullyQualifiedNamespace, tsig: NominalTypeSignature, tdecl: AbstractNominalTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): string {
        const tbase = this.emitAbstractDeclBase(tdecl, EmitNameManager.generateNamespaceKey(ns));

        const tkey = EmitNameManager.generateTypeKey(tsig);

        const invariants = tdecl.invariants.map((inv, ii) => this.emitInvariantDecl(inv, EmitNameManager.generateNamespaceKey(ns), tkey, ii)).join(", ");
        const validates = tdecl.validates.map((val, ii) => this.emitValidateDecl(val, EmitNameManager.generateNamespaceKey(ns), tkey, ii)).join(", ");

        this.emitConstMemberDecls(ns, tsig, tdecl.consts);

        const [absmethods, virtmethods, overmethods, staticmethods] = this.emitMethodDecls(ns, [tsig, instantiation.binds], tdecl.methods.map((md) => [md, instantiation.methodbinds.get(md.name)]), fmt);

        // in BSQAssembly::AbstractNominalTypeDecl there is no field for typefuncs, so we just call the emission here and let emitFunctionDecl do the insert
        this.emitFunctionDecls(ns, [tsig, instantiation.binds], tdecl.functions.map(((f) => [f, instantiation.functionbinds.get(f.name)])), fmt);

        const provides = tdecl.saturatedProvides.map((sp) => this.emitTypeSignature(sp)).join(", ");
        const bfields = tdecl.saturatedBFieldInfo.map((sb) => this.emitSaturatedFieldInfo(sb)).join(", ");

        const allInvariants = tdecl.allInvariants.map((ai) => this.emitSaturatedInvariantInfo(ai)).join(", ");
        const allValidates = tdecl.allValidates.map((av) => this.emitSaturatedInvariantInfo(av)).join(", ");

        return `${tbase}, tkey='${tkey}'<BSQAssembly::TypeKey>, name='${tdecl.name}', invariants=List<BSQAssembly::InvariantDecl>{ ${invariants} }, validates=List<BSQAssembly::ValidateDecl>{ ${validates} }, absmethods=List<BSQAssembly::InvokeKey>{ ${absmethods} }, virtmethods=List<BSQAssembly::InvokeKey>{ ${virtmethods} }, overmethods=List<BSQAssembly::InvokeKey>{ ${overmethods} }, staticmethods=List<BSQAssembly::InvokeKey>{ ${staticmethods} }, saturatedProvides=List<BSQAssembly::NominalTypeSignature>{ ${provides} }, saturatedBFieldInfo=List<BSQAssembly::SaturatedFieldInfo>{ ${bfields} }, allInvariants=List<BSQAssembly::SaturatedInvariantInfo>{ ${allInvariants} }, allValidates=List<BSQAssembly::SaturatedInvariantInfo>{ ${allValidates} }`;
    }

    private emitAbstractEntityTypeDeclBase(ns: FullyQualifiedNamespace, tsig: NominalTypeSignature, tdecl: AbstractEntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): string {
        return this.emitAbstractNominalTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);
    }

    private emitEnumTypeDecl(ns: FullyQualifiedNamespace, tdecl: EnumTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        const tbase = this.emitAbstractNominalTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        this.typegraph.set(EmitNameManager.generateTypeKey(tsig), []);

        const fields = tdecl.members.map((mname) => `'${mname}'`).join(", ");
        return [`'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey>`, `'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey> => BSQAssembly::EnumTypeDecl{ ${tbase}, members=List<CString>{ ${fields} } }`];
    }

    private emitTypedeclTypeDecl(ns: FullyQualifiedNamespace, tdecl: TypedeclTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        const tbase = this.emitAbstractNominalTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        this.typegraph.set(EmitNameManager.generateTypeKey(tsig), this.emitChildrenTypes(tdecl.valuetype));

        return [`'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey>`, `'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey> => BSQAssembly::TypedeclTypeDecl{ ${tbase}, valuetype=${this.emitTypeSignature(tdecl.valuetype)} }`];
    }

    private emitTypedeclStringOfTypeDecl(ns: FullyQualifiedNamespace, tdecl: TypedeclTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        const tbase = this.emitAbstractNominalTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        this.typegraph.set(EmitNameManager.generateTypeKey(tsig), this.emitChildrenTypes(tdecl.valuetype));

        return [`'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey>`, `'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey> => BSQAssembly::TypedeclStringOfTypeDecl{ ${tbase}, valuetype=${this.emitTypeSignature(tdecl.valuetype)}, ofexp=${this.emitExpression((tdecl.optofexp as LiteralExpressionValue).exp)} }`];
    }

    private emitInternalEntityTypeDeclBase(ns: FullyQualifiedNamespace, tsig: NominalTypeSignature, tdecl: InternalEntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): string {
        return this.emitAbstractEntityTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);
    }

    private emitPrimitiveEntityTypeDecl(ns: FullyQualifiedNamespace, tdecl: PrimitiveEntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        const ibase = this.emitInternalEntityTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        this.typegraph.set(EmitNameManager.generateTypeKey(tsig), []);

        return [`'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey>`, `'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey> => BSQAssembly::PrimitiveEntityTypeDecl{ ${ibase} }`];
    }

    private emitOkTypeDecl(ns: FullyQualifiedNamespace, tdecl: OkTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T", "E"]);
        const ibase = this.emitInternalEntityTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        this.typegraph.set(EmitNameManager.generateTypeKey(tsig), this.emitChildrenTypes(tsig.alltermargs[0]));

        return [`'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey>`, `'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey> => BSQAssembly::OkTypeDecl{ ${ibase}, oktype=${this.emitTypeSignature(tsig.alltermargs[0])}, failtype=${this.emitTypeSignature(tsig.alltermargs[1])} }`];
    }

    private emitFailTypeDecl(ns: FullyQualifiedNamespace, tdecl: FailTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T", "E"]);
        const ibase = this.emitInternalEntityTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        this.typegraph.set(EmitNameManager.generateTypeKey(tsig), this.emitChildrenTypes(tsig.alltermargs[1]));

        return [`'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey>`, `'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey> => BSQAssembly::FailTypeDecl{ ${ibase}, oktype=${this.emitTypeSignature(tsig.alltermargs[0])}, failtype=${this.emitTypeSignature(tsig.alltermargs[1])} }`];
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

        this.typegraph.set(EmitNameManager.generateTypeKey(tsig), this.emitChildrenTypes(tsig.alltermargs[0]));

        return [`'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey>`, `'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey> => BSQAssembly::SomeTypeDecl{ ${ibase}, oftype=${this.emitTypeSignature(tsig.alltermargs[0])} }`];
    }

    private emitMapEntryTypeDecl(ns: FullyQualifiedNamespace, tdecl: MapEntryTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        assert(false, "Not implemented -- emitMapEntryTypeDecl");
    }

    private emitListTypeDecl(ns: FullyQualifiedNamespace, tdecl: ListTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const ibase = this.emitInternalEntityTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        this.typegraph.set(EmitNameManager.generateTypeKey(tsig), this.emitChildrenTypes(tsig.alltermargs[0]));

        return [`'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey>`, `'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey> => BSQAssembly::ListTypeDecl{ ${ibase}, oftype=${this.emitTypeSignature(tsig.alltermargs[0])} }`];
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

        this.typegraph.set(EmitNameManager.generateTypeKey(tsig), this.emitChildrenTypesForAll(tdecl.saturatedBFieldInfo.map((sfi) => sfi.type)));

        const mfields = tdecl.fields.map((f) => this.emitMemberFieldDecl(ns, tsig, f)).join(", ");
        return [`'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey>`, `'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey> => BSQAssembly::EntityTypeDecl{ ${ibase}, fields=List<BSQAssembly::MemberFieldDecl>{ ${mfields} } }`];
    }

    private emitAbstractConceptTypeDeclBase(ns: FullyQualifiedNamespace, tsig: NominalTypeSignature, tdecl: AbstractConceptTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): string {
        const ccbase = this.emitAbstractNominalTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);
        const subtypes = this.subtypemap.get(EmitNameManager.generateTypeKey(tsig)) as string[];

        this.typegraph.set(EmitNameManager.generateTypeKey(tsig), subtypes);

        const tss = subtypes.map((st) => `'${st}'<BSQAssembly::TypeKey>`).join(", ");
        return `${ccbase}, subtypes=List<BSQAssembly::TypeKey>{ ${tss} }`;
    }

    private emitOptionTypeDecl(ns: FullyQualifiedNamespace, tdecl: OptionTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const ibase = this.emitAbstractConceptTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        const oftype = this.emitTypeSignature(tsig.alltermargs[0]);

        const somedecl = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Some") as AbstractNominalTypeDecl;
        const sometype = new NominalTypeSignature(tdecl.sinfo, undefined, somedecl, tsig.alltermargs);

        return [`'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey>`, `'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey> => BSQAssembly::OptionTypeDecl{ ${ibase}, oftype=${oftype}, someType=${this.emitTypeSignature(sometype)} }`];
    }

    private emitResultTypeDecl(ns: FullyQualifiedNamespace, tdecl: ResultTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        assert(false, "Not implemented -- emitResultTypeDecl");
    }

    private emitAPIResultTypeDecl(ns: FullyQualifiedNamespace, tdecl: APIResultTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        assert(false, "Not implemented -- emitAPIResultTypeDecl");
    }

    private emitConceptTypeDecl(ns: FullyQualifiedNamespace, tdecl: ConceptTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const ibase = this.emitAbstractConceptTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        const fields = tdecl.fields.map((f) => this.emitMemberFieldDecl(ns, tsig, f)).join(", ");
        return [`'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey>`, `'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey> => BSQAssembly::ConceptTypeDecl{ ${ibase}, fields=List<BSQAssembly::MemberFieldDecl>{ ${fields} } }`];
    }

    private emitDatatypeMemberEntityTypeDecl(ns: FullyQualifiedNamespace, tdecl: DatatypeMemberEntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const ibase = this.emitAbstractEntityTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        this.typegraph.set(EmitNameManager.generateTypeKey(tsig), this.emitChildrenTypesForAll(tdecl.saturatedBFieldInfo.map((sfi) => sfi.type)));

        const fields = tdecl.fields.map((f) => this.emitMemberFieldDecl(ns, tsig, f)).join(", ");
        const parenttype = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl.parentTypeDecl, tsig.alltermargs);

        return [`'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey>`, `'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey> => BSQAssembly::DatatypeMemberEntityTypeDecl{ ${ibase}, fields=List<BSQAssembly::MemberFieldDecl>{ ${fields} }, parentTypeDecl=${this.emitTypeSignature(parenttype)} }`];
    }

    private emitDatatypeTypeDecl(ns: FullyQualifiedNamespace, tdecl: DatatypeTypeDecl, instantiation: TypeInstantiationInfo, fmt: BsqonCodeFormatter): [string, string] {
        const tsig = BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const ibase = this.emitAbstractConceptTypeDeclBase(ns, tsig, tdecl, instantiation, fmt);

        const fields = tdecl.fields.map((f) => this.emitMemberFieldDecl(ns, tsig, f)).join(", ");
        const associatedMemberEntityDecls = tdecl.associatedMemberEntityDecls.map((dd) => this.emitTypeSignature(new NominalTypeSignature(dd.sinfo, undefined, dd, tsig.alltermargs))).join(", ");

        return [`'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey>`, `'${EmitNameManager.generateTypeKey(tsig)}'<BSQAssembly::TypeKey> => BSQAssembly::DatatypeTypeDecl{ ${ibase}, fields=List<BSQAssembly::MemberFieldDecl>{ ${fields} }, associatedMemberEntityDecls=List<BSQAssembly::NominalTypeSignature>{ ${associatedMemberEntityDecls} } }`];
    }

    private emitNamespaceConstDecls(ns: FullyQualifiedNamespace, decls: NamespaceConstDecl[]) {
        for(let i = 0; i < decls.length; ++i) {
            const dd = decls[i];

            const dbase = this.emitAbstractCoreDecl(dd, EmitNameManager.generateNamespaceKey(ns), new BsqonCodeFormatter(undefined));
            const dtype = this.emitTypeSignature(dd.declaredType);
            const value = this.emitExpression(dd.value.exp);

            this.nsconsts.push(`BSQAssembly::NamespaceConstDecl{ ${dbase}, declaredType=${dtype}, value=${value} }`);
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
                    const [tkey, decl] = this.emitOptionTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allabstracttypes.push(tkey);
                    this.pconcepts.push(decl);
                }
                else if(tt instanceof ResultTypeDecl) {
                    const [tkey, decl] = this.emitResultTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allabstracttypes.push(tkey);
                    this.pconcepts.push(decl);
                }
                else if(tt instanceof APIResultTypeDecl) {
                    const [tkey, decl] = this.emitAPIResultTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allabstracttypes.push(tkey);
                    this.pconcepts.push(decl);
                }
                else if(tt instanceof ConceptTypeDecl) {
                    const [tkey, decl] = this.emitConceptTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allabstracttypes.push(tkey);
                    this.concepts.push(decl);
                }
                else if(tt instanceof DatatypeMemberEntityTypeDecl) {
                    const [tkey, decl] = this.emitDatatypeMemberEntityTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
                    this.allconcretetypes.push(tkey);
                    this.datamembers.push(decl);
                }
                else if(tt instanceof DatatypeTypeDecl) {
                    const [tkey, decl] = this.emitDatatypeTypeDecl(ns.fullnamespace, tt, instantiation, fmt);
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

        this.emitNamespaceConstDecls(decl.fullnamespace, decl.consts);

        this.emitFunctionDecls(decl.fullnamespace, undefined, decl.functions.map((fd) => [fd, asminstantiation.functionbinds.get(fd.name)]), fmt);
        
        this.emitNamespaceTypeDecls(decl, decl.typedecls, asminstantiation, fmt);
    }

    private computeTKeyForDeclAndInstantiation(tdecl: AbstractNominalTypeDecl, instantiation: TypeInstantiationInfo): NominalTypeSignature {
        if(tdecl instanceof EnumTypeDecl) {
            return new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        }
        else if(tdecl instanceof TypedeclTypeDecl) {
            return new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        }
        else if(tdecl instanceof PrimitiveEntityTypeDecl) {
            return new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        }
        else if(tdecl instanceof OkTypeDecl) {
            return BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T", "E"]);
        }
        else if(tdecl instanceof FailTypeDecl) {
            return BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T", "E"]);
        }
        else if(tdecl instanceof APIRejectedTypeDecl) {
            assert(false, "Not implemented -- emitAPIRejectedTypeDecl");
        }
        else if(tdecl instanceof APIFailedTypeDecl) {
            assert(false, "Not implemented -- emitAPIFailedTypeDecl");
        }
        else if(tdecl instanceof APIErrorTypeDecl) {
            assert(false, "Not implemented -- emitAPIErrorTypeDecl");
        }
        else if(tdecl instanceof APISuccessTypeDecl) {
            assert(false, "Not implemented -- emitAPISuccessTypeDecl");
        }
        else if(tdecl instanceof SomeTypeDecl) {
            return BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        }
        else if(tdecl instanceof MapEntryTypeDecl) {
            assert(false, "Not implemented -- emitMapEntryTypeDecl");
        }
        else if(tdecl instanceof ListTypeDecl) {
            return BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        }
        else if(tdecl instanceof StackTypeDecl) {
            assert(false, "Not implemented -- emitStackTypeDecl");
        }
        else if(tdecl instanceof QueueTypeDecl) {
            assert(false, "Not implemented -- emitQueueTypeDecl");
        }
        else if(tdecl instanceof SetTypeDecl) {
            assert(false, "Not implemented -- emitSetTypeDecl");
        }
        else if(tdecl instanceof MapTypeDecl) {
            assert(false, "Not implemented -- emitMapTypeDecl");
        }
        else if(tdecl instanceof EventListTypeDecl) {
            assert(false, "Not implemented -- emitEventListTypeDecl");
        }
        else if(tdecl instanceof EntityTypeDecl) {
            return BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        }
        else if(tdecl instanceof OptionTypeDecl) {
            return BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        }
        else if(tdecl instanceof ResultTypeDecl) {
            assert(false, "Not implemented -- emitResultTypeDecl");
        }
        else if(tdecl instanceof APIResultTypeDecl) {
            assert(false, "Not implemented -- emitAPIResultTypeDecl");
        }
        else if(tdecl instanceof ConceptTypeDecl) {
            return BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        }
        else if(tdecl instanceof DatatypeMemberEntityTypeDecl) {
            return BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        }
        else if(tdecl instanceof DatatypeTypeDecl) {
            return BSQIREmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        }
        else {
            assert(false, "Unknown type decl kind");
        }
    }

    private computeSubtypesForNamespace(decl: NamespaceDeclaration, asminstantiation: NamespaceInstantiationInfo, aainsts: NamespaceInstantiationInfo[]) {
        for(let i = 0; i < decl.subns.length; ++i) {
            const subdecl = decl.subns[i];
            const nsii = aainsts.find((ai) => ai.ns.emit() === subdecl.fullnamespace.emit());
            
            if(nsii !== undefined) {
                this.computeSubtypesForNamespace(subdecl, nsii, aainsts);
            }
        }

        for(let i = 0; i < decl.typedecls.length; ++i) {
            const tt = decl.typedecls[i];
            const iinsts = asminstantiation.typebinds.get(tt.name);
            if(iinsts === undefined) {
                continue;
            }
            
            for(let j = 0; j < iinsts.length; ++j) {
                const instantiation = iinsts[j];
                this.mapper = instantiation.binds;

                const tsig = this.computeTKeyForDeclAndInstantiation(tt, instantiation);
                const sprovides= tt.saturatedProvides.map((sp) => this.tproc(sp))

                for(let k = 0; k < sprovides.length; ++k) {
                    const st = sprovides[k];
                    const tkey = EmitNameManager.generateTypeKey(st);

                    if(!this.subtypemap.has(tkey)) {
                        this.subtypemap.set(tkey, []);
                    }
                    
                    let ste = this.subtypemap.get(tkey) as string[];
                    ste.push(EmitNameManager.generateTypeKey(tsig));
                }

                this.mapper = undefined;
            }
        }
    }

    private computeSubtypes() {
        for(let i = 0; i < this.assembly.toplevelNamespaces.length; ++i) {
            const nsdecl = this.assembly.toplevelNamespaces[i];
            const nsii = this.asminstantiation.find((ai) => ai.ns.emit() === nsdecl.fullnamespace.emit());
            
            if(nsii !== undefined) {
                this.computeSubtypesForNamespace(nsdecl, nsii, this.asminstantiation);
            }
        }
    }

    private topovisit(gkey: string, topo: string[], visited: Set<string>) {
        if(visited.has(gkey)) {
            return;
        }

        let children: string[] = [...(this.typegraph.get(gkey) as string[])];
        visited.add(gkey);

        while(children.length > 0) {
            const next = children.pop() as string;
            this.topovisit(next, topo, visited);
        }
        topo.push(gkey);
    }


    private computeTypeGraphTopoOrder(): string[] {
        let topo: string[] = [];
        let visited = new Set<string>();

        const tgtypes = [...this.typegraph.keys()].sort();
        for(let i = 0; i < tgtypes.length; ++i) {
            const tkey = tgtypes[i];
            this.topovisit(tkey, topo, visited);
        }

        return topo;
    }

    private sccVisit(gkey: string, visited: Map<string, boolean>, scc: string[]) {
        if(visited.has(gkey)) {
            return;
        }

        visited.set(gkey, false);
        
        let children: string[] = [...(this.typegraph.get(gkey) as string[])];
        while(children.length > 0) {
            const next = children.pop() as string;
            this.sccVisit(next, visited, scc);
        }

        scc.push(gkey);
        visited.set(gkey, true);
    }

    private computeTypeGraphSCCS(topo: string[]): string[][] {
        let visited = new Map<string, boolean>();
        let sccs: string[][] = [];

        for(let i = 0; i < topo.length; ++i) {
            const gkey = topo[i];

            if(!visited.has(gkey)) {
                let children: string[] = [...(this.typegraph.get(gkey) as string[])];
                if(children.every((v) => visited.get(v) === true)) {
                    visited.set(gkey, true);
                }
                else {
                    let scc: string[] = [];
                    this.sccVisit(gkey, visited, scc);

                    sccs.push(scc.filter((v) => this.allconcretetypes.includes(`'${v}'<BSQAssembly::TypeKey>`)));
                }
            }
        }

        return sccs;
    }

    static emitAssembly(assembly: Assembly, asminstantiation: NamespaceInstantiationInfo[]): string {
        const emitter = new BSQIREmitter(assembly, asminstantiation, false, undefined, undefined);
        emitter.computeSubtypes();

        //emit each of the assemblies
        for(let i = 0; i < assembly.toplevelNamespaces.length; ++i) {
            const nsdecl = assembly.toplevelNamespaces[i];
            const nsii = asminstantiation.find((ai) => ai.ns.emit() === nsdecl.fullnamespace.emit());

            if(nsii !== undefined) {
                emitter.emitNamespaceDeclaration(nsdecl, nsii, asminstantiation, new BsqonCodeFormatter(2));
            }
        }

        const topotypes = emitter.computeTypeGraphTopoOrder();
        const sccs = emitter.computeTypeGraphSCCS(topotypes);
        
        const topoinfo = topotypes.map((t) => `'${t}'<BSQAssembly::TypeKey>`);
        const sccinfo = sccs.map((scc) => `List<BSQAssembly::TypeKey>{ ${scc.map((s) => `'${s}'<BSQAssembly::TypeKey>`).join(", ")} }`);
        const cginfo = `BSQAssembly::TypeTopology{ ctopo=List<BSQAssembly::TypeKey>{ ${topoinfo.join(", ")} }, sccs=List<List<BSQAssembly::TypeKey>>{ ${sccinfo.join(", ")} } }`;

        let fmt = new BsqonCodeFormatter(1);
        return "BSQAssembly::Assembly{\n" +
            fmt.formatListOf("List<BSQAssembly::NamespaceConstDecl>{", emitter.nsconsts, "},\n") +
            fmt.formatListOf("List<BSQAssembly::ConstMemberDecl>{", emitter.typeconsts, "},\n") +

            fmt.formatListOf("Map<BSQAssembly::InvokeKey, BSQAssembly::NamespaceFunctionDecl>{", emitter.nsfuncs, "},\n") +
            fmt.formatListOf("Map<BSQAssembly::InvokeKey, BSQAssembly::TypeFunctionDecl>{", emitter.typefuncs, "},\n") +
            
            fmt.formatListOf("Map<BSQAssembly::InvokeKey, BSQAssembly::MethodDeclAbstract>{", emitter.absmethods, "},\n") +
            fmt.formatListOf("Map<BSQAssembly::InvokeKey, BSQAssembly::MethodDeclVirtual>{", emitter.virtmethods, "},\n") +
            fmt.formatListOf("Map<BSQAssembly::InvokeKey, BSQAssembly::MethodDeclOverride>{", emitter.overmethods, "},\n") +
            fmt.formatListOf("Map<BSQAssembly::InvokeKey, BSQAssembly::MethodDeclStatic>{", emitter.staticmethods, "},\n") +
            
            fmt.formatListOf("Map<BSQAssembly::TypeKey, BSQAssembly::EnumTypeDecl>{", emitter.enums, "},\n") +
            fmt.formatListOf("Map<BSQAssembly::TypeKey, BSQAssembly::TypedeclTypeDecl>{", emitter.typedecls, "},\n") +
            fmt.formatListOf("Map<BSQAssembly::TypeKey, BSQAssembly::PrimitiveEntityTypeDecl>{", emitter.primtives, "},\n") +
            fmt.formatListOf("Map<BSQAssembly::TypeKey, BSQAssembly::ConstructableTypeDecl>{", emitter.constructables, "},\n") +
            fmt.formatListOf("Map<BSQAssembly::TypeKey, BSQAssembly::CollectionTypeDecl>{", emitter.collections, "},\n") +
            fmt.formatListOf("Map<BSQAssembly::TypeKey, BSQAssembly::EntityTypeDecl>{", emitter.entities, "},\n") +
            fmt.formatListOf("Map<BSQAssembly::TypeKey, BSQAssembly::DatatypeMemberEntityTypeDecl>{", emitter.datamembers, "},\n") +
            
            fmt.formatListOf("Map<BSQAssembly::TypeKey, BSQAssembly::PrimitiveConceptTypeDecl>{", emitter.pconcepts, "},\n") +
            fmt.formatListOf("Map<BSQAssembly::TypeKey, BSQAssembly::ConceptTypeDecl>{", emitter.concepts, "},\n") +
            fmt.formatListOf("Map<BSQAssembly::TypeKey, BSQAssembly::DatatypeTypeDecl>{", emitter.datatypes, "},\n") +
            
            fmt.formatListOf("List<BSQAssembly::InvokeKey>{", emitter.allfuncs, "},\n") +
            fmt.formatListOf("List<BSQAssembly::InvokeKey>{", emitter.allmethods, "},\n") +
            fmt.formatListOf("List<BSQAssembly::InvokeKey>{", emitter.allvmethods, "},\n") +
            
            fmt.formatListOf("List<BSQAssembly::TypeKey>{", emitter.allconcretetypes, "},\n") +
            fmt.formatListOf("List<BSQAssembly::TypeKey>{", emitter.allabstracttypes, "},\n") +
            fmt.indent(cginfo) + "\n" +
        "}";
    }
}

export {
    BSQIREmitter
};