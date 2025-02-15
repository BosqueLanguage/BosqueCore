import assert from "node:assert";

import { AbstractCollectionTypeDecl, AbstractNominalTypeDecl, Assembly, ConstructableTypeDecl, EntityTypeDecl, ListTypeDecl, MapTypeDecl, NamespaceDeclaration, NamespaceFunctionDecl, TestAssociation, TypedeclTypeDecl } from "./assembly.js";
import { NamespaceInstantiationInfo } from "./instantiation_map.js";
import { BuildLevel, SourceInfo } from "./build_decls.js";
import { EListTypeSignature, FullyQualifiedNamespace, LambdaParameterSignature, LambdaTypeSignature, NominalTypeSignature, RecursiveAnnotation, TemplateNameMapper, TypeSignature, VoidTypeSignature } from "./type.js";
import { AccessEnumExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, ArgumentList, ArgumentValue, CallNamespaceFunctionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, CreateDirectExpression, Expression, LambdaInvokeExpression, LetExpression, LiteralNoneExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralTypeDeclValueExpression, LogicActionAndExpression, LogicActionOrExpression, NamedArgumentValue, ParseAsTypeExpression, PositionalArgumentValue, RefArgumentValue, SafeConvertExpression, SpecialConstructorExpression, SpreadArgumentValue } from "./body.js";


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

    private emitCollectionConstructorOfArgType(elemtype: TypeSignature, exp: ConstructorPrimaryExpression): string {
        const cpee = this.emitConstructorPrimaryExpressionBase(exp);

        if(exp.args.args.every((arg) => arg instanceof PositionalArgumentValue)) {
            return `ConstructorPrimaryCollectionSingletonsExpression{ ${cpee}, elemtype=${this.emitTypeSignature(elemtype)} }`;
        }
        else {
            assert(false, "Not implemented -- ConstructorPrimaryCollection -- Spreads");
        }
    }

    private emitCollectionConstructor(cdecl: AbstractCollectionTypeDecl, exp: ConstructorPrimaryExpression): string {
        const ctype = this.tproc(exp.ctype) as NominalTypeSignature;

        if(cdecl instanceof ListTypeDecl) {
            const ttype = ctype.alltermargs[0];
            return this.emitCollectionConstructorOfArgType(ttype, exp);
        }
        else if(cdecl instanceof MapTypeDecl) {
            const tval = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "MapEntry") as AbstractNominalTypeDecl;
            const mentry = new NominalTypeSignature(ctype.sinfo, undefined, tval, ctype.alltermargs);

            return this.emitCollectionConstructorOfArgType(mentry, exp);
        }
        else {
            assert(false, "Unknown collection type -- emitCollectionConstructor");
        }
    }

    private emitSpecialConstructableConstructor(exp: ConstructorPrimaryExpression): string {
        const cpee = this.emitConstructorPrimaryExpressionBase(exp);

        return `ConstructorPrimarySpecialConstructableExpression{ ${cpee} }`;
    }

    private emitTypeDeclConstructor(cdecl: TypedeclTypeDecl, exp: ConstructorPrimaryExpression): string {
        const cpee = this.emitConstructorPrimaryExpressionBase(exp);
        const invchecks = cdecl.allInvariants.length !== 0;

        if(cdecl.valuetype.tkeystr !== "CString" && cdecl.valuetype.tkeystr !== "String") {
            return `ConstructorTypeDeclExpression{ ${cpee}, invchecks=${invchecks} }`;
            
        }
        else {
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
    
    private emitCallTypeFunctionExpressionSpecial(exp: CallTypeFunctionExpression, rtrgt: NominalTypeSignature): string {
        const sexp = (exp.shuffleinfo[0][1] as TypeSignature).tkeystr
        const simple = (sexp === "CString" || sexp === "String");

        const cbe = this.emitExpressionBase(exp);

        const cdecl = rtrgt.decl as TypedeclTypeDecl;
        const invchecks = cdecl.allInvariants.length !== 0;

        if(simple) {
            const arg = this.emitArgumentListSinglePositional(exp.args.args[0].exp);
            const opcheck = cdecl.optofexp !== undefined ? `some(${this.emitExpression(cdecl.optofexp.exp)}` : "none";
            return `ConstructorTypeDeclStringExpression{ ${cbe}, args=${arg}, ctype=${this.emitTypeSignature(rtrgt)}, invchecks=${invchecks}, opcheck=${opcheck} }`;
        }
        else {
            assert(false, "Not implemented -- CallTypeFunctionExpressionSpecial with complex arg access");
        }
    }

    private emitCallTypeFunctionExpression(exp: CallTypeFunctionExpression): string {
        const rtrgt = (this.tproc(exp.resolvedDeclType as TypeSignature) as NominalTypeSignature);

        if(exp.isSpecialCall) {
            return this.emitCallTypeFunctionExpressionSpecial(exp, rtrgt);
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

    private emitExpression(exp: Expression): string {
        xxxx;
    }
}

export {
    BSQIREmitter
};
