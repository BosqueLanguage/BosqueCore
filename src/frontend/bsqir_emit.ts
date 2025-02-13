import assert from "node:assert";

import { AbstractCollectionTypeDecl, AbstractNominalTypeDecl, Assembly, ConstructableTypeDecl, EntityTypeDecl, ListTypeDecl, MapTypeDecl, NamespaceDeclaration, TestAssociation, TypedeclTypeDecl } from "./assembly.js";
import { NamespaceInstantiationInfo } from "./instantiation_map.js";
import { BuildLevel, SourceInfo } from "./build_decls.js";
import { EListTypeSignature, LambdaParameterSignature, LambdaTypeSignature, NominalTypeSignature, RecursiveAnnotation, TemplateNameMapper, TypeSignature, VoidTypeSignature } from "./type.js";
import { AccessEnumExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, ArgumentList, ArgumentValue, ConstructorEListExpression, ConstructorExpression, ConstructorPrimaryExpression, Expression, LiteralNoneExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralTypeDeclValueExpression, NamedArgumentValue, PositionalArgumentValue, RefArgumentValue, SpreadArgumentValue } from "./body.js";


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
            const opcheck = cdecl.optofexp !== undefined ? "Some<Expression>{this.emitExpression(cdecl.optofexp.exp)}" : "none";
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

    private emitExpression(exp: Expression): string {
        xxxx;
    }
}

export {
    BSQIREmitter
};
