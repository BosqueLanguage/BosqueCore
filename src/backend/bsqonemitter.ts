import assert from "node:assert";

import { AbstractNominalTypeDecl, Assembly, DeclarationAttibute, EnumTypeDecl, InternalEntityTypeDecl, MemberFieldDecl, PrimitiveEntityTypeDecl, TypedeclTypeDecl } from "../frontend/assembly.js";
import { NominalTypeSignature, TemplateNameMapper, TypeSignature } from "../frontend/type.js";
import { TypeInstantiationInfo } from "../frontend/instantiation_map.js";

class BSQONTypeInfoEmitter {
    readonly assembly: Assembly;

    mapper: TemplateNameMapper | undefined;

    constructor(assembly: Assembly) {
        this.assembly = assembly;
    }

    private getTemplateMapper(): TemplateNameMapper {
        assert(this.mapper !== undefined, "Template mapper is not set");
        return this.mapper;
    }

    private tproc(ttype: TypeSignature): TypeSignature {
        return this.mapper !== undefined ? ttype.remapTemplateBindings(this.getTemplateMapper()) : ttype;
    }

    private emitTypeAttributes(attrs: DeclarationAttibute[], isrecursive: boolean): any {
        let attr: any = {};

        if(isrecursive) {
            attr.isrecursive = true;
        }

        const docattr = attrs.find((aa) => aa.name === "doc");
        if(docattr !== undefined) {
            attr.docstring = docattr.text;
        }

        const sensattr = attrs.find((aa) => aa.name === "sensitive");
        if(sensattr !== undefined) {
            attr.sensitive = sensattr.tags.map((aa) => [aa.enumType.tkeystr, aa.tag]);
        }

        return attr;
    }

    private emitFieldAttributes(attrs: DeclarationAttibute[]): any {
        xxxx;
    }

    private emitSuperTypes(tdecl: AbstractNominalTypeDecl, rcvr: NominalTypeSignature): string[] {
        xxxx;
    }

    private emitStdTypeDeclHelper(tdecl: AbstractNominalTypeDecl, rcvr: NominalTypeSignature, optfdecls: MemberFieldDecl[], instantiation: TypeInstantiationInfo, tag: string, isentity: boolean, isrecursive: boolean): any {
        if(tdecl.terms.length !== 0) {
            this.mapper = instantiation.binds;
        }

        let decl: any = {};

        decl.tag = tag;
        if(tdecl.attributes.length !== 0) {
            decl.attributes = this.emitTypeAttributes(tdecl.attributes);
        }
        
        decl.supertypes = this.emitSuperTypes(tdecl, rcvr);

        if(isentity) {
            decl.fields = optfdecls.map((ff) => {
                let fdecl: any = {};
                fdecl.name = ff.name;
                fdecl.type = this.tproc(ff.declaredType).tkeystr;
                fdecl.isOptional = ff.defaultValue !== undefined;
                if(ff.attributes.length !== 0) {
                    fdecl.fsannotation = this.emitFieldAttributes(ff.attributes);
                }

                return fdecl;
            });

            decl.hasvalidations = tdecl.allInvariants.length !== 0 || tdecl.allValidates.length !== 0;
        }

        decl.tkey = rcvr.tkeystr;

        this.mapper = undefined;

        return decl;
    }

    private emitInteralSimpleTypeDeclHelper(tdecl: InternalEntityTypeDecl, rcvr: NominalTypeSignature, instantiation: TypeInstantiationInfo, tag: string, isrecursive: boolean): any {
        if(tdecl.terms.length !== 0) {
            this.mapper = instantiation.binds;
        }

        let decl: any = {};

        decl.tag = tag;
        if(tdecl.attributes.length !== 0) {
            decl.attributes = this.emitTypeAttributes(tdecl.attributes);
        }

        decl.supertypes = this.emitSuperTypes(tdecl, rcvr);
        decl.tkey = rcvr.tkeystr;

        this.mapper = undefined;
        
        return decl;
    }

    private emitPrimitiveEntityTypeDecl(tdecl: PrimitiveEntityTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "PrimitiveEntity", false);
    }

    private emitEnumTypeDecl(tdecl: EnumTypeDecl): any {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);

        let decl: any = {};

        decl.tag = "EnumEntity";
        if(tdecl.attributes.length !== 0) {
            decl.attributes = this.emitTypeAttributes(tdecl.attributes, false);
        }

        decl.supertypes = [];
        decl.tkey = rcvr.tkeystr;

        this.mapper = undefined;
        
        return decl;
    }

    private emitTypedeclTypeDecl(tdecl: TypedeclTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): {decl: string, tests: string[]} {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);

        fmt.indentPush();
        let decls: string[] = [];
        let tests: string[] = [];

        decls.push(this.emitTypeSymbol(rcvr));

        //make sure all of the invariants on this typecheck
        decls.push(...this.emitInvariants(rcvr, tdecl.saturatedBFieldInfo, tdecl.invariants));
        decls.push(...this.emitValidates(rcvr, tdecl.saturatedBFieldInfo, tdecl.validates));

        if(tdecl.optofexp !== undefined || tdecl.allInvariants.length !== 0) {
            decls.push(this.emitCreate(tdecl, rcvr, fmt));
        }

        if(tdecl.optofexp !== undefined || tdecl.allInvariants.length !== 0 || tdecl.allValidates.length !== 0) {
            decls.push(this.emitCreateAPIValidate(tdecl, rcvr, fmt));
        }

        decls.push(...this.emitConstMemberDecls(tdecl.consts));

        const fdecls = this.emitFunctionDecls(rcvr, tdecl.functions.map((fd) => [fd, instantiation.functionbinds.get(fd.name)]), fmt);
        decls.push(...fdecls.decls);
        tests.push(...fdecls.tests);

        const mdecls = this.emitMethodDecls(rcvr, tdecl.methods.map((md) => [md, instantiation.methodbinds.get(md.name)]), fmt);
        decls.push(...mdecls.decls);
        tests.push(...mdecls.tests);

        if(tdecl.hasDynamicInvokes) {
            decls.push(this.emitVTable(tdecl, fmt));
        }

        const declsentry = [...decls].map((dd) => fmt.indent(dd)).join(",\n");

        fmt.indentPop();

        const obj = `{\n${declsentry}\n${fmt.indent("}")}`;

        return {decl: `export const ${tdecl.name} = ${obj}`, tests: tests};
    }

    private emitOkTypeDecl(ns: NamespaceDeclaration, tdecl: OkTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T", "E"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], "Result");
    }

    private emitFailTypeDecl(ns: NamespaceDeclaration, tdecl: FailTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T", "E"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], "Result");
    }

    private emitAPIRejectedTypeDecl(ns: NamespaceDeclaration, tdecl: APIRejectedTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], "APIResult");
    }

    private emitAPIFailedTypeDecl(ns: NamespaceDeclaration, tdecl: APIFailedTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], "APIResult");
    }

    private emitAPIErrorTypeDecl(ns: NamespaceDeclaration, tdecl: APIErrorTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], "APIResult");
    }

    private emitAPISuccessTypeDecl(ns: NamespaceDeclaration, tdecl: APISuccessTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], "APIResult");
    }

    private emitSomeTypeDecl(ns: NamespaceDeclaration, tdecl: SomeTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitMapEntryTypeDecl(ns: NamespaceDeclaration, tdecl: MapEntryTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitListTypeDecl(ns: NamespaceDeclaration, tdecl: ListTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitStackTypeDecl(ns: NamespaceDeclaration, tdecl: StackTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitQueueTypeDecl(ns: NamespaceDeclaration, tdecl: QueueTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitSetTypeDecl(ns: NamespaceDeclaration, tdecl: SetTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitMapTypeDecl(ns: NamespaceDeclaration, tdecl: MapTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitEventListTypeDecl(ns: NamespaceDeclaration, tdecl: EventListTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitEntityTypeDecl(ns: NamespaceDeclaration, tdecl: EntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): {decl: string, tests: string[]} {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
        const rr = this.emitStdTypeDeclHelper(tdecl, rcvr, tdecl.fields, instantiation, true, fmt);
        fmt.indentPush();
        const declsfmt = rr.decls.map((dd) => fmt.indent(dd)).join(",\n");
        fmt.indentPop();

        const obj = `{\n${declsfmt}\n${fmt.indent("}")}`;

        if(tdecl.terms.length !== 0) {
            return {decl: `${EmitNameManager.emitTypeTermKey(rcvr)}: ${obj}`, tests: rr.tests};
        }
        else {
            return {decl: `export const ${tdecl.name} = ${obj}`, tests: rr.tests};
        }
    }

    private emitOptionTypeDecl(ns: NamespaceDeclaration, tdecl: OptionTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitResultTypeDecl(ns: NamespaceDeclaration, tdecl: ResultTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        fmt.indentPush();
        const okdecl = this.emitOkTypeDecl(ns, tdecl.getOkType(), instantiation, fmt);
        const faildecl = this.emitFailTypeDecl(ns, tdecl.getFailType(), instantiation, fmt);
        fmt.indentPop();

        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [okdecl, faildecl], undefined);
    }

    private emitAPIResultTypeDecl(ns: NamespaceDeclaration, tdecl: APIResultTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        fmt.indentPush();
        const rejecteddecl = this.emitAPIRejectedTypeDecl(ns, tdecl.getAPIRejectedType(), instantiation, fmt);
        const faileddecl = this.emitAPIFailedTypeDecl(ns, tdecl.getAPIFailedType(), instantiation, fmt);
        const errordecl = this.emitAPIErrorTypeDecl(ns, tdecl.getAPIErrorType(), instantiation, fmt);
        const successdecl = this.emitAPISuccessTypeDecl(ns, tdecl.getAPISuccessType(), instantiation, fmt);
        fmt.indentPop();

        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [rejecteddecl, faileddecl, errordecl, successdecl], undefined);
    }

    private emitConceptTypeDecl(ns: NamespaceDeclaration, tdecl: ConceptTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): {decl: string, tests: string[]} {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
        const rr = this.emitStdTypeDeclHelper(tdecl, rcvr, tdecl.fields, instantiation, false, fmt);
        fmt.indentPush();
        const declsfmt = rr.decls.map((dd) => fmt.indent(dd)).join(",\n");
        fmt.indentPop();

        const obj = `{\n${declsfmt}\n${fmt.indent("}")}`;

        if(tdecl.terms.length !== 0) {
            return {decl: `${EmitNameManager.emitTypeTermKey(rcvr)}: ${obj}`, tests: rr.tests};
        }
        else {
            return {decl: `export const ${tdecl.name} = ${obj}`, tests: rr.tests};
        }
    }

    private emitDatatypeMemberEntityTypeDecl(ns: NamespaceDeclaration, tdecl: DatatypeMemberEntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): {decl: string, tests: string[]} {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
        const rr = this.emitStdTypeDeclHelper(tdecl, rcvr, tdecl.fields, instantiation, true, fmt);
        fmt.indentPush();
        const declsfmt = rr.decls.map((dd) => fmt.indent(dd)).join(",\n");
        fmt.indentPop();

        const obj = `{\n${declsfmt}\n${fmt.indent("}")}`;

        if(tdecl.terms.length !== 0) {
            return {decl: `${EmitNameManager.emitTypeTermKey(rcvr)}: ${obj}`, tests: rr.tests};
        }
        else {
            return {decl: `export const ${tdecl.name} = ${obj}`, tests: rr.tests};
        }
    }

    private emitDatatypeTypeDecl(ns: NamespaceDeclaration, tdecl: DatatypeTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): {decl: string, tests: string[]} {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
        const rr = this.emitStdTypeDeclHelper(tdecl, rcvr, tdecl.fields, instantiation, false, fmt);
        fmt.indentPush();
        const declsfmt = rr.decls.map((dd) => fmt.indent(dd)).join(",\n");
        fmt.indentPop();

        const obj = `{\n${declsfmt}\n${fmt.indent("}")}`;

        if(tdecl.terms.length !== 0) {
            return {decl: `${EmitNameManager.emitTypeTermKey(rcvr)}: ${obj}`, tests: rr.tests};
        }
        else {
            return {decl: `export const ${tdecl.name} = ${obj}`, tests: rr.tests};
        }
    }
}

export {
    BSQONTypeInfoEmitter
};
