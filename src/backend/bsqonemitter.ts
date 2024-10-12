import assert from "node:assert";

import { AbstractNominalTypeDecl, APIErrorTypeDecl, APIFailedTypeDecl, APIRejectedTypeDecl, APIResultTypeDecl, APISuccessTypeDecl, Assembly, ConceptTypeDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, DeclarationAttibute, EntityTypeDecl, EnumTypeDecl, FailTypeDecl, InternalEntityTypeDecl, ListTypeDecl, MapEntryTypeDecl, MapTypeDecl, MemberFieldDecl, OkTypeDecl, OptionTypeDecl, PrimitiveEntityTypeDecl, QueueTypeDecl, SetTypeDecl, SomeTypeDecl, StackTypeDecl, TypedeclTypeDecl } from "../frontend/assembly.js";
import { NominalTypeSignature, TemplateNameMapper, TemplateTypeSignature, TypeSignature } from "../frontend/type.js";
import { TypeInstantiationInfo } from "../frontend/instantiation_map.js";
import { AccessNamespaceConstantExpression, LiteralRegexExpression } from "../frontend/body.js";
import { SourceInfo } from "../frontend/build_decls.js";

class BSQONTypeInfoEmitter {
    readonly assembly: Assembly;

    mapper: TemplateNameMapper | undefined;

    constructor(assembly: Assembly) {
        this.assembly = assembly;
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
            decl.attributes = this.emitTypeAttributes(tdecl.attributes, isrecursive);
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
            decl.attributes = this.emitTypeAttributes(tdecl.attributes, isrecursive);
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

        decl.variants = tdecl.members;

        decl.supertypes = [];
        decl.tkey = rcvr.tkeystr;

        this.mapper = undefined;
        
        return decl;
    }

    private emitTypedeclTypeDecl(tdecl: TypedeclTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);

        let decl: any = {};

        decl.tag = "TypeDecl";
        if(tdecl.attributes.length !== 0) {
            decl.attributes = this.emitTypeAttributes(tdecl.attributes, false);
        }

        if(tdecl.optofexp !== undefined) {
            if(tdecl.optofexp.exp instanceof LiteralRegexExpression) {
                decl.ofvalidator = tdecl.optofexp.exp.value;
            }
            else {
                const ane = tdecl.optofexp.exp as AccessNamespaceConstantExpression;
                decl.ofvalidator = ane.ns.emit() + "::" + ane.name;
            }
        }

        decl.hasvalidations = tdecl.allInvariants.length !== 0 || tdecl.allValidates.length !== 0;
        decl.valuetype = tdecl.valuetype.tkeystr;

        decl.supertypes = this.emitSuperTypes(tdecl, rcvr);
        decl.tkey = rcvr.tkeystr;

        return decl;
    }

    private emitOkTypeDecl(tdecl: OkTypeDecl, instantiation: TypeInstantiationInfo, isrecursive: boolean): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T", "E"]);
        const okdecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "Result::Ok", isrecursive);
        okdecl.ttype = rcvr.alltermargs[0].tkeystr;
        okdecl.etype = rcvr.alltermargs[1].tkeystr;

        return okdecl;
    }

    private emitFailTypeDecl(tdecl: FailTypeDecl, instantiation: TypeInstantiationInfo, isrecursive: boolean): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T", "E"]);
        const faildecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "Result::Fail", isrecursive);
        faildecl.ttype = rcvr.alltermargs[0].tkeystr;
        faildecl.etype = rcvr.alltermargs[1].tkeystr;

        return faildecl;
    }

    private emitAPIRejectedTypeDecl(tdecl: APIRejectedTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        const rejecteddecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "APIResult::Rejected", false);
        rejecteddecl.ttype = rcvr.alltermargs[0].tkeystr;

        return rejecteddecl;
    }

    private emitAPIFailedTypeDecl(tdecl: APIFailedTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        const faileddecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "APIResult::Failed", false);
        faileddecl.ttype = rcvr.alltermargs[0].tkeystr;

        return faileddecl;
    }

    private emitAPIErrorTypeDecl(tdecl: APIErrorTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        const errordecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "APIResult::Error", false);
        errordecl.ttype = rcvr.alltermargs[0].tkeystr;

        return errordecl;
    }

    private emitAPISuccessTypeDecl(tdecl: APISuccessTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        const successdecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "APIResult::Success", false);
        successdecl.ttype = rcvr.alltermargs[0].tkeystr;

        return successdecl;
    }

    private emitSomeTypeDecl(tdecl: SomeTypeDecl, instantiation: TypeInstantiationInfo, isrecursive: boolean): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const somedecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "Some", isrecursive);
        somedecl.oftype = rcvr.alltermargs[0].tkeystr;

        return somedecl;
    }

    private emitMapEntryTypeDecl(tdecl: MapEntryTypeDecl, instantiation: TypeInstantiationInfo, isrecursive: boolean): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const medecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "MapEntry", isrecursive);
        medecl.ktype = rcvr.alltermargs[0].tkeystr;
        medecl.vtype = rcvr.alltermargs[1].tkeystr;

        return medecl;
    }

    private emitListTypeDecl(tdecl: ListTypeDecl, instantiation: TypeInstantiationInfo, isrecursive: boolean): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const ldecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "List", isrecursive);
        ldecl.oftype = rcvr.alltermargs[0].tkeystr;

        return ldecl;
    }

    private emitStackTypeDecl(tdecl: StackTypeDecl, instantiation: TypeInstantiationInfo, isrecursive: boolean): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const sdecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "Stack", isrecursive);
        sdecl.oftype = rcvr.alltermargs[0].tkeystr;

        return sdecl;
    }

    private emitQueueTypeDecl(tdecl: QueueTypeDecl, instantiation: TypeInstantiationInfo, isrecursive: boolean): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const qdecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "Queue", isrecursive);
        qdecl.oftype = rcvr.alltermargs[0].tkeystr;

        return qdecl;
    }

    private emitSetTypeDecl(tdecl: SetTypeDecl, instantiation: TypeInstantiationInfo, isrecursive: boolean): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const sdecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "Set", isrecursive);
        sdecl.oftype = rcvr.alltermargs[0].tkeystr;

        return sdecl;
    }

    private emitMapTypeDecl(tdecl: MapTypeDecl, instantiation: TypeInstantiationInfo, isrecursive: boolean): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const mdecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "Map", isrecursive);
        mdecl.ktype = rcvr.alltermargs[0].tkeystr;
        mdecl.vtype = rcvr.alltermargs[1].tkeystr;

        return mdecl;
    }

    private emitEntityTypeDecl(tdecl: EntityTypeDecl, instantiation: TypeInstantiationInfo, isrecursive: boolean): any {
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

    private emitOptionTypeDecl(tdecl: OptionTypeDecl, instantiation: TypeInstantiationInfo, isrecursive: boolean): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitResultTypeDecl(tdecl: ResultTypeDecl, instantiation: TypeInstantiationInfo, isrecursive: boolean): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [okdecl, faildecl], undefined);
    }

    private emitAPIResultTypeDecl(tdecl: APIResultTypeDecl, instantiation: TypeInstantiationInfo, isrecursive: boolean): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [rejecteddecl, faileddecl, errordecl, successdecl], undefined);
    }

    private emitConceptTypeDecl(tdecl: ConceptTypeDecl, instantiation: TypeInstantiationInfo, isrecursive: boolean): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
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

    private emitDatatypeMemberEntityTypeDecl(tdecl: DatatypeMemberEntityTypeDecl, instantiation: TypeInstantiationInfo, isrecursive: boolean): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
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

    private emitDatatypeTypeDecl(tdecl: DatatypeTypeDecl, instantiation: TypeInstantiationInfo, isrecursive: boolean): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
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
