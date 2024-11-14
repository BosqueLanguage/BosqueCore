import assert from "node:assert";

import { AbstractNominalTypeDecl, APIErrorTypeDecl, APIFailedTypeDecl, APIRejectedTypeDecl, APIResultTypeDecl, APISuccessTypeDecl, Assembly, ConceptTypeDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, DeclarationAttibute, EntityTypeDecl, EnumTypeDecl, EventListTypeDecl, FailTypeDecl, InternalEntityTypeDecl, ListTypeDecl, MapEntryTypeDecl, MapTypeDecl, MemberFieldDecl, NamespaceDeclaration, OkTypeDecl, OptionTypeDecl, PrimitiveEntityTypeDecl, QueueTypeDecl, ResultTypeDecl, SetTypeDecl, SomeTypeDecl, StackTypeDecl, TypedeclTypeDecl } from "../frontend/assembly.js";
import { NominalTypeSignature, TemplateNameMapper, TemplateTypeSignature, TypeSignature } from "../frontend/type.js";
import { NamespaceInstantiationInfo, TypeInstantiationInfo } from "../frontend/instantiation_map.js";
import { AccessNamespaceConstantExpression, LiteralRegexExpression } from "../frontend/body.js";
import { SourceInfo } from "../frontend/build_decls.js";

class BSQONTypeInfoEmitter {
    readonly assembly: Assembly;
    readonly coreinstantiation: NamespaceInstantiationInfo;
    
    mapper: TemplateNameMapper | undefined;

    constructor(assembly: Assembly, coreinstantiation: NamespaceInstantiationInfo) {
        this.assembly = assembly;
        this.coreinstantiation = coreinstantiation;
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

    private emitTypeAttributes(attrs: DeclarationAttibute[]): any {
        let attr: any = {};

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
        let attr: any = {};

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

    private emitSuperTypes(tdecl: AbstractNominalTypeDecl, rcvr: NominalTypeSignature): string[] | undefined {
        if(tdecl.name === "None" || tdecl.saturatedProvides.length === 0) {
            return undefined;
        }
        
        return tdecl.saturatedProvides.map((ss) => ss.tkeystr);
    }

    private emitStdTypeDeclHelper(tdecl: AbstractNominalTypeDecl, rcvr: NominalTypeSignature, optfdecls: MemberFieldDecl[], instantiation: TypeInstantiationInfo, tag: string, isentity: boolean): any {
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
        decl.name = decl.name;

        this.mapper = undefined;

        return decl;
    }

    private emitInteralSimpleTypeDeclHelper(tdecl: InternalEntityTypeDecl, rcvr: NominalTypeSignature, instantiation: TypeInstantiationInfo, tag: string): any {
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
        decl.name = decl.name;

        this.mapper = undefined;
        
        return decl;
    }

    private emitPrimitiveEntityTypeDecl(tdecl: PrimitiveEntityTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "PrimitiveEntity");
    }

    private emitEnumTypeDecl(tdecl: EnumTypeDecl): any {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);

        let decl: any = {};

        decl.tag = "EnumEntity";
        if(tdecl.attributes.length !== 0) {
            decl.attributes = this.emitTypeAttributes(tdecl.attributes);
        }

        decl.variants = tdecl.members;

        decl.supertypes = [];
        decl.tkey = rcvr.tkeystr;
        decl.name = decl.name;

        this.mapper = undefined;
        
        return decl;
    }

    private emitTypedeclTypeDecl(tdecl: TypedeclTypeDecl): any {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);

        let decl: any = {};

        decl.tag = "TypeDecl";
        if(tdecl.attributes.length !== 0) {
            decl.attributes = this.emitTypeAttributes(tdecl.attributes);
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
        decl.name = decl.name;

        return decl;
    }

    private emitOkTypeDecl(tdecl: OkTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T", "E"]);
        const okdecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "Result::Ok");
        okdecl.ttype = rcvr.alltermargs[0].tkeystr;
        okdecl.etype = rcvr.alltermargs[1].tkeystr;

        return okdecl;
    }

    private emitFailTypeDecl(tdecl: FailTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T", "E"]);
        const faildecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "Result::Fail");
        faildecl.ttype = rcvr.alltermargs[0].tkeystr;
        faildecl.etype = rcvr.alltermargs[1].tkeystr;

        return faildecl;
    }

    private emitAPIRejectedTypeDecl(tdecl: APIRejectedTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        const rejecteddecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "APIResult::Rejected");
        rejecteddecl.ttype = rcvr.alltermargs[0].tkeystr;

        return rejecteddecl;
    }

    private emitAPIFailedTypeDecl(tdecl: APIFailedTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        const faileddecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "APIResult::Failed");
        faileddecl.ttype = rcvr.alltermargs[0].tkeystr;

        return faileddecl;
    }

    private emitAPIErrorTypeDecl(tdecl: APIErrorTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        const errordecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "APIResult::Error");
        errordecl.ttype = rcvr.alltermargs[0].tkeystr;

        return errordecl;
    }

    private emitAPISuccessTypeDecl(tdecl: APISuccessTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        const successdecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "APIResult::Success");
        successdecl.ttype = rcvr.alltermargs[0].tkeystr;

        return successdecl;
    }

    private emitSomeTypeDecl(tdecl: SomeTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const somedecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "Some");
        somedecl.oftype = rcvr.alltermargs[0].tkeystr;

        return somedecl;
    }

    private emitMapEntryTypeDecl(tdecl: MapEntryTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const medecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "MapEntry");
        medecl.ktype = rcvr.alltermargs[0].tkeystr;
        medecl.vtype = rcvr.alltermargs[1].tkeystr;

        return medecl;
    }

    private emitListTypeDecl(tdecl: ListTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const ldecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "List");
        ldecl.oftype = rcvr.alltermargs[0].tkeystr;

        return ldecl;
    }

    private emitStackTypeDecl(tdecl: StackTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const sdecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "Stack");
        sdecl.oftype = rcvr.alltermargs[0].tkeystr;

        return sdecl;
    }

    private emitQueueTypeDecl(tdecl: QueueTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const qdecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "Queue");
        qdecl.oftype = rcvr.alltermargs[0].tkeystr;

        return qdecl;
    }

    private emitSetTypeDecl(tdecl: SetTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const sdecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "Set");
        sdecl.oftype = rcvr.alltermargs[0].tkeystr;

        return sdecl;
    }

    private emitMapTypeDecl(tdecl: MapTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const mdecl = this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "Map");
        mdecl.ktype = rcvr.alltermargs[0].tkeystr;
        mdecl.vtype = rcvr.alltermargs[1].tkeystr;

        return mdecl;
    }

    private emitEntityTypeDecl(tdecl: EntityTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
        return this.emitStdTypeDeclHelper(tdecl, rcvr, tdecl.fields, instantiation, "StdEntity", true);
    }

    private emitOptionTypeDecl(tdecl: OptionTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "Option");
    }

    private emitResultTypeDecl(tdecl: ResultTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "Result");
    }

    private emitAPIResultTypeDecl(tdecl: APIResultTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, "APIResult");
    }

    private emitConceptTypeDecl(tdecl: ConceptTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
        return this.emitStdTypeDeclHelper(tdecl, rcvr, tdecl.fields, instantiation, "StdConcept", false);
    }

    private emitDatatypeMemberEntityTypeDecl(tdecl: DatatypeMemberEntityTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
        return this.emitStdTypeDeclHelper(tdecl, rcvr, tdecl.fields, instantiation, "StdEntity", true);
    }

    private emitDatatypeTypeDecl(tdecl: DatatypeTypeDecl, instantiation: TypeInstantiationInfo): any {
        const rcvr = BSQONTypeInfoEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
        return this.emitStdTypeDeclHelper(tdecl, rcvr, tdecl.fields, instantiation, "StdConcept", false);
    }

    private emitTypes(tdecl: AbstractNominalTypeDecl[], asminstantiation: NamespaceInstantiationInfo): any[] {
        let alldecls: any[] = [];
        
        for(let i = 0; i < tdecl.length; ++i) {
            const tt = tdecl[i];
            const iinsts = asminstantiation.typebinds.get(tt.name);
            if(iinsts === undefined) {
                continue;
            }

            for(let j = 0; j < iinsts.length; ++j) {
                const instantiation = iinsts[j];

                if(tt instanceof EnumTypeDecl) {
                    alldecls.push(this.emitEnumTypeDecl(tt));
                }
                else if(tt instanceof TypedeclTypeDecl) {
                    alldecls.push(this.emitTypedeclTypeDecl(tt));
                }
                else if(tt instanceof PrimitiveEntityTypeDecl) {
                    alldecls.push(this.emitPrimitiveEntityTypeDecl(tt, instantiation));
                }
                else if(tt instanceof OkTypeDecl) {
                    alldecls.push(this.emitOkTypeDecl(tt, instantiation));
                }
                else if(tt instanceof FailTypeDecl) {
                    alldecls.push(this.emitFailTypeDecl(tt, instantiation));
                }
                else if(tt instanceof APIRejectedTypeDecl) {
                    alldecls.push(this.emitAPIRejectedTypeDecl(tt, instantiation));
                }
                else if(tt instanceof APIFailedTypeDecl) {
                    alldecls.push(this.emitAPIFailedTypeDecl(tt, instantiation));
                }
                else if(tt instanceof APIErrorTypeDecl) {
                    alldecls.push(this.emitAPIErrorTypeDecl(tt, instantiation));
                }
                else if(tt instanceof APISuccessTypeDecl) {
                    alldecls.push(this.emitAPISuccessTypeDecl(tt, instantiation));
                }
                else if(tt instanceof SomeTypeDecl) {
                    alldecls.push(this.emitSomeTypeDecl(tt, instantiation));
                }
                else if(tt instanceof MapEntryTypeDecl) {
                    alldecls.push(this.emitMapEntryTypeDecl(tt, instantiation));
                }
                else if(tt instanceof ListTypeDecl) {
                    alldecls.push(this.emitListTypeDecl(tt, instantiation));
                }
                else if(tt instanceof StackTypeDecl) {
                    alldecls.push(this.emitStackTypeDecl(tt, instantiation));
                }
                else if(tt instanceof QueueTypeDecl) {
                    alldecls.push(this.emitQueueTypeDecl(tt, instantiation));
                }
                else if(tt instanceof SetTypeDecl) {
                    alldecls.push(this.emitSetTypeDecl(tt, instantiation));
                }
                else if(tt instanceof MapTypeDecl) {
                    alldecls.push(this.emitMapTypeDecl(tt, instantiation));
                }
                else if(tt instanceof EventListTypeDecl) {
                    ; //no-op for parsing as we don't emit these
                }
                else if(tt instanceof EntityTypeDecl) {
                    alldecls.push(this.emitEntityTypeDecl(tt, instantiation));
                }
                else if(tt instanceof OptionTypeDecl) {
                    alldecls.push(this.emitOptionTypeDecl(tt, instantiation));
                }
                else if(tt instanceof ResultTypeDecl) {
                    alldecls.push(this.emitResultTypeDecl(tt, instantiation));
                }
                else if(tt instanceof APIResultTypeDecl) {
                    alldecls.push(this.emitAPIResultTypeDecl(tt, instantiation));
                }
                else if(tt instanceof ConceptTypeDecl) {
                    alldecls.push(this.emitConceptTypeDecl(tt, instantiation));
                }
                else if(tt instanceof DatatypeMemberEntityTypeDecl) {
                    alldecls.push(this.emitDatatypeMemberEntityTypeDecl(tt, instantiation));
                }
                else if(tt instanceof DatatypeTypeDecl) {
                    alldecls.push(this.emitDatatypeTypeDecl(tt, instantiation));
                }
                else {
                    assert(false, "Unknown type decl kind");
                }
            }
        }

        return alldecls;
    }

    private emitNamespace(nsdecl: NamespaceDeclaration, asminstantiation: NamespaceInstantiationInfo): {ns: any, types: any[]} {
        let decl: any = {};

        decl.istoplevel = nsdecl.isTopNamespace;

        decl.imports = nsdecl.usings.map((usd) => [usd.fromns, usd.asns || usd.fromns]);
        decl.ns = nsdecl.name;

        decl.subns = nsdecl.subns.map((snd) => [snd.name, snd.fullnamespace.emit()]);
        
        const tdecls = this.emitTypes(nsdecl.typedecls, asminstantiation);
        decl.types = tdecls.map((td) => [td.name, td.tkey]);
        
        //
        //TODO: later something with APIS too!
        //
        
        return {ns: decl, types: tdecls};
    }

    private emitElistInfo(): any[] {
        assert(false, "TODO: handle EList type info in assembly instantiations");
    }

    static emitAssembly(assembly: Assembly, asminstantiation: NamespaceInstantiationInfo[], includeregexinfo: boolean): any {
        let decl: any = {};

        const nscore = asminstantiation.find((ai) => ai.ns.ns.join("::") === "Core") as NamespaceInstantiationInfo;
        const emitter = new BSQONTypeInfoEmitter(assembly, nscore);

        decl.namespaces = [];
        decl.typerefs = [];
        let nsworklist: NamespaceDeclaration[] = [...assembly.toplevelNamespaces];
        while(nsworklist.length !== 0) {
            const nsdecl = nsworklist.pop() as NamespaceDeclaration;
            const nsii = asminstantiation.find((ai) => ai.ns.emit() === nsdecl.fullnamespace.emit());
            
            if(nsii !== undefined) {
                const nsemit = emitter.emitNamespace(nsdecl, nsii);

                decl.namespaces.push(nsemit.ns);
                decl.typerefs.push(...nsemit.types);
                if(nsii.elists.size !== 0) {
                    decl.typerefs.push(...emitter.emitElistInfo());
                }

                nsworklist.push(...nsdecl.subns);
            }
        }
        
        //
        //TODO: Recursive Sets here!!!
        //

        if(includeregexinfo) {
            decl.resystem = assembly.toplevelNamespaces.flatMap((ns) => assembly.loadConstantsAndValidatorREs(ns));
        }

        return decl;
    }
}

export {
    BSQONTypeInfoEmitter
};
