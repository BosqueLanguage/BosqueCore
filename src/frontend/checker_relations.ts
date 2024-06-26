import assert from "node:assert";

import { AutoTypeSignature, EListTypeSignature, ErrorTypeSignature, FullyQualifiedNamespace, LambdaParameterSignature, LambdaTypeSignature, NominalTypeSignature, NoneableTypeSignature, StringTemplateTypeSignature, TemplateConstraintScope, TemplateNameMapper, TemplateTypeSignature, TypeSignature, VoidTypeSignature } from "./type.js";
import { AbstractConceptTypeDecl, AbstractEntityTypeDecl, AbstractNominalTypeDecl, AdditionalTypeDeclTag, Assembly, ConceptTypeDecl, ConstMemberDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, EntityTypeDecl, EnumTypeDecl, ErrTypeDecl, CRegexValidatorTypeDecl, InternalEntityTypeDecl, MemberFieldDecl, MethodDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, OkTypeDecl, OptionTypeDecl, PathValidatorTypeDecl, PrimitiveEntityTypeDecl, RegexValidatorTypeDecl, ResultTypeDecl, SomethingTypeDecl, TaskDecl, TemplateTermDeclExtraTag, TypeFunctionDecl, TypedeclTypeDecl, PrimitiveConceptTypeDecl } from "./assembly.js";
import { SourceInfo } from "./build_decls.js";
import { EListStyleTypeInferContext, SimpleTypeInferContext, TypeInferContext } from "./checker_environment.js";

class TypeLookupInfo {
    readonly tsig: NominalTypeSignature;
    readonly mapping: TemplateNameMapper;

    constructor(tsig: NominalTypeSignature, mapping: TemplateNameMapper) {
        this.tsig = tsig;
        this.mapping = mapping;
    }
}

class MemberLookupInfo<T> {
    readonly typeinfo: TypeLookupInfo;
    readonly member: T;

    constructor(typeinfo: TypeLookupInfo, member: T) {
        this.typeinfo = typeinfo;
        this.member = member;
    }
}

class TypeCheckerRelations {
    readonly assembly: Assembly;
    readonly wellknowntypes: Map<string, TypeSignature>;

    readonly memoizedNormalize: Map<string, TypeSignature> = new Map<string, TypeSignature>();
    readonly memoizedTypeEqualRelation: Map<string, boolean> = new Map<string, boolean>();
    readonly memoizedTypeSubtypeRelation: Map<string, boolean> = new Map<string, boolean>();

    constructor(assembly: Assembly, wellknowntypes: Map<string, TypeSignature>) {
        this.assembly = assembly;
        this.wellknowntypes = wellknowntypes;
    }

    resolveSpecialProvidesDecls(t: NominalTypeSignature, tconstrain: TemplateConstraintScope): TypeSignature[] {
        if(t.decl instanceof EnumTypeDecl) {
            return [this.wellknowntypes.get("KeyType") as TypeSignature, this.wellknowntypes.get("Some") as TypeSignature];
        }
        else if(t.decl instanceof RegexValidatorTypeDecl) {
            return [this.wellknowntypes.get("RegexValidator") as TypeSignature];
        }
        else if(t.decl instanceof CRegexValidatorTypeDecl) {
            return [this.wellknowntypes.get("CRegexValidator") as TypeSignature];
        }
        else if(t.decl instanceof PathValidatorTypeDecl) {
            return [this.wellknowntypes.get("PathValidator") as TypeSignature];
        }
        else if(t.decl instanceof DatatypeMemberEntityTypeDecl) {
            return [new NominalTypeSignature(t.sinfo, t.decl.parentTypeDecl, t.alltermargs)];
        }
        else if(t.decl instanceof TypedeclTypeDecl) {
            let provides: TypeSignature[] = [this.wellknowntypes.get("Some") as TypeSignature];
            const btype = this.getTypeDeclBasePrimitiveType(t, tconstrain);
            if(btype !== undefined) {
                if(this.isSubtypeOf(btype, this.wellknowntypes.get("KeyType") as TypeSignature, tconstrain)) {
                    provides.push(this.wellknowntypes.get("KeyType") as TypeSignature);
                }
                if(this.isSubtypeOf(btype, this.wellknowntypes.get("Numeric") as TypeSignature, tconstrain)) {
                    provides.push(this.wellknowntypes.get("Numeric") as TypeSignature);
                }
                if(this.isSubtypeOf(btype, this.wellknowntypes.get("Comparable") as TypeSignature, tconstrain)) {
                    provides.push(this.wellknowntypes.get("Comparable") as TypeSignature);
                }
                if(this.isSubtypeOf(btype, this.wellknowntypes.get("LinearArithmetic") as TypeSignature, tconstrain)) {
                    provides.push(this.wellknowntypes.get("LinearArithmetic") as TypeSignature);
                }
            }
            return provides;
        }
        else {
            return [];
        }
    }

    //get all of the actual concepts + template mappings that are provided by a type
    resolveAllProvidesDecls(provides: TypeSignature[]): TypeLookupInfo[] {
        const pdecls: TypeLookupInfo[] = [];
        for(let i = 0; i < provides.length; ++i) {
            const ptype = provides[i];
            if(!(ptype instanceof NominalTypeSignature) || !(ptype.decl instanceof AbstractConceptTypeDecl)) {
                continue;
            }

            if(ptype.decl.terms.length !== ptype.alltermargs.length) {
                continue;
            }

            let pmap = new Map<string, TypeSignature>();
            for(let j = 0; j < ptype.decl.terms.length; ++j) {
                pmap.set(ptype.decl.terms[j].name, ptype.alltermargs[j]);
            }

            pdecls.push(new TypeLookupInfo(ptype, TemplateNameMapper.createInitialMapping(pmap)));
        }

        return pdecls;
    }

    private normalizeTypeSignatureHelper(tsig: TypeSignature, tconstrain: TemplateConstraintScope, toptemplate: boolean, alltemplates: boolean): TypeSignature {
        const memoval = this.memoizedNormalize.get(tsig.tkeystr);
        if(memoval !== undefined) {
            return memoval;
        }

        let res: TypeSignature;
        if(tsig instanceof ErrorTypeSignature || tsig instanceof VoidTypeSignature || tsig instanceof AutoTypeSignature) {
            res = tsig;
        }
        else if(tsig instanceof TemplateTypeSignature) {
            const rr = toptemplate ? tconstrain.resolveConstraint(tsig.name) : undefined;
            res = rr === undefined ? tsig : rr.tconstraint;
        }
        else if(tsig instanceof NominalTypeSignature) {
            res = new NominalTypeSignature(tsig.sinfo, tsig.decl, tsig.alltermargs.map((tt) => this.normalizeTypeSignatureHelper(tt, tconstrain, alltemplates, alltemplates)));
        }
        else if(tsig instanceof EListTypeSignature) {
            res = new EListTypeSignature(tsig.sinfo, tsig.entries.map((tt) => this.normalizeTypeSignatureHelper(tt, tconstrain, alltemplates, alltemplates)));
        }
        else if(tsig instanceof StringTemplateTypeSignature) {
            res = new StringTemplateTypeSignature(tsig.sinfo, tsig.kind, tsig.argtypes.map((ts) => this.normalizeTypeSignatureHelper(ts, tconstrain, alltemplates, alltemplates)));
        }
        else if(tsig instanceof LambdaTypeSignature) {
            const rparams = tsig.params.map((pp) => {
                return new LambdaParameterSignature(this.normalizeTypeSignatureHelper(pp.type, tconstrain, alltemplates, alltemplates), pp.isRefParam, pp.isRestParam);
            });

            res = new LambdaTypeSignature(tsig.sinfo, tsig.recursive, tsig.name, rparams, this.normalizeTypeSignatureHelper(tsig.resultType, tconstrain, alltemplates, alltemplates));
        }
        else if(tsig instanceof NoneableTypeSignature) {
            const ots = this.normalizeTypeSignatureHelper(tsig.type, tconstrain, alltemplates, alltemplates);
            if(ots instanceof NoneableTypeSignature) {
                res = ots;
            }
            else {
                if(ots instanceof PrimitiveEntityTypeDecl && ots.name === "None") {
                    res = this.wellknowntypes.get("None") as TypeSignature;
                }
                else if(ots instanceof PrimitiveConceptTypeDecl && ots.name === "Some") {
                    res = this.wellknowntypes.get("Any") as TypeSignature;
                }
                else {
                    res = new NoneableTypeSignature(tsig.sinfo, ots);
                }
            }
        }
        else {
            assert(false, "Unknown type signature");
        }

        this.memoizedNormalize.set(tsig.tkeystr, res);
        return res;
    }

    normalize(tsig: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        return this.normalizeTypeSignatureHelper(tsig, tconstrain, false, false);
    }

    normalizeAndTemplateInstantiate(tsig: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        return this.normalizeTypeSignatureHelper(tsig, tconstrain, true, true);
    }

    private areSameTypeSignatureLists(tl1: TypeSignature[], tl2: TypeSignature[], tconstrain: TemplateConstraintScope): boolean {
        if(tl1.length !== tl2.length) {
            return false;
        }

        for(let i = 0; i < tl1.length; ++i) {
            if(!this.areSameTypes(tl1[i], tl2[i], tconstrain)) {
                return false;
            }
        }

        return true;
    }

    private areSameFunctionParamLists(tl1: LambdaParameterSignature[], tl2: LambdaParameterSignature[], tconstrain: TemplateConstraintScope): boolean {
        if(tl1.length !== tl2.length) {
            return false;
        }

        for(let i = 0; i < tl1.length; ++i) {
            if(tl1[i].isRefParam !== tl2[i].isRefParam || tl1[i].isRestParam !== tl2[i].isRestParam) {
                return false;
            }
            
            if(!this.areSameTypes(tl1[i].type, tl2[i].type, tconstrain)) {
                return false;
            }
        }

        return true;
    }

    //Check if t1 and t2 are the same type -- template types are not expanded in this check
    areSameTypes(t1: TypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t1 instanceof ErrorTypeSignature) && !(t2 instanceof ErrorTypeSignature), "Checking type same on errors");
        assert(!(t1 instanceof AutoTypeSignature) && !(t2 instanceof AutoTypeSignature), "Checking type same on auto");

        const kstr = `(${t1.tkeystr} <> ${t2.tkeystr})`;
        const memoval = this.memoizedTypeEqualRelation.get(kstr);
        if(memoval !== undefined) {
            return memoval;
        }

        const nt1 = this.normalize(t1, tconstrain);
        const nt2 = this.normalize(t2, tconstrain);

        let res = false
        if(nt1 instanceof VoidTypeSignature && nt2 instanceof VoidTypeSignature) {
            res = true;
        }
        else if(nt1 instanceof TemplateTypeSignature && nt2 instanceof TemplateTypeSignature) {
            res = (nt1.name === nt2.name);
        }
        else if(nt1 instanceof NominalTypeSignature && nt2 instanceof NominalTypeSignature) {
            res = (nt1.decl === nt2.decl) && this.areSameTypeSignatureLists(nt1.alltermargs, nt2.alltermargs, tconstrain);
        }
        else if(nt1 instanceof EListTypeSignature && nt2 instanceof EListTypeSignature) {
            res = this.areSameTypeSignatureLists(nt1.entries, nt2.entries, tconstrain);
        }
        else if(nt1 instanceof StringTemplateTypeSignature && nt2 instanceof StringTemplateTypeSignature) {
            res = (nt1.kind === nt2.kind) && this.areSameTypeSignatureLists(nt1.argtypes, nt2.argtypes, tconstrain);
        }
        else if(nt1 instanceof LambdaTypeSignature && nt2 instanceof LambdaTypeSignature) {
            if(nt1.recursive !== nt2.recursive || nt1.name !== nt2.name) {
                res = false;
            }
            else {
                const okargs = this.areSameFunctionParamLists(nt1.params, nt2.params, tconstrain);
                const okres = this.areSameTypes(nt1.resultType, nt2.resultType, tconstrain);

                res = okargs && okres;
            }
        }
        else if(nt1 instanceof NoneableTypeSignature && nt2 instanceof NoneableTypeSignature) {
            res = this.areSameTypes(nt1.type, nt2.type, tconstrain);
        }
        else {
            ; //for all other cases res stays false
        }

        this.memoizedTypeEqualRelation.set(kstr, res);
        return res;
    }

    private templateIsSubtypeOf(t1: TemplateTypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        const cons = tconstrain.resolveConstraint(t1.name);
        return cons !== undefined && this.isSubtypeOf(cons.tconstraint, t2, tconstrain);
    }

    private nominalIsSubtypeOf(t1: NominalTypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        const providesinfo = this.resolveAllProvidesDecls(t1.decl.provides);

        return providesinfo.map((pp) => pp.tsig.remapTemplateBindings(pp.mapping)).some((t) => this.isSubtypeOf(t, t2, tconstrain));
    }

    private stringTemplateIsSubtypeOf(t1: StringTemplateTypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        if(t2 instanceof NominalTypeSignature) {
            return this.isSubtypeOf(t1.kind === "utf8" ? this.wellknowntypes.get("TemplateString") as NominalTypeSignature : this.wellknowntypes.get("TemplateCString") as NominalTypeSignature, t2, tconstrain);
        }
        else if(t2 instanceof NoneableTypeSignature) {
            return this.isSubtypeOf(t1, t2.type, tconstrain);
        }
        else {
            return false;
        }
    }

    //Check is t1 is a subtype of t2 -- template types are expanded when needed in this check
    isSubtypeOf(t1: TypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t1 instanceof ErrorTypeSignature) && !(t2 instanceof ErrorTypeSignature), "Checking subtypes on errors");
        assert(!(t1 instanceof AutoTypeSignature) && !(t2 instanceof AutoTypeSignature), "Checking subtypes on auto");
        
        const kstr = `(${t1.tkeystr} <: ${t2.tkeystr})`;
        const memoval = this.memoizedTypeSubtypeRelation.get(kstr);
        if(memoval !== undefined) {
            return memoval;
        }

        const nt1 = this.normalize(t1, tconstrain);
        const nt2 = this.normalize(t2, tconstrain);

        let res = false;
        if(nt2.tkeystr === "Any") {
            res = true;
        }
        else if(this.areSameTypes(nt1, nt2, tconstrain)) {
            res = true;
        }
        else {
            if(nt1 instanceof TemplateTypeSignature) {
                res = this.templateIsSubtypeOf(nt1, nt2, tconstrain);
            }
            else if(nt1 instanceof NominalTypeSignature) {
                res = this.nominalIsSubtypeOf(nt1, nt2, tconstrain);
            }
            else if (nt1 instanceof StringTemplateTypeSignature) {
                res = this.stringTemplateIsSubtypeOf(nt1, nt2, tconstrain);
            }
            else if(nt1 instanceof NoneableTypeSignature) {
                res = this.isSubtypeOf(this.wellknowntypes.get("None") as TypeSignature, nt2, tconstrain) && this.isSubtypeOf(nt1.type, nt2, tconstrain);
            }
            else {
                res = false;
            }
        }

        this.memoizedTypeSubtypeRelation.set(kstr, res);
        return res;
    }

    flowTypeLUB(sinfo: SourceInfo, ns: FullyQualifiedNamespace, lubopt: TypeSignature | undefined, tl: TypeSignature[], tconstrain: TemplateConstraintScope): TypeSignature {
        if(tl.some((t) => (t instanceof ErrorTypeSignature) || (t instanceof AutoTypeSignature) || (t instanceof VoidTypeSignature) || (t instanceof LambdaTypeSignature))) {
            return new ErrorTypeSignature(sinfo, ns);
        }

        const ttl = tl.map((t) => this.normalize(t, tconstrain));

        //handle elist case
        if(ttl.some((t) => t instanceof EListTypeSignature)) {
            if(!ttl.every((t) => t instanceof EListTypeSignature)) {
                return new ErrorTypeSignature(sinfo, ns);
            }

            const elts = ttl[0];
            for(let i = 1; i < tl.length; ++i) {
                if(!this.areSameTypes(elts, tl[i], tconstrain)) {
                    return new ErrorTypeSignature(sinfo, ns);
                }
            }

            return elts;
        }

        //check for None+Some -> Any
        const hasnone = ttl.some((t) => this.isSubtypeOf(this.wellknowntypes.get("None") as TypeSignature, t, tconstrain));
        const hassome = ttl.some((t) => this.isSubtypeOf(this.wellknowntypes.get("Some") as TypeSignature, t, tconstrain));
        if(hasnone && hassome) {
            return this.wellknowntypes.get("Any") as TypeSignature;
        }

        //now we know if it has none in some form so simplify the list to non-none types
        const nttl = ttl.map((t) => (t instanceof NoneableTypeSignature) ? t.type : t).filter((t) => !(t instanceof NominalTypeSignature) || !((t.decl instanceof PrimitiveEntityTypeDecl) && t.decl.name === "None"));
        if(nttl.length === 0) {
            return this.wellknowntypes.get("None") as TypeSignature;
        }

        //eliminate duplicates
        let restypel = [nttl[0]];
        for(let i = 1; i < tl.length; ++i) {
            const ntt = nttl[i];

            const findres = restypel.findIndex((rt) => this.isSubtypeOf(ntt, rt, tconstrain));
            if(findres === -1) {
                //not a subtype of any of the existing types -- filter any types that are subtypes of ntt and then add ntt
                restypel = [...restypel.filter((rt) => !this.isSubtypeOf(rt, ntt, tconstrain)), ntt];
            }
        }
        
        const corens = this.assembly.getCoreNamespace();
        let resopt: TypeSignature | undefined = undefined; 

        //only one type left
        if(restypel.length === 1) {
            resopt = restypel[0];
        }
    
        //check for special case of Nothing+Something -> Option
        if(nttl.length === 2 && nttl.every((t) => (t instanceof NominalTypeSignature) && (t.decl instanceof InternalEntityTypeDecl))) {
            const ptl = nttl as NominalTypeSignature[];

            const hasnothing = ptl.some((t) => t.decl.name === "Nothing");
            const something = ptl.find((t) => t.decl instanceof SomethingTypeDecl);
            if(hasnothing && something !== undefined) {
                resopt = new NominalTypeSignature(sinfo, corens.typedecls.find((tdecl) => tdecl.name === "Option") as TypedeclTypeDecl, something.alltermargs);
            }

            //check for special case of Ok+Err -> Result
            const okopt = ptl.find((t) => t.decl instanceof OkTypeDecl);
            const erropt = ptl.find((t) => t.decl instanceof ErrTypeDecl);
            if(okopt && erropt && this.areSameTypeSignatureLists(okopt.alltermargs, erropt.alltermargs, tconstrain)) {
                resopt = new NominalTypeSignature(sinfo, corens.typedecls.find((tdecl) => tdecl.name === "Result") as TypedeclTypeDecl, okopt.alltermargs);
            }
        }

        if(nttl.length > 1 && nttl.every((t) => (t instanceof NominalTypeSignature) && (t.decl instanceof DatatypeMemberEntityTypeDecl))) {
            //check for complete set of datatype members
            const dptl = nttl as NominalTypeSignature[];

            const pptype = new NominalTypeSignature(dptl[0].sinfo, (dptl[0].decl as DatatypeMemberEntityTypeDecl).parentTypeDecl, dptl[0].alltermargs);
            const allsameparents = dptl.every((t) => this.isSubtypeOf(t, pptype, tconstrain));
            
            if(allsameparents) {
                resopt = pptype;
            }
        }
        
        //take these special cases and wrap non-able if needed
        if(resopt !== undefined) {
            return hasnone ? new NoneableTypeSignature(sinfo, resopt) : resopt;
        }

        //ok check for lubopt then Some then Any (with non-able if needed)
        let reslub: TypeSignature;
        if(lubopt !== undefined && restypel.every((t) => this.isSubtypeOf(t, lubopt, tconstrain))) {
            if(!hasnone) {
                reslub = lubopt;
            }
            else {
                if(this.isSubtypeOf(this.wellknowntypes.get("Some") as TypeSignature, lubopt, tconstrain)) {
                    reslub = this.wellknowntypes.get("Any") as TypeSignature;
                }
                else if(lubopt instanceof NoneableTypeSignature) {
                    reslub = lubopt;
                }
                else {
                    reslub = new NoneableTypeSignature(lubopt.sinfo, lubopt);
                }
            }
        }
        else if(restypel.every((t) => this.isSubtypeOf(t, this.wellknowntypes.get("Some") as TypeSignature, tconstrain))) {
            reslub = hasnone ? this.wellknowntypes.get("Any") as TypeSignature : this.wellknowntypes.get("Some") as TypeSignature;
        }
        else {
            reslub = this.wellknowntypes.get("Any") as TypeSignature;
        }

        return reslub;
    }

    //Check is this type is unique (i.e. a entity type or a template that is marked as unique)
    isUniqueType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        if(t instanceof NominalTypeSignature) {
            return !(t.decl instanceof AbstractConceptTypeDecl);
        }
        else if(t instanceof TemplateTypeSignature) {
            const tcs = tconstrain.resolveConstraint(t.name);
            return tcs !== undefined && tcs.extraTags.includes(TemplateTermDeclExtraTag.Unique);
        }
        else {
            return false;
        }
    }

    //Check if this type is a KeyType (e.g. a subtype of KeyType)
    isKeyType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        return this.isSubtypeOf(t, this.wellknowntypes.get("KeyType") as TypeSignature, tconstrain);
    }

    //Check if this type is unique and a numeric type of some sort (either primitive number or a typedecl of a numeric type)
    isUniqueKeyType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");
        
        return this.isUniqueType(t, tconstrain) && this.isSubtypeOf(t, this.wellknowntypes.get("KeyType") as TypeSignature, tconstrain);
    }

    //Check if this type is unique and a numeric type of some sort (either primitive number or a typedecl of a numeric type)
    isUniqueNumericType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");
        
        return this.isUniqueType(t, tconstrain) && this.isSubtypeOf(t, this.wellknowntypes.get("Numeric") as TypeSignature, tconstrain);
    }

    //Check if this type is a primitive type in Core
    isPrimitiveType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        return (t instanceof NominalTypeSignature) && t.decl instanceof PrimitiveEntityTypeDecl;
    }

    //Check if we can assign this type as the RHS of a typedecl declaration
    isTypedeclableType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        if(!(t instanceof NominalTypeSignature)) {
            return false;
        }

        if(t.decl instanceof EnumTypeDecl) {
            return true;
        }
        else if(t.decl instanceof TypedeclTypeDecl) {
            return true;
        }
        else if(t.decl instanceof InternalEntityTypeDecl) {
            return t.decl.attributes.find((attr) => attr.name === "__typedeclable") !== undefined;
        }
        else {
            return false;
        }
    }

    //Check if this type is a valid event type
    isEventDataType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        return (t instanceof NominalTypeSignature) && t.decl.etag === AdditionalTypeDeclTag.Event;
    }

    //Check if this type is a valid status
    isStatusDataType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        return (t instanceof NominalTypeSignature) && t.decl.etag === AdditionalTypeDeclTag.Status;
    }

    //Check if this type is a valid type to have as a provides type -- must be a unique CONCEPT type
    isValidProvidesType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        return (t instanceof NominalTypeSignature) && (t.decl instanceof AbstractConceptTypeDecl);
    }

    //Check if this is a valid type to have a template restriction set to
    //Currently must be a Concept or union
    //TODO: this precludes accidentally setting it to a vacuous instantiation option but we will need to adjust if/when we allow for template literals
    isValidTemplateRestrictionType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        if(t instanceof UnionTypeSignature) {
            return true;
        }
        else if(t instanceof NoneableTypeSignature) {
            return true;
        }
        else if(t instanceof NominalTypeSignature) {
            return ttnorm.resolvedDeclaration instanceof AbstractConceptTypeDecl;
        }
        else {
            return false;
        }
    }

    //Check if this type is a typedecl of some sort
    isTypeDeclType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        const tnorm = this.normalizeTypeSignature(t, tconstrain);
        return tnorm instanceof TypedeclTypeDecl;
    }

    private refineNominal(src: NominalTypeSignature, refine: TypeSignature, tconstrain: TemplateConstraintScope): { overlap: TypeSignature | undefined, remain: TypeSignature | undefined } {
        const nsrc = this.normalizeTypeSignature(src, tconstrain);

        //If this is an alias to some non-nominal thing then we don't refine it and just leave it as is in the developers original form
        if(!(nsrc instanceof NominalTypeSignature)) {
            return { overlap: refine, remain: src };
        }

        const srcdecl = nsrc.resolvedDeclaration as AbstractNominalTypeDecl;
        if(srcdecl instanceof AbstractEntityTypeDecl) {
            if(this.isSubtypeOf(nsrc, refine, tconstrain)) {
                return { overlap: src, remain: undefined };
            }
            else {
                return { overlap: undefined, remain: src };
            }
        }
        else if(this.areSameTypes(nsrc, this.wellknowntypes.get("Any") as TypeSignature, tconstrain) && this.areSameTypes(refine, this.wellknowntypes.get("None") as TypeSignature, tconstrain)) {
            return { overlap: this.wellknowntypes.get("None"), remain: this.wellknowntypes.get("Some") };
        }
        else if(this.areSameTypes(nsrc, this.wellknowntypes.get("Any") as TypeSignature, tconstrain) && this.areSameTypes(refine, this.wellknowntypes.get("Some") as TypeSignature, tconstrain)) {
            return { overlap: this.wellknowntypes.get("Some"), remain: this.wellknowntypes.get("None") };
        }
        else if(srcdecl instanceof OptionTypeDecl && this.areSameTypes(refine, this.wellknowntypes.get("Nothing") as TypeSignature, tconstrain)) {
            return {overlap: refine, remain: this.getSomethingTypeForOptionT(nsrc, tconstrain)};
        }
        else if(srcdecl instanceof OptionTypeDecl && this.areSameTypes(refine, this.getSomethingTypeForOptionT(nsrc, tconstrain), tconstrain)) {
            return {overlap: refine, remain: this.wellknowntypes.get("Nothing") as TypeSignature};
        }
        else if(srcdecl instanceof ResultTypeDecl && this.areSameTypes(refine, this.getErrorTypeForResultTE(nsrc, tconstrain), tconstrain)) {
            return {overlap: refine, remain: this.getOkTypeForResultTE(nsrc, tconstrain)};
        }
        else if(srcdecl instanceof ResultTypeDecl && this.areSameTypes(refine, this.getErrorTypeForResultTE(nsrc, tconstrain), tconstrain)) {
            return {overlap: refine, remain: this.getOkTypeForResultTE(nsrc, tconstrain)};
        }
        else if(srcdecl instanceof DatatypeTypeDecl) {
            const opts = srcdecl.associatedMemberEntityDecls.map((mem) => {
                const tmem = new NominalTypeSignature(mem.sinfo, nsrc.ns, [{ tname: mem.name, terms: nsrc.tscope[0].terms}], undefined, mem);
                return this.refineNominal(tmem, refine, tconstrain)
            });

            const ovlp = opts.map((opt) => opt.overlap).filter((opt) => opt !== undefined);
            const rmn = opts.map((opt) => opt.remain).filter((opt) => opt !== undefined);

            let ovlres: TypeSignature | undefined = undefined;
            if(ovlp.length !== 0) {
                ovlres = ovlp[0];
                for(let i = 1; i < ovlp.length; ++i) {
                    ovlres = this.joinTypes(ovlres as TypeSignature, ovlp[i] as TypeSignature, tconstrain);
                }
            }

            let rmnres: TypeSignature | undefined = undefined;
            if(rmn.length !== 0) {
                rmnres = rmn[0];
                for(let i = 1; i < rmn.length; ++i) {
                    rmnres = this.joinTypes(rmnres as TypeSignature, rmn[i] as TypeSignature, tconstrain);
                }
            }

            return { overlap: ovlres, remain: rmnres };
        }
        else {
            return { overlap: refine, remain: src };
        }
    }

    private refineStringTemplate(src: StringTemplateTypeSignature, refine: TypeSignature, tconstrain: TemplateConstraintScope): { overlap: TypeSignature | undefined, remain: TypeSignature | undefined } {
        if(this.isSubtypeOf(src, refine, tconstrain)) {
            return { overlap: src, remain: undefined };
        }
        else {
            return { overlap: undefined, remain: src };
        }
    }

    private refineNoneable(src: NoneableTypeSignature, refine: TypeSignature, tconstrain: TemplateConstraintScope): { overlap: TypeSignature | undefined, remain: TypeSignature | undefined } {
        const refbase = this.refineType(src.type, refine, tconstrain);

        if(!this.includesNoneType(refine, tconstrain)) {
            return {overlap: refbase.overlap, remain: refbase.remain !== undefined ? new NoneableTypeSignature(src.sinfo, refbase.remain) : this.wellknowntypes.get("None") as TypeSignature};
        }
        else {
            return {overlap: refbase.overlap !== undefined ? new NoneableTypeSignature(src.sinfo, refbase.overlap) : this.wellknowntypes.get("None") as TypeSignature, remain: refbase.remain};
        }
    }

    private refineUnion(src: UnionTypeSignature, refine: TypeSignature, tconstrain: TemplateConstraintScope): { overlap: TypeSignature | undefined, remain: TypeSignature | undefined } {
        const lref = this.refineType(src.ltype, refine, tconstrain);
        const rref = this.refineType(src.rtype, refine, tconstrain);

        let ovl: TypeSignature | undefined;
        if(lref.overlap !== undefined && rref.overlap !== undefined) {
            ovl = new UnionTypeSignature(src.sinfo, lref.overlap, rref.overlap);
        }
        else if(lref.overlap !== undefined) {
            ovl = lref.overlap;
        }
        else if(rref.overlap !== undefined) {
            ovl = rref.overlap;
        }
        else {
            ovl = undefined;
        }

        let rmn: TypeSignature | undefined;
        if(lref.remain !== undefined && rref.remain !== undefined) {
            rmn = new UnionTypeSignature(src.sinfo, lref.remain, rref.remain);
        }
        else if(lref.remain !== undefined) {
            rmn = lref.remain;
        }
        else if(rref.remain !== undefined) {
            rmn = rref.remain;
        }
        else {
            rmn = undefined;
        }

        return { overlap: ovl, remain: rmn };
    }

    refineType(src: TypeSignature, refine: TypeSignature, tconstrain: TemplateConstraintScope): { overlap: TypeSignature | undefined, remain: TypeSignature | undefined } {
        //If src is an error then just return error for both
        if(src instanceof ErrorTypeSignature) {
            return { overlap: src, remain: src };
        }

        //If the refinement is indeterminate (an error) then just nop and return src as the option for both
        if(refine instanceof ErrorTypeSignature) {
            return { overlap: src, remain: src };
        }

        if(this.isSubtypeOf(src, refine, tconstrain)) {
            return { overlap: src, remain: undefined };
        }

        //now do the actual cases
        if(src instanceof NominalTypeSignature) {
            return this.refineNominal(src, refine, tconstrain);
        }
        else if(src instanceof TupleTypeSignature) {
            return this.refineTuple(src, refine, tconstrain);
        }
        else if(src instanceof RecordTypeSignature) {
            return this.refineRecord(src, refine, tconstrain);
        }
        else if(src instanceof StringTemplateTypeSignature) {
            return this.refineStringTemplate(src, refine, tconstrain);
        }
        else if(src instanceof NoneableTypeSignature) {
            return this.refineNoneable(src, refine, tconstrain);
        }
        else if(src instanceof UnionTypeSignature) {
            return this.refineUnion(src, refine, tconstrain);
        }
        else {
            return { overlap: refine, remain: src };
        }
    }

    //Get the assigned value type of a typedecl (resolving as needed)
    getTypeDeclValueType(t: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature | undefined {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        const tnorm = this.normalizeTypeSignature(t, tconstrain);
        if(!(tnorm instanceof NominalTypeSignature)) {
            return undefined;
        }

        const tdecl = tnorm.resolvedDeclaration as AbstractNominalTypeDecl;
        if(tdecl instanceof TypedeclTypeDecl) {
            const remapper = TypeCheckerRelations.computeNameMapperFromDirectTypeSignatureInfo(tnorm);
            return tdecl.valuetype.remapTemplateBindings(remapper);
        }
        else {
            return undefined;
        }
    }

    private getTypeDeclBasePrimitiveType_Helper(t: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature | undefined {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        const tnorm = this.normalizeTypeSignature(t, tconstrain);
        if(!(tnorm instanceof NominalTypeSignature)) {
            return undefined;
        }

        const tdecl = tnorm.resolvedDeclaration as AbstractNominalTypeDecl;
        if(tdecl instanceof EnumTypeDecl) {
            return tnorm;
        }
        else if(tdecl instanceof TypedeclTypeDecl) {
            const remapper = TypeCheckerRelations.computeNameMapperFromDirectTypeSignatureInfo(tnorm);
            return this.getTypeDeclBasePrimitiveType(tdecl.valuetype.remapTemplateBindings(remapper), tconstrain);
        }
        else if(tdecl instanceof InternalEntityTypeDecl) {
            const isdeclable = tdecl.attributes.find((attr) => attr.name === "__typedeclable") !== undefined;
            return isdeclable ? tnorm : undefined;
        }
        else {
            return undefined;
        }
    }

    //Get the base primitive type of a typedecl (resolving through typedecls and aliases as needed)
    getTypeDeclBasePrimitiveType(t: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature | undefined {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        const tnorm = this.normalizeTypeSignature(t, tconstrain);
        if(!(tnorm instanceof NominalTypeSignature)) {
            return undefined;
        }

        const tdecl = tnorm.resolvedDeclaration as AbstractNominalTypeDecl;
        if(tdecl instanceof TypedeclTypeDecl) {
            return this.getTypeDeclBasePrimitiveType_Helper(t, tconstrain);
        }
        else {
            return undefined;
        }
    }

    //If possible resolve this type as an elist type
    tryResolveAsEListType(vtype: TypeSignature, tconstrain: TemplateConstraintScope): EListTypeSignature | undefined {
        const tnorm = this.normalizeTypeSignature(vtype, tconstrain);
        return (tnorm instanceof EListTypeSignature) ? tnorm : undefined;
    }

    getStringOfType(vtype: TypeSignature): TypeSignature {
        const corens = this.assembly.getCoreNamespace();
        const stringofdecl = corens.typedecls.find((tdecl) => tdecl.name === "StringOf");

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "StringOf", terms: [vtype]}], undefined, stringofdecl);
    }

    getCStringOfType(vtype: TypeSignature): TypeSignature {
        const corens = this.assembly.getCoreNamespace();
        const stringofdecl = corens.typedecls.find((tdecl) => tdecl.name === "CStringOf");

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "CStringOf", terms: [vtype]}], undefined, stringofdecl);
    }

    getEventListOf(vtype: TypeSignature): TypeSignature {
        const corens = this.assembly.getCoreNamespace();
        const stringofdecl = corens.typedecls.find((tdecl) => tdecl.name === "EventList");

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "EventList", terms: [vtype]}], undefined, stringofdecl);
    }

    //given a type that is of the form Something<T> return the corresponding type Option<T>
    private getOptionTypeForSomethingT(vtype: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        const mapper = TypeCheckerRelations.computeNameMapperFromDirectTypeSignatureInfo(vtype as NominalTypeSignature);
        const ttype = mapper.resolveTemplateMapping(new TemplateTypeSignature(vtype.sinfo, "T"));

        const corens = this.assembly.getCoreNamespace();
        const optiondecl = corens.typedecls.find((tdecl) => tdecl.name === "Option");

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "Option", terms: [ttype]}], undefined, optiondecl);
    }

    //given a type that is of the form Option<T> return the corresponding type Something<T>
    private getSomethingTypeForOptionT(vtype: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        const mapper = TypeCheckerRelations.computeNameMapperFromDirectTypeSignatureInfo(vtype as NominalTypeSignature);
        const ttype = mapper.resolveTemplateMapping(new TemplateTypeSignature(vtype.sinfo, "T"));

        const corens = this.assembly.getCoreNamespace();
        const somethingdecl = corens.typedecls.find((tdecl) => tdecl.name === "Something");

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "Something", terms: [ttype]}], undefined, somethingdecl);
    }

    private getResultTypeForErrorTE(vtype: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        const mapper = TypeCheckerRelations.computeNameMapperFromDirectTypeSignatureInfo(vtype as NominalTypeSignature);
        const ttype = mapper.resolveTemplateMapping(new TemplateTypeSignature(vtype.sinfo, "T"));
        const etype = mapper.resolveTemplateMapping(new TemplateTypeSignature(vtype.sinfo, "E"));

        const corens = this.assembly.getCoreNamespace();
        const resultdecl = corens.typedecls.find((tdecl) => tdecl.name === "Result");

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "Result", terms: [ttype, etype]}], undefined, resultdecl);
    }

    private getResultTypeForOkTE(vtype: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        const mapper = TypeCheckerRelations.computeNameMapperFromDirectTypeSignatureInfo(vtype as NominalTypeSignature);
        const ttype = mapper.resolveTemplateMapping(new TemplateTypeSignature(vtype.sinfo, "T"));
        const etype = mapper.resolveTemplateMapping(new TemplateTypeSignature(vtype.sinfo, "E"));

        const corens = this.assembly.getCoreNamespace();
        const resultdecl = corens.typedecls.find((tdecl) => tdecl.name === "Result");

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "Result", terms: [ttype, etype]}], undefined, resultdecl);
    }

    private getErrorTypeForResultTE(vtype: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        const mapper = TypeCheckerRelations.computeNameMapperFromDirectTypeSignatureInfo(vtype as NominalTypeSignature);
        const ttype = mapper.resolveTemplateMapping(new TemplateTypeSignature(vtype.sinfo, "T"));
        const etype = mapper.resolveTemplateMapping(new TemplateTypeSignature(vtype.sinfo, "E"));

        const corens = this.assembly.getCoreNamespace();
        const errdecl = (corens.typedecls.find((tdecl) => tdecl.name === "Result") as ResultTypeDecl).nestedEntityDecls.find((tdecl) => tdecl.name === "Err") as ErrTypeDecl;

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "Result", terms: [ttype, etype]}, {tname: "Err", terms: []}], undefined, errdecl);
    }

    private getOkTypeForResultTE(vtype: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        const mapper = TypeCheckerRelations.computeNameMapperFromDirectTypeSignatureInfo(vtype as NominalTypeSignature);
        const ttype = mapper.resolveTemplateMapping(new TemplateTypeSignature(vtype.sinfo, "T"));
        const etype = mapper.resolveTemplateMapping(new TemplateTypeSignature(vtype.sinfo, "E"));

        const corens = this.assembly.getCoreNamespace();
        const okdecl = (corens.typedecls.find((tdecl) => tdecl.name === "Result") as ResultTypeDecl).nestedEntityDecls.find((tdecl) => tdecl.name === "Ok") as OkTypeDecl;

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "Result", terms: [ttype, etype]}, {tname: "Ok", terms: []}], undefined, okdecl);
    }

    getNominalTypeForDecl(enclns: NamespaceDeclaration, tdecl: AbstractNominalTypeDecl): TypeSignature {
        const tterms = tdecl.terms.map((tterm) => new TemplateTypeSignature(tdecl.sinfo, tterm.name));
        return new NominalTypeSignature(tdecl.sinfo, enclns.fullnamespace.ns, [{tname: tdecl.name, terms: tterms}], undefined, tdecl);
    }

    getNominalTypeForNestedDecl(enclns: NamespaceDeclaration, encldecl: AbstractNominalTypeDecl, tdecl: AbstractNominalTypeDecl): TypeSignature {
        const tterms = encldecl.terms.map((tterm) => new TemplateTypeSignature(tdecl.sinfo, tterm.name));

        return new NominalTypeSignature(tdecl.sinfo, enclns.fullnamespace.ns, [{tname: encldecl.name, terms: tterms}, {tname: tdecl.name, terms: []}], undefined, tdecl);
    }

    resolveNamespaceDecl(ns: string[]): NamespaceDeclaration | undefined {
        let curns = this.assembly.getToplevelNamespace(ns[0]);
        if(curns === undefined) {
            return undefined;
        }

        for(let i = 1; i < ns.length; ++i) {
            curns = curns.subns.find((nns) => nns.name === ns[i]);
            if(curns === undefined) {
                return undefined;
            }
        }

        return curns;
    }

    resolveStringRegexValidatorInfo(ttype: TypeSignature): RegexValidatorPack | undefined {
        const tnorm = this.normalizeTypeSignature(ttype, new TemplateConstraintScope());
        if(tnorm instanceof NominalTypeSignature) {
            if(tnorm.resolvedDeclaration instanceof RegexValidatorTypeDecl) {
                return new SingleRegexValidatorPack(tnorm.resolvedDeclaration.regex);
            }
            else if(tnorm.resolvedDeclaration instanceof CRegexValidatorTypeDecl) {
                return new SingleRegexValidatorPack(tnorm.resolvedDeclaration.regex);
            }
            else {
                return undefined;
            }
        }
        else if(tnorm instanceof UnionTypeSignature) {
            const lpack = this.resolveStringRegexValidatorInfo(tnorm.ltype);
            const rpack = this.resolveStringRegexValidatorInfo(tnorm.rtype);
            if(lpack === undefined || rpack === undefined) {
                return undefined;
            }
            else {
                return new OrRegexValidatorPack([lpack, rpack]);
            }
        }
        else {
            return undefined;
        }
    }

    resolveNamespaceConstant(ns: FullyQualifiedNamespace, name: string): NamespaceConstDecl | undefined {
        const nsdecl = this.resolveNamespaceDecl(ns.ns);
        if(nsdecl === undefined) {
            return undefined;
        }

        return nsdecl.consts.find((c) => c.name === name);
    }

    resolveNamespaceFunction(ns: FullyQualifiedNamespace, name: string): NamespaceFunctionDecl | undefined {
        const nsdecl = this.resolveNamespaceDecl(ns.ns);
        if(nsdecl === undefined) {
            return undefined;
        }

        return nsdecl.functions.find((c) => c.name === name);
    }

    isAccessToEnum(tsig: TypeSignature, name: string): boolean {
        const tn = this.normalizeTypeSignatureIncludingTemplate(tsig, new TemplateConstraintScope());
        if(!(tn instanceof NominalTypeSignature)) {
            return false;
        }

        const tdecl = tn.resolvedDeclaration as AbstractNominalTypeDecl;
        return (tdecl instanceof EnumTypeDecl && tdecl.members.includes(name));
    }

    resolveTypeConstant(tsig: TypeSignature, name: string, tconstrain: TemplateConstraintScope): MemberLookupInfo<ConstMemberDecl> | undefined {
        const tn = this.normalizeTypeSignatureIncludingTemplate(tsig, tconstrain);

        if(!(tn instanceof NominalTypeSignature)) {
            return undefined; //TODO: we could potentially resolve constants from unions later
        }

        const tdecl = tn.resolvedDeclaration as AbstractNominalTypeDecl;
        const cci = tdecl.consts.find((c) => c.name === name);
        if(cci !== undefined) {
            const tlinfo = new TypeLookupInfo(tn, tdecl, TypeCheckerRelations.computeNameMapperFromDirectTypeSignatureInfo(tn));
            return new MemberLookupInfo<ConstMemberDecl>(tlinfo, cci);
        }
        else {
            assert(false, "Need to handle inherited constants");
        }
    }

    resolveTypeField(tsig: TypeSignature, name: string, tconstrain: TemplateConstraintScope): MemberLookupInfo<MemberFieldDecl> | undefined {
        const tn = this.normalizeTypeSignatureIncludingTemplate(tsig, tconstrain);

        if(!(tn instanceof NominalTypeSignature)) {
            return undefined; //TODO: we could potentially resolve fields from unions later
        }

        const tdecl = tn.resolvedDeclaration as AbstractNominalTypeDecl;
        let cci: MemberFieldDecl | undefined = undefined;
        if(tdecl instanceof EntityTypeDecl) {
            cci = tdecl.fields.find((c) => c.name === name);
        }
        else if(tdecl instanceof ConceptTypeDecl) {
            cci = tdecl.fields.find((c) => c.name === name);
        }
        else if(tdecl instanceof DatatypeMemberEntityTypeDecl) {
            cci = tdecl.fields.find((c) => c.name === name);
        }
        else if(tdecl instanceof DatatypeTypeDecl) {
            cci = tdecl.fields.find((c) => c.name === name);
        }
        else if(tdecl instanceof TaskDecl) {
            cci = tdecl.fields.find((c) => c.name === name);
        }
        else {
            return undefined;
        }

        if(cci !== undefined) {
            const tlinfo = new TypeLookupInfo(tn, tdecl, TypeCheckerRelations.computeNameMapperFromDirectTypeSignatureInfo(tn));
            return new MemberLookupInfo<MemberFieldDecl>(tlinfo, cci);
        }
        else {
            assert(false, "Need to handle inherited constants");
        }
    }

    resolveTypeMethodDeclaration(tsig: TypeSignature, name: string, tconstrain: TemplateConstraintScope): MemberLookupInfo<MethodDecl> | undefined {
        const tn = this.normalizeTypeSignatureIncludingTemplate(tsig, tconstrain);

        if(!(tn instanceof NominalTypeSignature)) {
            return undefined; //TODO: we could potentially resolve methods from unions later
        }

        const tdecl = tn.resolvedDeclaration as AbstractNominalTypeDecl;
        const cci = tdecl.methods.find((c) => c.name === name);
        if(cci !== undefined && cci.attributes.find((attr) => attr.name !== "override") === undefined) {
            const tlinfo = new TypeLookupInfo(tn, tdecl, TypeCheckerRelations.computeNameMapperFromDirectTypeSignatureInfo(tn));
            return new MemberLookupInfo<MethodDecl>(tlinfo, cci);
        }
        else {
            assert(false, "Need to handle inherited constants");
        }
    }

    resolveTypeMethodImplementation(tsig: TypeSignature, name: string, tconstrain: TemplateConstraintScope): MemberLookupInfo<MethodDecl> | undefined {
        const tn = this.normalizeTypeSignatureIncludingTemplate(tsig, tconstrain);

        if(!(tn instanceof NominalTypeSignature)) {
            return undefined; //TODO: we could potentially resolve methods from unions later
        }

        const tdecl = tn.resolvedDeclaration as AbstractNominalTypeDecl;
        const cci = tdecl.methods.find((c) => c.name === name);
        if(cci !== undefined && cci.attributes.find((attr) => attr.name !== "override") === undefined) {
            const tlinfo = new TypeLookupInfo(tn, tdecl, TypeCheckerRelations.computeNameMapperFromDirectTypeSignatureInfo(tn));
            return new MemberLookupInfo<MethodDecl>(tlinfo, cci);
        }
        else {
            assert(false, "Need to handle inherited constants");
        }
    }

    resolveTypeFunction(tsig: TypeSignature, name: string, tconstrain: TemplateConstraintScope): MemberLookupInfo<TypeFunctionDecl> | undefined {
        const tn = this.normalizeTypeSignatureIncludingTemplate(tsig, tconstrain);

        if(!(tn instanceof NominalTypeSignature)) {
            return undefined; //TODO: we could potentially resolve methods from unions later
        }

        const tdecl = tn.resolvedDeclaration as AbstractNominalTypeDecl;
        const cci = tdecl.methods.find((c) => c.name === name);
        if(cci !== undefined && cci.attributes.find((attr) => attr.name !== "override") === undefined) {
            const tlinfo = new TypeLookupInfo(tn, tdecl, TypeCheckerRelations.computeNameMapperFromDirectTypeSignatureInfo(tn));
            return new MemberLookupInfo<TypeFunctionDecl>(tlinfo, cci);
        }
        else {
            assert(false, "Need to handle inherited constants");
        }
    }

    //get all of the actual fields that are provided via inheritance
    resolveAllInheritedFieldDecls(provides: TypeSignature[], tconstrain: TemplateConstraintScope): MemberLookupInfo<MemberFieldDecl>[] {
        const pdecls = this.resolveAllProvidesDecls(provides, tconstrain);

        let allfields: MemberLookupInfo<MemberFieldDecl>[] = [];
        for(let i = 0; i < pdecls.length; ++i) {
            const pdecl = pdecls[i];

            if(pdecl.ttype instanceof EntityTypeDecl) {
                allfields = allfields.concat(pdecl.ttype.fields.map((f) => new MemberLookupInfo<MemberFieldDecl>(pdecl, f)));
            }
            else if(pdecl.ttype instanceof ConceptTypeDecl) {
                allfields = allfields.concat(pdecl.ttype.fields.map((f) => new MemberLookupInfo<MemberFieldDecl>(pdecl, f)));
            }
            else if(pdecl.ttype instanceof DatatypeMemberEntityTypeDecl) {
                allfields = allfields.concat(pdecl.ttype.fields.map((f) => new MemberLookupInfo<MemberFieldDecl>(pdecl, f)));
            }
            else if(pdecl.ttype instanceof DatatypeTypeDecl) {
                allfields = allfields.concat(pdecl.ttype.fields.map((f) => new MemberLookupInfo<MemberFieldDecl>(pdecl, f)));
            }
            else if(pdecl.ttype instanceof TaskDecl) {
                allfields = allfields.concat(pdecl.ttype.fields.map((f) => new MemberLookupInfo<MemberFieldDecl>(pdecl, f)));
            }
            else {
                allfields = [];
            }
        }

        return allfields;
    }

    generateAllFieldBNamesInfo(tdecl: AbstractNominalTypeDecl, mfields: MemberFieldDecl[], tconstrain: TemplateConstraintScope): {name: string, type: TypeSignature}[] {
        const ifields = this.resolveAllInheritedFieldDecls(tdecl.provides, tconstrain);

        const ibnames = ifields.map((mf) => { return {name: mf.member.name, type: mf.member.declaredType.remapTemplateBindings(mf.typeinfo.mapping)}; });
        const mbnames = mfields.map((mf) => { return {name: mf.name, type: mf.declaredType}; });

        return [...ibnames, ...mbnames];
    }

    convertTypeSignatureToTypeInferCtx(tsig: TypeSignature, tconstrain: TemplateConstraintScope): TypeInferContext {
        const tnorm = this.normalizeTypeSignature(tsig, tconstrain);
        
        if(!(tnorm instanceof EListTypeSignature)) {
            return new SimpleTypeInferContext(tnorm);
        }
        else {
            return new EListStyleTypeInferContext([...tnorm.entries]);
        }
    }

    //Compute the upper bound of two types for use in control-flow join types
    joinTypes(t1: TypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        assert(!(t1 instanceof ErrorTypeSignature), "Checking subtypes on errors");
        assert(!(t2 instanceof ErrorTypeSignature), "Checking subtypes on errors");

        return this.simplifyUnionType(new UnionTypeSignature(t1.sinfo, t1, t2), tconstrain);
    }

    //Compute the upper bound of two types for use in control-flow join types
    joinAllTypes(topts: TypeSignature[], tconstrain: TemplateConstraintScope): TypeSignature {
        assert(topts.length > 0, "Empty type list for joinAllTypes");
        let res = topts[0];
        for(let i = 1; i < topts.length; ++i) {
            res = this.joinTypes(res, topts[i], tconstrain);
        }

        return res;
    }
}

export {
    RegexValidatorPack, ErrorRegexValidatorPack, SingleRegexValidatorPack, OrRegexValidatorPack,
    TypeLookupInfo, MemberLookupInfo,
    TypeCheckerRelations
};
