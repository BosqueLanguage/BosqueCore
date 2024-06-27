import assert from "node:assert";

import { AutoTypeSignature, EListTypeSignature, ErrorTypeSignature, FullyQualifiedNamespace, LambdaParameterSignature, LambdaTypeSignature, NominalTypeSignature, NoneableTypeSignature, StringTemplateTypeSignature, TemplateConstraintScope, TemplateNameMapper, TemplateTypeSignature, TypeSignature, VoidTypeSignature } from "./type.js";
import { AbstractConceptTypeDecl, AbstractNominalTypeDecl, AdditionalTypeDeclTag, Assembly, ConceptTypeDecl, ConstMemberDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, EntityTypeDecl, EnumTypeDecl, ErrTypeDecl, CRegexValidatorTypeDecl, InternalEntityTypeDecl, MemberFieldDecl, MethodDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, OkTypeDecl, OptionTypeDecl, PathValidatorTypeDecl, PrimitiveEntityTypeDecl, RegexValidatorTypeDecl, ResultTypeDecl, SomethingTypeDecl, TaskDecl, TemplateTermDeclExtraTag, TypeFunctionDecl, TypedeclTypeDecl, PrimitiveConceptTypeDecl, MapEntryTypeDecl, PairTypeDecl, StringOfTypeDecl, CStringOfTypeDecl } from "./assembly.js";
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

    generateTemplateMappingForTypeDecl(t: NominalTypeSignature): TemplateNameMapper {
        let pmap = new Map<string, TypeSignature>();
        for(let j = 0; j < t.decl.terms.length; ++j) {
            pmap.set(t.decl.terms[j].name, t.alltermargs[j]);
        }

        return TemplateNameMapper.createInitialMapping(pmap)
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
            const btype = this.getTypeDeclBasePrimitiveType(t);
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

            pdecls.push(new TypeLookupInfo(ptype, this.generateTemplateMappingForTypeDecl(ptype)));
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
    isPrimitiveType(t: TypeSignature): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        return (t instanceof NominalTypeSignature) && t.decl instanceof PrimitiveEntityTypeDecl;
    }

    //Check if we can assign this type as the RHS of a typedecl declaration
    isTypedeclableType(t: TypeSignature): boolean {
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
    isEventDataType(t: TypeSignature): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        return (t instanceof NominalTypeSignature) && t.decl.etag === AdditionalTypeDeclTag.Event;
    }

    //Check if this type is a valid status
    isStatusDataType(t: TypeSignature): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        return (t instanceof NominalTypeSignature) && t.decl.etag === AdditionalTypeDeclTag.Status;
    }

    //Check if this type is a valid type to have as a provides type -- must be a unique CONCEPT type
    isValidProvidesType(t: TypeSignature): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        return (t instanceof NominalTypeSignature) && (t.decl instanceof AbstractConceptTypeDecl);
    }

    //Check if this is a valid type to have a template restriction set to
    isValidTemplateRestrictionType(t: TypeSignature): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        if(t instanceof NoneableTypeSignature) {
            return true;
        }
        else if(t instanceof NominalTypeSignature) {
            return t.decl instanceof AbstractConceptTypeDecl;
        }
        else {
            return false;
        }
    }

    //Check if this type is a typedecl of some sort
    isTypeDeclType(t: TypeSignature): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        return (t instanceof NominalTypeSignature) && (t.decl instanceof TypedeclTypeDecl);
    }

    //Take a type and decompose it (using out type system rules) into the constituent types that make it up
    decomposeType(t: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature[] | undefined {
        assert((t instanceof TemplateTypeSignature) || (t instanceof NominalTypeSignature) || (t instanceof NoneableTypeSignature) || (t instanceof StringTemplateTypeSignature));

        if(t instanceof TemplateTypeSignature) {
            const cons = tconstrain.resolveConstraint(t.name);
            return cons !== undefined ? this.decomposeType(cons.tconstraint, tconstrain) : undefined;
        }
        else if(t instanceof NoneableTypeSignature) {
            const ntdcs = this.decomposeType(t.type, tconstrain);
            return ntdcs !== undefined ? [...ntdcs, this.wellknowntypes.get("None") as TypeSignature] : undefined;
        }
        else if(t instanceof NominalTypeSignature) {
            const corens = this.assembly.getCoreNamespace();

            if(t.tkeystr === "Any") {
                return [this.wellknowntypes.get("None") as TypeSignature, this.wellknowntypes.get("Some") as TypeSignature];
            }
            else if(t.decl instanceof OptionTypeDecl) {
                const something = new NominalTypeSignature(t.sinfo, corens.typedecls.find((tdecl) => tdecl.name === "Something") as SomethingTypeDecl, t.alltermargs);

                return [this.wellknowntypes.get("Nothing") as TypeSignature, something];
            }
            else if(t.decl instanceof ResultTypeDecl) {
                const tresult = corens.typedecls.find((tdecl) => tdecl.name === "Result") as ResultTypeDecl;
                const tok = new NominalTypeSignature(t.sinfo, tresult.getOkType(), t.alltermargs);
                const terr = new NominalTypeSignature(t.sinfo, tresult.getErrType(), t.alltermargs);

                return [tok, terr];
            }
            else if(t.decl instanceof DatatypeTypeDecl) {
                return t.decl.associatedMemberEntityDecls.map((mem) => new NominalTypeSignature(mem.sinfo, mem, t.alltermargs));
            }
            else {
                return [t];
            }
        }
        else {
            return [t];
        }
    }

    private isUniqueSplitCheckType(t: TypeSignature): boolean {
        return (t instanceof StringTemplateTypeSignature) || (t instanceof NominalTypeSignature && !(t.decl instanceof AbstractConceptTypeDecl));
    }

    private mustDisjointCheckForSplit(t1: TypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        if(this.isUniqueSplitCheckType(t1) && this.isUniqueSplitCheckType(t2)) {
            return !this.areSameTypes(t1, t2, tconstrain);
        }
        else if(this.isUniqueSplitCheckType(t1)) {
            return !this.isSubtypeOf(t1, t2, tconstrain);
        }
        else if(this.isUniqueSplitCheckType(t2)) {
            return !this.isSubtypeOf(t2, t1, tconstrain);
        }
        else {
            return false;
        }
    }


    splitOnTypeDecomposedSet(dcs: TypeSignature[], refine: TypeSignature, tconstrain: TemplateConstraintScope): { overlap: TypeSignature | undefined, remain: TypeSignature[] } | undefined {
        assert((refine instanceof ErrorTypeSignature) || (refine instanceof TemplateTypeSignature) || (refine instanceof NominalTypeSignature) || (refine instanceof NoneableTypeSignature) || (refine instanceof StringTemplateTypeSignature));

        if(refine instanceof ErrorTypeSignature) {
            return { overlap: undefined, remain: [] };
        }

        //It is an overlap if there is any type that may overlap (e.g. not definitely disjoint -- consider T as it's restriction for this test)
        const refineexp = this.normalizeAndTemplateInstantiate(refine, tconstrain);
        let overlap: boolean = dcs.some((tt) => !this.mustDisjointCheckForSplit(tt, refineexp, tconstrain));

        //It stays in the remain set unless it is definitely a subtype of the refine type
        let remain: TypeSignature[] = dcs.filter((tt) => !this.isSubtypeOf(tt, refine, tconstrain));
        
        return { overlap: overlap ? refine : undefined, remain: remain };
    }

    refineType(src: TypeSignature, refine: TypeSignature, tconstrain: TemplateConstraintScope): { overlap: TypeSignature | undefined, remain: TypeSignature[] } | undefined {
        assert((refine instanceof ErrorTypeSignature) || (refine instanceof TemplateTypeSignature) || (refine instanceof NominalTypeSignature) || (refine instanceof NoneableTypeSignature) || (refine instanceof StringTemplateTypeSignature));

        if((src instanceof ErrorTypeSignature) || (refine instanceof ErrorTypeSignature)) {
            return { overlap: undefined, remain: [] };
        }

        if(this.isSubtypeOf(src, refine, tconstrain)) {
            return { overlap: refine, remain: [] };
        }

        const refineexp = this.normalizeAndTemplateInstantiate(refine, tconstrain);
        if(this.mustDisjointCheckForSplit(src, refineexp, tconstrain)) {
            return { overlap: undefined, remain: [src] };
        }

        const dct = this.decomposeType(src, tconstrain);
        if(dct === undefined) {
            return undefined;
        }
        return this.splitOnTypeDecomposedSet(dct, refine, tconstrain);
    }

    splitOnNoneDecomposedSet(dcs: TypeSignature[], tconstrain: TemplateConstraintScope): { overlap: TypeSignature | undefined, remain: TypeSignature[] } | undefined {
        return this.splitOnTypeDecomposedSet(dcs, this.wellknowntypes.get("None") as TypeSignature, tconstrain);
    }

    splitOnNone(src: TypeSignature, tconstrain: TemplateConstraintScope): { hasnoneoverlap: boolean, remain: TypeSignature[] } | undefined {
        const dcs = this.refineType(src, this.wellknowntypes.get("None") as TypeSignature, tconstrain);

        return dcs !== undefined ? { hasnoneoverlap: dcs.overlap !== undefined, remain: dcs.remain } : undefined;
    }

    splitOnSomeDecomposedSet(dcs: TypeSignature[], tconstrain: TemplateConstraintScope): { overlap: TypeSignature | undefined, remain: TypeSignature[] } | undefined {
        return this.splitOnTypeDecomposedSet(dcs, this.wellknowntypes.get("Some") as TypeSignature, tconstrain);
    }

    splitOnSome(src: TypeSignature, tconstrain: TemplateConstraintScope): { hassome: boolean, hasnoneremain: boolean } | undefined {
        const dcs = this.refineType(src, this.wellknowntypes.get("Some") as TypeSignature, tconstrain);

        return dcs !== undefined ? { hassome: dcs.overlap !== undefined , hasnoneremain: dcs.remain.length !== 0 } : undefined;
    }

    splitOnNothingDecomposedSet(dcs: TypeSignature[], tconstrain: TemplateConstraintScope): { hasnothing: boolean, remainSomethingT: TypeSignature | undefined } | undefined {
        if(!dcs.every((t) => (t instanceof NominalTypeSignature) && ((t.decl instanceof SomethingTypeDecl) || (t.decl instanceof OptionTypeDecl) || (t.decl instanceof PrimitiveEntityTypeDecl) && t.decl.name === "Nothing"))) {
            return undefined;
        }

        let hasnothing = false;
        let somethingT: TypeSignature | undefined = undefined;
        for(let i = 0; i < dcs.length; ++i) {
            const t = dcs[i] as NominalTypeSignature;

            hasnothing = hasnothing || this.isSubtypeOf(this.wellknowntypes.get("Nothing") as TypeSignature, t, tconstrain);
            if((t.decl instanceof SomethingTypeDecl) || (t.decl instanceof OptionTypeDecl)) {
                const topt = t.alltermargs[0];

                if(somethingT !== undefined && !this.areSameTypes(somethingT, topt, tconstrain)) {
                    return undefined;
                }
                somethingT = topt;
            }
        }

        return { hasnothing: hasnothing, remainSomethingT: somethingT as TypeSignature };
    }

    splitOnNothing(src: TypeSignature, tconstrain: TemplateConstraintScope): { hasnothing: boolean, remainSomethingT: TypeSignature | undefined } | undefined {
        if(src instanceof ErrorTypeSignature) {
            return { hasnothing: false, remainSomethingT: undefined };
        }

        const dct = this.decomposeType(src, tconstrain);
        if(dct === undefined) {
            return undefined;
        }
        return this.splitOnNothingDecomposedSet(dct, tconstrain);
    }

    splitOnSomethingDecomposedSet(dcs: TypeSignature[], tconstrain: TemplateConstraintScope): { overlapSomethingT: TypeSignature | undefined, hasnothing: boolean } | undefined {
        if(!dcs.every((t) => (t instanceof NominalTypeSignature) && ((t.decl instanceof SomethingTypeDecl) || (t.decl instanceof OptionTypeDecl) || (t.decl instanceof PrimitiveEntityTypeDecl) && t.decl.name === "Nothing"))) {
            return undefined;
        }

        let hasnothing = false;
        let somethingT: TypeSignature | undefined = undefined;
        for(let i = 0; i < dcs.length; ++i) {
            const t = dcs[i] as NominalTypeSignature;

            hasnothing = hasnothing || this.isSubtypeOf(this.wellknowntypes.get("Nothing") as TypeSignature, t, tconstrain);
            if((t.decl instanceof SomethingTypeDecl) || (t.decl instanceof OptionTypeDecl)) {
                const topt = t.alltermargs[0];

                if(somethingT !== undefined && !this.areSameTypes(somethingT, topt, tconstrain)) {
                    return undefined;
                }
                somethingT = topt;
            }
        }

        return { overlapSomethingT: somethingT as TypeSignature, hasnothing: hasnothing };
    }

    splitOnSomething(src: TypeSignature, tconstrain: TemplateConstraintScope): { overlapSomethingT: TypeSignature | undefined, hasnothing: boolean } | undefined {
        if(src instanceof ErrorTypeSignature) {
            return { overlapSomethingT: undefined, hasnothing: false };
        }

        const dct = this.decomposeType(src, tconstrain);
        if(dct === undefined) {
            return undefined;
        }
        return this.splitOnSomethingDecomposedSet(dct, tconstrain);
    }

    splitOnOkDecomposedSet(dcs: TypeSignature[], tconstrain: TemplateConstraintScope): { overlapOkT: TypeSignature | undefined, remainErrE: TypeSignature | undefined } | undefined {
        if(!dcs.every((t) => (t instanceof NominalTypeSignature) && ((t.decl instanceof OkTypeDecl) || (t.decl instanceof ErrTypeDecl) || (t.decl instanceof ResultTypeDecl)))) {
            return undefined;
        }

        let typeT: TypeSignature | undefined = undefined;
        let typeE: TypeSignature | undefined = undefined;
        let haserr = false;
        let hasok = false;
        for(let i = 0; i < dcs.length; ++i) {
            const t = dcs[i] as NominalTypeSignature;
            const topt = t.alltermargs[0];
            const eopt = t.alltermargs[1];

            if(typeT !== undefined && !this.areSameTypes(typeT, topt, tconstrain)) {
                return undefined;
            }
            typeT = topt;

            if(typeE !== undefined && !this.areSameTypes(typeE, eopt, tconstrain)) {
                return undefined;
            }
            typeE = eopt;

            if(t.decl instanceof ResultTypeDecl) {
                hasok = true;
                haserr = true;
            }
            if(t.decl instanceof ErrTypeDecl) {
                haserr = true;
            }
            else {
                hasok = true;
            }
        }

        return { overlapOkT: hasok ? typeT : undefined, remainErrE: haserr ? typeE : undefined};
    }

    splitOnOk(src: TypeSignature, tconstrain: TemplateConstraintScope): { overlapOkT: TypeSignature | undefined, remainErrE: TypeSignature | undefined } | undefined {
        if(src instanceof ErrorTypeSignature) {
            return { overlapOkT: undefined, remainErrE: undefined };
        }

        const dct = this.decomposeType(src, tconstrain);
        if(dct === undefined) {
            return undefined;
        }
        return this.splitOnOkDecomposedSet(dct, tconstrain);
    }

    splitOnErrDecomposedSet(dcs: TypeSignature[], tconstrain: TemplateConstraintScope): { overlapErrE: TypeSignature | undefined, remainOkT: TypeSignature | undefined } | undefined {
        if(!dcs.every((t) => (t instanceof NominalTypeSignature) && ((t.decl instanceof OkTypeDecl) || (t.decl instanceof ErrTypeDecl) || (t.decl instanceof ResultTypeDecl)))) {
            return undefined;
        }

        let typeT: TypeSignature | undefined = undefined;
        let typeE: TypeSignature | undefined = undefined;
        let hasok = false;
        let haserr = false;
        for(let i = 0; i < dcs.length; ++i) {
            const t = dcs[i] as NominalTypeSignature;
            const topt = t.alltermargs[0];
            const eopt = t.alltermargs[1];

            if(typeT !== undefined && !this.areSameTypes(typeT, topt, tconstrain)) {
                return undefined;
            }
            typeT = topt;

            if(typeE !== undefined && !this.areSameTypes(typeE, eopt, tconstrain)) {
                return undefined;
            }
            typeE = eopt;

            if(t.decl instanceof ResultTypeDecl) {
                haserr = true;
                hasok = true;
            }
            if(t.decl instanceof OkTypeDecl) {
                hasok = true;
            }
            else {
                haserr = true;
            }
        }

        return { overlapErrE: haserr ? typeE : undefined, remainOkT: hasok ? typeT : undefined };
    }

    splitOnErr(src: TypeSignature, tconstrain: TemplateConstraintScope): { overlapErrE: TypeSignature | undefined, remainOkT: TypeSignature | undefined } | undefined {
        if(src instanceof ErrorTypeSignature) {
            return { overlapErrE: undefined, remainOkT: undefined };
        }

        const dct = this.decomposeType(src, tconstrain);
        if(dct === undefined) {
            return undefined;
        }
        return this.splitOnErrDecomposedSet(dct, tconstrain);
    }

    //Get the assigned value type of a typedecl (resolving as needed)
    getTypeDeclValueType(t: TypeSignature): TypeSignature | undefined {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        if(!(t instanceof NominalTypeSignature)) {
            return undefined;
        }

        if(t.decl instanceof TypedeclTypeDecl) {
            return t.decl.valuetype.remapTemplateBindings(this.generateTemplateMappingForTypeDecl(t));
        }
        else {
            return undefined;
        }
    }

    private getTypeDeclBasePrimitiveType_Helper(t: TypeSignature): TypeSignature | undefined {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        if(!(t instanceof NominalTypeSignature)) {
            return undefined;
        }

        if(t.decl instanceof EnumTypeDecl) {
            return t;
        }
        else if(t.decl instanceof TypedeclTypeDecl) {
            return this.getTypeDeclBasePrimitiveType_Helper(t.decl.valuetype.remapTemplateBindings(this.generateTemplateMappingForTypeDecl(t)));
        }
        else if(t.decl instanceof InternalEntityTypeDecl) {
            const isdeclable = t.decl.attributes.find((attr) => attr.name === "__typedeclable") !== undefined;
            return isdeclable ? t : undefined;
        }
        else {
            return undefined;
        }
    }

    //Get the base primitive type of a typedecl (resolving through typedecls and aliases as needed)
    getTypeDeclBasePrimitiveType(t: TypeSignature): TypeSignature | undefined {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        if(!(t instanceof NominalTypeSignature)) {
            return undefined;
        }

        if(t.decl instanceof TypedeclTypeDecl) {
            return this.getTypeDeclBasePrimitiveType_Helper(t);
        }
        else {
            return undefined;
        }
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

    resolveStringRegexValidatorInfo(ttype: TypeSignature): string | undefined {
        if(ttype instanceof NominalTypeSignature) {
            if(ttype.decl instanceof RegexValidatorTypeDecl) {
                return ttype.decl.regex;
            }
            else if(ttype.decl instanceof CRegexValidatorTypeDecl) {
                return ttype.decl.regex;
            }
            else {
                return undefined;
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
        if(!(tsig instanceof NominalTypeSignature)) {
            return false;
        }

        return (tsig.decl instanceof EnumTypeDecl && tsig.decl.members.includes(name));
    }

    resolveTypeConstant(tsig: TypeSignature, name: string, tconstrain: TemplateConstraintScope): MemberLookupInfo<ConstMemberDecl> | undefined {
        const tn = this.normalizeAndTemplateInstantiate(tsig, tconstrain);

        if(!(tn instanceof NominalTypeSignature)) {
            return undefined;
        }

        const cci = tn.decl.consts.find((c) => c.name === name);
        if(cci !== undefined) {
            const tlinfo = new TypeLookupInfo(tn, this.generateTemplateMappingForTypeDecl(tn));
            return new MemberLookupInfo<ConstMemberDecl>(tlinfo, cci);
        }
        else {
            const provides = this.resolveAllProvidesDecls(tn.decl.provides);
            for(let i = 0; i < provides.length; ++i) {
                const pdecl = provides[i];
                const pdtype = pdecl.tsig.remapTemplateBindings(pdecl.mapping);

                const flookup = this.resolveTypeConstant(pdtype, name, tconstrain);
                if(flookup !== undefined) {
                    return flookup;
                }
            }

            return undefined;
        }
    }

    resolveTypeField(tsig: TypeSignature, name: string, tconstrain: TemplateConstraintScope): MemberLookupInfo<MemberFieldDecl> | undefined {
        const tn = this.normalizeAndTemplateInstantiate(tsig, tconstrain);

        if(!(tn instanceof NominalTypeSignature)) {
            return undefined; //TODO: we could potentially resolve fields from unions later
        }

        let cci: MemberFieldDecl | undefined = undefined;
        if(tn.decl instanceof EntityTypeDecl) {
            cci = tn.decl.fields.find((c) => c.name === name);
        }
        else if(tn.decl instanceof ConceptTypeDecl) {
            cci = tn.decl.fields.find((c) => c.name === name);
        }
        else if(tn.decl instanceof DatatypeMemberEntityTypeDecl) {
            cci = tn.decl.fields.find((c) => c.name === name);
        }
        else if(tn.decl instanceof DatatypeTypeDecl) {
            cci = tn.decl.fields.find((c) => c.name === name);
        }
        else if(tn.decl instanceof TaskDecl) {
            cci = tn.decl.fields.find((c) => c.name === name);
        }
        else {
            if(tn.decl instanceof TypedeclTypeDecl) {
                if(name === "value") {
                    const valuetype = this.getTypeDeclValueType(tn);
                    if(valuetype !== undefined) {
                        cci = new MemberFieldDecl(tn.decl.file, tn.decl.sinfo, [], "value", valuetype, undefined);
                    }
                }
                if(name === "primitive") {
                    const primtype = this.getTypeDeclBasePrimitiveType(tn);
                    if(primtype !== undefined) {
                        cci = new MemberFieldDecl(tn.decl.file, tn.decl.sinfo, [], "primitive", primtype, undefined);
                    }
                }
            }
            else if(tn.decl instanceof StringOfTypeDecl) {
                if(name === "value") {
                    cci = new MemberFieldDecl(tn.decl.file, tn.decl.sinfo, [], "value", this.wellknowntypes.get("String") as TypeSignature, undefined);
                }
            }
            else if(tn.decl instanceof CStringOfTypeDecl) {
                if(name === "value") {
                    cci = new MemberFieldDecl(tn.decl.file, tn.decl.sinfo, [], "value", this.wellknowntypes.get("CString") as TypeSignature, undefined);
                }
            }
            else if(tn.decl instanceof SomethingTypeDecl) {
                if(name === "value") {
                    cci = new MemberFieldDecl(tn.decl.file, tn.decl.sinfo, [], "value", tn.alltermargs[0], undefined);
                }
            }
            else if(tn.decl instanceof OkTypeDecl) {
                if(name === "value") {
                    cci = new MemberFieldDecl(tn.decl.file, tn.decl.sinfo, [], "value", tn.alltermargs[0], undefined);
                }
            }
            else if(tn.decl instanceof ErrTypeDecl) {
                if(name === "error") {
                    cci = new MemberFieldDecl(tn.decl.file, tn.decl.sinfo, [], "value", tn.alltermargs[0], undefined);
                }
            }
            else if(tn.decl instanceof PairTypeDecl) {
                if(name === "first") {
                    cci = new MemberFieldDecl(tn.decl.file, tn.decl.sinfo, [], "first", tn.alltermargs[0], undefined);
                }
                if(name === "second") {
                    cci = new MemberFieldDecl(tn.decl.file, tn.decl.sinfo, [], "second", tn.alltermargs[1], undefined);
                }
            }
            else if(tn.decl instanceof MapEntryTypeDecl) {
                if(name === "key") {
                    cci = new MemberFieldDecl(tn.decl.file, tn.decl.sinfo, [], "key", tn.alltermargs[0], undefined);
                }
                if(name === "value") {
                    cci = new MemberFieldDecl(tn.decl.file, tn.decl.sinfo, [], "value", tn.alltermargs[1], undefined);
                }
            }
            else {
                ;
            }
        }

        if(cci !== undefined) {
            const tlinfo = new TypeLookupInfo(tn, this.generateTemplateMappingForTypeDecl(tn));
            return new MemberLookupInfo<MemberFieldDecl>(tlinfo, cci);
        }
        else {
            const provides = this.resolveAllProvidesDecls(tn.decl.provides);
            for(let i = 0; i < provides.length; ++i) {
                const pdecl = provides[i];
                const pdtype = pdecl.tsig.remapTemplateBindings(pdecl.mapping);

                const flookup = this.resolveTypeField(pdtype, name, tconstrain);
                if(flookup !== undefined) {
                    return flookup;
                }
            }

            return undefined;
        }
    }

    resolveTypeMethodDeclaration(tsig: TypeSignature, name: string, tconstrain: TemplateConstraintScope): MemberLookupInfo<MethodDecl> | undefined {
        const tn = this.normalizeAndTemplateInstantiate(tsig, tconstrain);

        if(!(tn instanceof NominalTypeSignature)) {
            return undefined; //TODO: we could potentially resolve methods from unions later
        }

        const cci = tn.decl.methods.find((c) => c.name === name);
        if(cci !== undefined && cci.attributes.every((attr) => attr.name !== "override") === undefined) {
            const tlinfo = new TypeLookupInfo(tn, this.generateTemplateMappingForTypeDecl(tn));
            return new MemberLookupInfo<MethodDecl>(tlinfo, cci);
        }
        else {
            const provides = this.resolveAllProvidesDecls(tn.decl.provides);
            for(let i = 0; i < provides.length; ++i) {
                const pdecl = provides[i];
                const pdtype = pdecl.tsig.remapTemplateBindings(pdecl.mapping);

                const flookup = this.resolveTypeMethodDeclaration(pdtype, name, tconstrain);
                if(flookup !== undefined) {
                    return flookup;
                }
            }

            return undefined;
        }
    }

    resolveTypeMethodImplementation(tsig: TypeSignature, name: string, tconstrain: TemplateConstraintScope): MemberLookupInfo<MethodDecl> | undefined {
        const tn = this.normalizeAndTemplateInstantiate(tsig, tconstrain);

        if(!(tn instanceof NominalTypeSignature)) {
            return undefined; //TODO: we could potentially resolve methods from unions later
        }

        const cci = tn.decl.methods.find((c) => c.name === name);
        if(cci !== undefined && cci.attributes.every((attr) => attr.name !== "virtual" && attr.name !== "abstract")) {
            const tlinfo = new TypeLookupInfo(tn, this.generateTemplateMappingForTypeDecl(tn));
            return new MemberLookupInfo<MethodDecl>(tlinfo, cci);
        }
        else {
            const provides = this.resolveAllProvidesDecls(tn.decl.provides);
            for(let i = 0; i < provides.length; ++i) {
                const pdecl = provides[i];
                const pdtype = pdecl.tsig.remapTemplateBindings(pdecl.mapping);

                const flookup = this.resolveTypeMethodImplementation(pdtype, name, tconstrain);
                if(flookup !== undefined) {
                    return flookup;
                }
            }

            return undefined;
        }
    }

    resolveTypeFunction(tsig: TypeSignature, name: string, tconstrain: TemplateConstraintScope): MemberLookupInfo<TypeFunctionDecl> | undefined {
        const tn = this.normalizeAndTemplateInstantiate(tsig, tconstrain);

        if(!(tn instanceof NominalTypeSignature)) {
            return undefined; //TODO: we could potentially resolve methods from unions later
        }

        const cci = tn.decl.functions.find((c) => c.name === name);
        if(cci !== undefined) {
            const tlinfo = new TypeLookupInfo(tn, this.generateTemplateMappingForTypeDecl(tn));
            return new MemberLookupInfo<TypeFunctionDecl>(tlinfo, cci);
        }
        else {
            const provides = this.resolveAllProvidesDecls(tn.decl.provides);
            for(let i = 0; i < provides.length; ++i) {
                const pdecl = provides[i];
                const pdtype = pdecl.tsig.remapTemplateBindings(pdecl.mapping);

                const flookup = this.resolveTypeFunction(pdtype, name, tconstrain);
                if(flookup !== undefined) {
                    return flookup;
                }
            }

            return undefined;
        }
    }

    //get all of the actual fields that are provided via inheritance
    resolveAllInheritedFieldDecls(provides: TypeSignature[]): MemberLookupInfo<MemberFieldDecl>[] {
        const pdecls = this.resolveAllProvidesDecls(provides);

        let allfields: MemberLookupInfo<MemberFieldDecl>[] = [];
        for(let i = 0; i < pdecls.length; ++i) {
            const pdecl = pdecls[i];

            if(pdecl.tsig.decl instanceof EntityTypeDecl) {
                allfields = allfields.concat(pdecl.tsig.decl.fields.map((f) => new MemberLookupInfo<MemberFieldDecl>(pdecl, f)));
            }
            else if(pdecl.tsig.decl instanceof ConceptTypeDecl) {
                allfields = allfields.concat(pdecl.tsig.decl.fields.map((f) => new MemberLookupInfo<MemberFieldDecl>(pdecl, f)));
            }
            else if(pdecl.tsig.decl instanceof DatatypeMemberEntityTypeDecl) {
                allfields = allfields.concat(pdecl.tsig.decl.fields.map((f) => new MemberLookupInfo<MemberFieldDecl>(pdecl, f)));
            }
            else if(pdecl.tsig.decl instanceof DatatypeTypeDecl) {
                allfields = allfields.concat(pdecl.tsig.decl.fields.map((f) => new MemberLookupInfo<MemberFieldDecl>(pdecl, f)));
            }
            else if(pdecl.tsig.decl instanceof TaskDecl) {
                allfields = allfields.concat(pdecl.tsig.decl.fields.map((f) => new MemberLookupInfo<MemberFieldDecl>(pdecl, f)));
            }
            else {
                allfields = [];
            }
        }

        return allfields;
    }

    generateAllFieldBNamesInfo(tdecl: AbstractNominalTypeDecl, mfields: MemberFieldDecl[]): {name: string, type: TypeSignature}[] {
        const ifields = this.resolveAllInheritedFieldDecls(tdecl.provides);

        const ibnames = ifields.map((mf) => { return {name: mf.member.name, type: mf.member.declaredType.remapTemplateBindings(mf.typeinfo.mapping)}; });
        const mbnames = mfields.map((mf) => { return {name: mf.name, type: mf.declaredType}; });

        return [...ibnames, ...mbnames];
    }

    convertTypeSignatureToTypeInferCtx(tsig: TypeSignature, tconstrain: TemplateConstraintScope): TypeInferContext {
        if(!(tsig instanceof EListTypeSignature)) {
            return new SimpleTypeInferContext(tsig);
        }
        else {
            return new EListStyleTypeInferContext([...tsig.entries]);
        }
    }
}

export {
    TypeLookupInfo, MemberLookupInfo,
    TypeCheckerRelations
};
