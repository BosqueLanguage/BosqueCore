import assert from "node:assert";

import { AutoTypeSignature, EListTypeSignature, ErrorTypeSignature, FullyQualifiedNamespace, LambdaParameterSignature, LambdaTypeSignature, NominalTypeSignature, StringTemplateTypeSignature, TemplateConstraintScope, TemplateNameMapper, TemplateTypeSignature, TypeSignature, VoidTypeSignature } from "./type.js";
import { AbstractConceptTypeDecl, AdditionalTypeDeclTag, Assembly, ConceptTypeDecl, ConstMemberDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, EntityTypeDecl, EnumTypeDecl, ErrTypeDecl, CRegexValidatorTypeDecl, InternalEntityTypeDecl, MemberFieldDecl, MethodDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, OkTypeDecl, OptionTypeDecl, PathValidatorTypeDecl, PrimitiveEntityTypeDecl, RegexValidatorTypeDecl, ResultTypeDecl, SomeTypeDecl, TaskDecl, TemplateTermDeclExtraTag, TypeFunctionDecl, TypedeclTypeDecl, MapEntryTypeDecl, StringOfTypeDecl, CStringOfTypeDecl, AbstractEntityTypeDecl, ValidateDecl, InvariantDecl } from "./assembly.js";
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

    readonly memoizedTypeEqualRelation: Map<string, boolean> = new Map<string, boolean>();
    readonly memoizedTypeSubtypeRelation: Map<string, boolean> = new Map<string, boolean>();

    constructor(assembly: Assembly, wellknowntypes: Map<string, TypeSignature>) {
        this.assembly = assembly;
        this.wellknowntypes = wellknowntypes;
    }

    generateTemplateMappingForTypeDecl(t: NominalTypeSignature): TemplateNameMapper {
        let pmap = new Map<string, TypeSignature>();

        if(t.decl.isSpecialResultEntity()) {
            pmap.set("T", t.alltermargs[0]);
            pmap.set("E", t.alltermargs[1]);
        }
        else if(t.decl.isSpecialAPIResultEntity()) {
            pmap.set("T", t.alltermargs[0]);
        }
        else {
            for(let j = 0; j < t.decl.terms.length; ++j) {
                pmap.set(t.decl.terms[j].name, t.alltermargs[j]);
            }
        }

        return TemplateNameMapper.createInitialMapping(pmap)
    }

    //get all of the actual concepts + template mappings that are provided by a type
    resolveDirectProvidesDecls(ttype: TypeSignature): TypeLookupInfo[] {
        if(!(ttype instanceof NominalTypeSignature)) {
            return [];
        }

        const pdecls: TypeLookupInfo[] = [];
        for(let i = 0; i < ttype.decl.provides.length; ++i) {
            const ptype = ttype.decl.provides[i];
            if(!(ptype instanceof NominalTypeSignature) || !(ptype.decl instanceof AbstractConceptTypeDecl)) {
                continue;
            }

            if(ptype.decl.terms.length !== ptype.alltermargs.length) {
                continue;
            }

            pdecls.push(new TypeLookupInfo(ptype, this.generateTemplateMappingForTypeDecl(ttype)));
        }

        return pdecls;
    }

    private areSameTypeSignatureLists(tl1: TypeSignature[], tl2: TypeSignature[]): boolean {
        if(tl1.length !== tl2.length) {
            return false;
        }

        for(let i = 0; i < tl1.length; ++i) {
            if(!this.areSameTypes(tl1[i], tl2[i])) {
                return false;
            }
        }

        return true;
    }

    private areSameFunctionParamLists(tl1: LambdaParameterSignature[], tl2: LambdaParameterSignature[]): boolean {
        if(tl1.length !== tl2.length) {
            return false;
        }

        for(let i = 0; i < tl1.length; ++i) {
            if(tl1[i].isRefParam !== tl2[i].isRefParam || tl1[i].isRestParam !== tl2[i].isRestParam) {
                return false;
            }
            
            if(!this.areSameTypes(tl1[i].type, tl2[i].type)) {
                return false;
            }
        }

        return true;
    }

    //Check if t1 and t2 are the same type -- template types are not expanded in this check
    areSameTypes(t1: TypeSignature, t2: TypeSignature): boolean {
        assert(!(t1 instanceof ErrorTypeSignature) && !(t2 instanceof ErrorTypeSignature), "Checking type same on errors");
        assert(!(t1 instanceof AutoTypeSignature) && !(t2 instanceof AutoTypeSignature), "Checking type same on auto");

        const kstr = `(${t1.tkeystr} <> ${t2.tkeystr})`;
        const memoval = this.memoizedTypeEqualRelation.get(kstr);
        if(memoval !== undefined) {
            return memoval;
        }

        let res = false
        if(t1 instanceof VoidTypeSignature && t2 instanceof VoidTypeSignature) {
            res = true;
        }
        else if(t1 instanceof TemplateTypeSignature && t2 instanceof TemplateTypeSignature) {
            res = (t1.name === t2.name);
        }
        else if(t1 instanceof NominalTypeSignature && t2 instanceof NominalTypeSignature) {
            res = (t1.decl === t2.decl) && this.areSameTypeSignatureLists(t1.alltermargs, t2.alltermargs);
        }
        else if(t1 instanceof EListTypeSignature && t2 instanceof EListTypeSignature) {
            res = this.areSameTypeSignatureLists(t1.entries, t2.entries);
        }
        else if(t1 instanceof StringTemplateTypeSignature && t2 instanceof StringTemplateTypeSignature) {
            res = (t1.kind === t2.kind) && this.areSameTypeSignatureLists(t1.argtypes, t2.argtypes);
        }
        else if(t1 instanceof LambdaTypeSignature && t2 instanceof LambdaTypeSignature) {
            if(t1.recursive !== t2.recursive || t1.name !== t2.name) {
                res = false;
            }
            else {
                const okargs = this.areSameFunctionParamLists(t1.params, t2.params);
                const okres = this.areSameTypes(t1.resultType, t2.resultType);

                res = okargs && okres;
            }
        }
        else {
            ; //for all other cases res stays false
        }

        this.memoizedTypeEqualRelation.set(kstr, res);
        return res;
    }

    private templateIsSubtypeOf(t1: TemplateTypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        const cons = tconstrain.resolveConstraint(t1.name);
        return cons !== undefined && cons.tconstraint !== undefined && this.isSubtypeOf(cons.tconstraint, t2, tconstrain);
    }

    private nominalIsSubtypeOf(t1: NominalTypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        if(t1.decl instanceof PrimitiveEntityTypeDecl && t1.decl.name === "None") {
            return t2 instanceof NominalTypeSignature && t2.decl instanceof OptionTypeDecl;
        }
        else {
            const providesinfo = this.resolveDirectProvidesDecls(t1);

            return providesinfo.map((pp) => pp.tsig.remapTemplateBindings(pp.mapping)).some((t) => this.isSubtypeOf(t, t2, tconstrain));
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

        let res = false;
        if(this.areSameTypes(t1, t2)) {
            res = true;
        }
        else {
            if(t1 instanceof TemplateTypeSignature) {
                res = this.templateIsSubtypeOf(t1, t2, tconstrain);
            }
            else if(t1 instanceof NominalTypeSignature) {
                res = this.nominalIsSubtypeOf(t1, t2, tconstrain);
            }
            else {
                res = false;
            }
        }

        this.memoizedTypeSubtypeRelation.set(kstr, res);
        return res;
    }

    flowTypeLUB(sinfo: SourceInfo, lubopt: TypeSignature | undefined, tl: TypeSignature[], tconstrain: TemplateConstraintScope): TypeSignature {
        if(tl.some((t) => (t instanceof ErrorTypeSignature) || (t instanceof AutoTypeSignature) || (t instanceof VoidTypeSignature) || (t instanceof LambdaTypeSignature))) {
            return new ErrorTypeSignature(sinfo, new FullyQualifiedNamespace(["LUB GEN"]));
        }

        //handle elist case
        if(tl.some((t) => t instanceof EListTypeSignature)) {
            if(!tl.every((t) => t instanceof EListTypeSignature)) {
                return new ErrorTypeSignature(sinfo, new FullyQualifiedNamespace(["LUB GEN"]));
            }

            const elts = tl[0];
            for(let i = 1; i < tl.length; ++i) {
                if(!this.areSameTypes(elts, tl[i])) {
                    return new ErrorTypeSignature(sinfo, new FullyQualifiedNamespace(["LUB GEN"]));
                }
            }

            return elts;
        }
        else {
            //eliminate duplicates
            let restypel = [tl[0]];
            for(let i = 1; i < tl.length; ++i) {
                const ntt = tl[i];

                const findres = restypel.findIndex((rt) => this.isSubtypeOf(ntt, rt, tconstrain));
                if(findres === -1) {
                    //not a subtype of any of the existing types -- filter any types that are subtypes of ntt and then add ntt
                    restypel = [...restypel.filter((rt) => !this.isSubtypeOf(rt, ntt, tconstrain)), ntt];
                }
            }
        
            const corens = this.assembly.getCoreNamespace();

            //only one type left
            if(restypel.length === 1) {
                return restypel[0];
            }
    
            //check for special case of None+Some -> Option
            if(tl.length === 2 && tl.every((t) => (t instanceof NominalTypeSignature) && (t.decl instanceof InternalEntityTypeDecl))) {
                const ptl = tl as NominalTypeSignature[];

                const hasnone = ptl.some((t) => t.decl.name === "None");
                const some = ptl.find((t) => t.decl instanceof SomeTypeDecl);
                if(hasnone && some !== undefined) {
                    return new NominalTypeSignature(sinfo, undefined, corens.typedecls.find((tdecl) => tdecl.name === "Option") as TypedeclTypeDecl, some.alltermargs);
                }

                //check for special case of Ok+Err -> Result
                const okopt = ptl.find((t) => t.decl instanceof OkTypeDecl);
                const erropt = ptl.find((t) => t.decl instanceof ErrTypeDecl);
                if(okopt && erropt && this.areSameTypeSignatureLists(okopt.alltermargs, erropt.alltermargs)) {
                    return new NominalTypeSignature(sinfo, undefined, corens.typedecls.find((tdecl) => tdecl.name === "Result") as TypedeclTypeDecl, okopt.alltermargs);
                }
            }

            //check for complete set of datatype members
            if(tl.length > 1 && tl.every((t) => (t instanceof NominalTypeSignature) && (t.decl instanceof DatatypeMemberEntityTypeDecl))) {
                const dptl = tl as NominalTypeSignature[];

                const pptype = new NominalTypeSignature(dptl[0].sinfo, dptl[0].altns, (dptl[0].decl as DatatypeMemberEntityTypeDecl).parentTypeDecl, dptl[0].alltermargs);
                const allsameparents = dptl.every((t) => this.isSubtypeOf(t, pptype, tconstrain));
            
                if(allsameparents) {
                    return pptype;
                }
            }


            //ok check for lubopt
            if(lubopt !== undefined && restypel.every((t) => this.isSubtypeOf(t, lubopt, tconstrain))) {
                return lubopt;
            }
            else {
                return new ErrorTypeSignature(sinfo, new FullyQualifiedNamespace(["LUB GEN"]));
            }
        }
    }

    isKeyType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        if(t instanceof NominalTypeSignature) {
            const oftype = (t.decl instanceof TypedeclTypeDecl) ? this.getTypeDeclBasePrimitiveType(t) : t;
            
            return oftype !== undefined && (oftype instanceof NominalTypeSignature) && oftype.decl.isKeyTypeRestricted();
        }
        else if(t instanceof TemplateTypeSignature) {
            const tcs = tconstrain.resolveConstraint(t.name);
            return tcs !== undefined && tcs.extraTags.includes(TemplateTermDeclExtraTag.KeyType);
        }
        else {
            return false;
        }
    }

    isNumericType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        if(t instanceof NominalTypeSignature) {
            const oftype = (t.decl instanceof TypedeclTypeDecl) ? this.getTypeDeclBasePrimitiveType(t) : t;
            
            return oftype !== undefined && (oftype instanceof NominalTypeSignature) && oftype.decl.isNumericRestricted();
        }
        else if(t instanceof TemplateTypeSignature) {
            const tcs = tconstrain.resolveConstraint(t.name);
            return tcs !== undefined && tcs.extraTags.includes(TemplateTermDeclExtraTag.Numeric);
        }
        else {
            return false;
        }
    }

    isREValidatorType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        if(t instanceof NominalTypeSignature) {
            const oftype = (t.decl instanceof TypedeclTypeDecl) ? this.getTypeDeclBasePrimitiveType(t) : t;
            
            return oftype !== undefined && (oftype instanceof NominalTypeSignature) && oftype.decl.isValidatorReRestricted();
        }
        else if(t instanceof TemplateTypeSignature) {
            const tcs = tconstrain.resolveConstraint(t.name);
            return tcs !== undefined && tcs.extraTags.includes(TemplateTermDeclExtraTag.ValidatorRe);
        }
        else {
            return false;
        }
    }

    isCREValidatorType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        if(t instanceof NominalTypeSignature) {
            const oftype = (t.decl instanceof TypedeclTypeDecl) ? this.getTypeDeclBasePrimitiveType(t) : t;
            
            return oftype !== undefined && (oftype instanceof NominalTypeSignature) && oftype.decl.isValidatorCReRestricted();
        }
        else if(t instanceof TemplateTypeSignature) {
            const tcs = tconstrain.resolveConstraint(t.name);
            return tcs !== undefined && tcs.extraTags.includes(TemplateTermDeclExtraTag.ValidatorCRe);
        }
        else {
            return false;
        }
    }

    isPathValidatorType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        if(t instanceof NominalTypeSignature) {
            const oftype = (t.decl instanceof TypedeclTypeDecl) ? this.getTypeDeclBasePrimitiveType(t) : t;
            
            return oftype !== undefined && (oftype instanceof NominalTypeSignature) && oftype.decl.isValidatorPathRestricted();
        }
        else if(t instanceof TemplateTypeSignature) {
            const tcs = tconstrain.resolveConstraint(t.name);
            return tcs !== undefined && tcs.extraTags.includes(TemplateTermDeclExtraTag.ValidatorPath);
        }
        else {
            return false;
        }
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

        return t.decl.attributes.find((attr) => attr.name === "__typedeclable") !== undefined;
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

        return (t instanceof NominalTypeSignature) && (t.decl instanceof AbstractConceptTypeDecl);
    }

    //Check if this type is a typedecl of some sort
    isTypeDeclType(t: TypeSignature): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        return (t instanceof NominalTypeSignature) && (t.decl instanceof TypedeclTypeDecl);
    }

    //Take a type and decompose it (using out type system rules) into the constituent types that make it up
    decomposeType(t: TypeSignature): TypeSignature[] | undefined {
        assert((t instanceof TemplateTypeSignature) || (t instanceof NominalTypeSignature) || (t instanceof StringTemplateTypeSignature));

        if(t instanceof NominalTypeSignature) {
            const corens = this.assembly.getCoreNamespace();

            if(t.decl instanceof OptionTypeDecl) {
                const some = new NominalTypeSignature(t.sinfo, undefined, corens.typedecls.find((tdecl) => tdecl.name === "Some") as SomeTypeDecl, t.alltermargs);
                return [this.wellknowntypes.get("None") as TypeSignature, some];
            }
            else if(t.decl instanceof ResultTypeDecl) {
                const tresult = corens.typedecls.find((tdecl) => tdecl.name === "Result") as ResultTypeDecl;
                const tok = new NominalTypeSignature(t.sinfo, undefined, tresult.getOkType(), t.alltermargs);
                const terr = new NominalTypeSignature(t.sinfo, undefined, tresult.getErrType(), t.alltermargs);

                return [tok, terr];
            }
            else if(t.decl instanceof DatatypeTypeDecl) {
                return t.decl.associatedMemberEntityDecls.map((mem) => new NominalTypeSignature(mem.sinfo, t.altns, mem, t.alltermargs));
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
        if(t instanceof NominalTypeSignature) {
            //Atomic types are unique and datatypes are closed on extensibility so subtyping is ok for disjointness there too
            return (t.decl instanceof AbstractEntityTypeDecl) || (t.decl instanceof DatatypeTypeDecl);
        }
        else {
            return false;
        }
    }

    private mustDisjointCheckForSplit(t1: TypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        if(this.isUniqueSplitCheckType(t1) || this.isUniqueSplitCheckType(t2)) {
            //in case of datatype we need to check both ways
            return !this.isSubtypeOf(t1, t2, tconstrain) && !this.isSubtypeOf(t2, t1, tconstrain);
        }
        else {
            return false;
        }
    }

    splitOnTypeDecomposedSet(dcs: TypeSignature[], refine: TypeSignature[], tconstrain: TemplateConstraintScope): { overlap: TypeSignature[], remain: TypeSignature[] } {
        let overlap: TypeSignature[] = [];
        let remain: TypeSignature[] = [];

        for(let i = 0; i < dcs.length; ++i) {
            const dct = dcs[i];
         
            //it if it MAY overlap (e.g. not must disjoint) then it is in the overlap set
            const isoverlap = refine.some((rt) => !this.mustDisjointCheckForSplit(dct, rt, tconstrain));

            //if is not a strict subtype of any of the refine types then it stays in the remain set
            const isremain = !refine.some((rt) => this.isSubtypeOf(dct, rt, tconstrain));

            if(isoverlap) {
                overlap.push(dct);
            }
            if(isremain) {
                remain.push(dct);
            }
        }

        return { overlap: overlap, remain: remain };
    }

    refineMatchType(src: TypeSignature[], refine: TypeSignature, tconstrain: TemplateConstraintScope): { overlap: TypeSignature[], remain: TypeSignature[] } | undefined {
        if((src instanceof ErrorTypeSignature)) {
            return { overlap: [], remain: [] };
        }

        const dcr = this.decomposeType(refine);
        if(dcr === undefined) {
            return undefined;
        }
        return this.splitOnTypeDecomposedSet(src, dcr, tconstrain);
    }

    refineType(src: TypeSignature, refine: TypeSignature, tconstrain: TemplateConstraintScope): { overlap: TypeSignature[], remain: TypeSignature[] } | undefined {
        if((src instanceof ErrorTypeSignature) || (refine instanceof ErrorTypeSignature)) {
            return { overlap: [], remain: [] };
        }

        const dct = this.decomposeType(src);
        if(dct === undefined) {
            return undefined;
        }

        const dcr = this.decomposeType(refine);
        if(dcr === undefined) {
            return undefined;
        }
        return this.splitOnTypeDecomposedSet(dct, dcr, tconstrain);
    }

    splitOnNoneDecomposedSet(dcs: TypeSignature[], tconstrain: TemplateConstraintScope): { hasnone: boolean, remainSomeT: TypeSignature | undefined } | undefined {
        if(!dcs.every((t) => (t instanceof NominalTypeSignature) && ((t.decl instanceof SomeTypeDecl) || (t.decl instanceof OptionTypeDecl) || (t.decl instanceof PrimitiveEntityTypeDecl) && t.decl.name === "None"))) {
            return undefined;
        }

        let hasnone = false;
        let someT: TypeSignature | undefined = undefined;
        for(let i = 0; i < dcs.length; ++i) {
            const t = dcs[i] as NominalTypeSignature;

            hasnone = hasnone || this.isSubtypeOf(this.wellknowntypes.get("None") as TypeSignature, t, tconstrain);
            if((t.decl instanceof SomeTypeDecl) || (t.decl instanceof OptionTypeDecl)) {
                const topt = t.alltermargs[0];

                if(someT !== undefined && !this.areSameTypes(someT, topt)) {
                    return undefined;
                }
                someT = topt;
            }
        }

        return { hasnone: hasnone, remainSomeT: someT as TypeSignature };
    }

    splitOnNone(src: TypeSignature, tconstrain: TemplateConstraintScope): { hasnone: boolean, remainSomeT: TypeSignature | undefined } | undefined {
        if(src instanceof ErrorTypeSignature) {
            return { hasnone: false, remainSomeT: undefined };
        }

        const dct = this.decomposeType(src);
        if(dct === undefined) {
            return undefined;
        }
        return this.splitOnNoneDecomposedSet(dct, tconstrain);
    }

    splitOnSomeDecomposedSet(dcs: TypeSignature[], tconstrain: TemplateConstraintScope): { overlapSomeT: TypeSignature | undefined, hasnone: boolean } | undefined {
        if(!dcs.every((t) => (t instanceof NominalTypeSignature) && ((t.decl instanceof SomeTypeDecl) || (t.decl instanceof OptionTypeDecl) || (t.decl instanceof PrimitiveEntityTypeDecl) && t.decl.name === "None"))) {
            return undefined;
        }

        let hasnone = false;
        let someT: TypeSignature | undefined = undefined;
        for(let i = 0; i < dcs.length; ++i) {
            const t = dcs[i] as NominalTypeSignature;

            hasnone = hasnone || this.isSubtypeOf(this.wellknowntypes.get("None") as TypeSignature, t, tconstrain);
            if((t.decl instanceof SomeTypeDecl) || (t.decl instanceof OptionTypeDecl)) {
                const topt = t.alltermargs[0];

                if(someT !== undefined && !this.areSameTypes(someT, topt)) {
                    return undefined;
                }
                someT = topt;
            }
        }

        return { overlapSomeT: someT as TypeSignature, hasnone: hasnone };
    }

    splitOnSome(src: TypeSignature, tconstrain: TemplateConstraintScope): { overlapSomeT: TypeSignature | undefined, hasnone: boolean } | undefined {
        if(src instanceof ErrorTypeSignature) {
            return { overlapSomeT: undefined, hasnone: false };
        }

        const dct = this.decomposeType(src);
        if(dct === undefined) {
            return undefined;
        }
        return this.splitOnSomeDecomposedSet(dct, tconstrain);
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

            if(typeT !== undefined && !this.areSameTypes(typeT, topt)) {
                return undefined;
            }
            typeT = topt;

            if(typeE !== undefined && !this.areSameTypes(typeE, eopt)) {
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

        const dct = this.decomposeType(src);
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

            if(typeT !== undefined && !this.areSameTypes(typeT, topt)) {
                return undefined;
            }
            typeT = topt;

            if(typeE !== undefined && !this.areSameTypes(typeE, eopt)) {
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

        const dct = this.decomposeType(src);
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
            if(!isdeclable) {
                return undefined;
            }
            else {
                return t;
            }
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

    getExpandoableOfType(t: TypeSignature): TypeSignature | undefined {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        if(!(t instanceof NominalTypeSignature)) {
            return undefined;
        }

        xxxx;
        const pexp = t.decl.provides.find((p) => p instanceof NominalTypeSignature && p.decl.ns.ns[0] === "Core" && p.decl.name === "Expandoable");
        const trmp = this.generateTemplateMappingForTypeDecl(t);
        
        return pexp !== undefined ? (pexp as NominalTypeSignature).alltermargs[0].remapTemplateBindings(trmp) : undefined;
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

    resolveStringRegexValidatorInfo(inns: FullyQualifiedNamespace, ttype: TypeSignature): string | undefined {
        if(ttype instanceof NominalTypeSignature) {
            if(ttype.decl instanceof RegexValidatorTypeDecl) {
                return inns.ns.join("::") + "::" + ttype.decl.name;
            }
            else if(ttype.decl instanceof CRegexValidatorTypeDecl) {
                return inns.ns.join("::") + "::" + ttype.decl.name;
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

    resolveTypeConstant(tsig: TypeSignature, name: string, tconstrain: TemplateConstraintScope): MemberLookupInfo<ConstMemberDecl> | undefined {
        if(!(tsig instanceof NominalTypeSignature)) {
            return undefined;
        }

        const cci = tsig.decl.consts.find((c) => c.name === name);
        if(cci !== undefined) {
            const tlinfo = new TypeLookupInfo(tsig, this.generateTemplateMappingForTypeDecl(tsig));
            return new MemberLookupInfo<ConstMemberDecl>(tlinfo, cci);
        }
        else {
            const provides = this.resolveDirectProvidesDecls(tsig);
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
        if(!(tsig instanceof NominalTypeSignature)) {
            return undefined; //TODO: we could potentially resolve fields from unions later
        }

        let cci: MemberFieldDecl | undefined = undefined;
        if(tsig.decl instanceof EntityTypeDecl) {
            cci = tsig.decl.fields.find((c) => c.name === name);
        }
        else if(tsig.decl instanceof ConceptTypeDecl) {
            cci = tsig.decl.fields.find((c) => c.name === name);
        }
        else if(tsig.decl instanceof DatatypeMemberEntityTypeDecl) {
            cci = tsig.decl.fields.find((c) => c.name === name);
        }
        else if(tsig.decl instanceof DatatypeTypeDecl) {
            cci = tsig.decl.fields.find((c) => c.name === name);
        }
        else if(tsig.decl instanceof TaskDecl) {
            cci = tsig.decl.fields.find((c) => c.name === name);
        }
        else {
            if(tsig.decl instanceof TypedeclTypeDecl) {
                if(name === "value") {
                    const valuetype = this.getTypeDeclValueType(tsig);
                    if(valuetype !== undefined) {
                        cci = new MemberFieldDecl(tsig.decl.file, tsig.decl.sinfo, [], "value", valuetype, undefined, true);
                    }
                }
                if(name === "primitive") {
                    const primtype = this.getTypeDeclBasePrimitiveType(tsig);
                    if(primtype !== undefined) {
                        cci = new MemberFieldDecl(tsig.decl.file, tsig.decl.sinfo, [], "primitive", primtype, undefined, true);
                    }
                }
            }
            else if(tsig.decl instanceof StringOfTypeDecl) {
                if(name === "value") {
                    cci = new MemberFieldDecl(tsig.decl.file, tsig.decl.sinfo, [], "value", this.wellknowntypes.get("String") as TypeSignature, undefined, true);
                }
            }
            else if(tsig.decl instanceof CStringOfTypeDecl) {
                if(name === "value") {
                    cci = new MemberFieldDecl(tsig.decl.file, tsig.decl.sinfo, [], "value", this.wellknowntypes.get("CString") as TypeSignature, undefined, true);
                }
            }
            else if(tsig.decl instanceof SomeTypeDecl) {
                if(name === "value") {
                    cci = new MemberFieldDecl(tsig.decl.file, tsig.decl.sinfo, [], "value", tsig.alltermargs[0], undefined, true);
                }
            }
            else if(tsig.decl instanceof OkTypeDecl) {
                if(name === "value") {
                    cci = new MemberFieldDecl(tsig.decl.file, tsig.decl.sinfo, [], "value", tsig.alltermargs[0], undefined, true);
                }
            }
            else if(tsig.decl instanceof ErrTypeDecl) {
                if(name === "error") {
                    cci = new MemberFieldDecl(tsig.decl.file, tsig.decl.sinfo, [], "value", tsig.alltermargs[0], undefined, true);
                }
            }
            else if(tsig.decl instanceof MapEntryTypeDecl) {
                if(name === "key") {
                    cci = new MemberFieldDecl(tsig.decl.file, tsig.decl.sinfo, [], "key", tsig.alltermargs[0], undefined, true);
                }
                if(name === "value") {
                    cci = new MemberFieldDecl(tsig.decl.file, tsig.decl.sinfo, [], "value", tsig.alltermargs[1], undefined, true);
                }
            }
            else {
                ;
            }
        }

        if(cci !== undefined) {
            const tlinfo = new TypeLookupInfo(tsig, this.generateTemplateMappingForTypeDecl(tsig));
            return new MemberLookupInfo<MemberFieldDecl>(tlinfo, cci);
        }
        else {
            const provides = this.resolveDirectProvidesDecls(tsig);
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
        const tn = this.normalize(tsig);

        if(!(tn instanceof NominalTypeSignature)) {
            return undefined; //TODO: we could potentially resolve methods from unions later
        }

        const cci = tn.decl.methods.find((c) => c.name === name);
        if(cci !== undefined && cci.attributes.every((attr) => attr.name !== "override") === undefined) {
            const tlinfo = new TypeLookupInfo(tn, this.generateTemplateMappingForTypeDecl(tn));
            return new MemberLookupInfo<MethodDecl>(tlinfo, cci);
        }
        else {
            const provides = this.resolveDirectProvidesDecls(tn, tconstrain);
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
        const tn = this.normalize(tsig);

        if(!(tn instanceof NominalTypeSignature)) {
            return undefined; //TODO: we could potentially resolve methods from unions later
        }

        const cci = tn.decl.methods.find((c) => c.name === name);
        if(cci !== undefined && cci.attributes.every((attr) => attr.name !== "virtual" && attr.name !== "abstract")) {
            const tlinfo = new TypeLookupInfo(tn, this.generateTemplateMappingForTypeDecl(tn));
            return new MemberLookupInfo<MethodDecl>(tlinfo, cci);
        }
        else {
            const provides = this.resolveDirectProvidesDecls(tn, tconstrain);
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
        const tn = this.normalize(tsig);

        if(!(tn instanceof NominalTypeSignature)) {
            return undefined; //TODO: we could potentially resolve methods from unions later
        }

        const cci = tn.decl.functions.find((c) => c.name === name);
        if(cci !== undefined) {
            const tlinfo = new TypeLookupInfo(tn, this.generateTemplateMappingForTypeDecl(tn));
            return new MemberLookupInfo<TypeFunctionDecl>(tlinfo, cci);
        }
        else {
            const provides = this.resolveDirectProvidesDecls(tn, tconstrain);
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

    private static addResolvedTLookup(tlookup: TypeLookupInfo, current: TypeLookupInfo[]): void {
        const found = current.find((c) => c.tsig.decl === tlookup.tsig.decl && TemplateNameMapper.identicalMappings(c.mapping, tlookup.mapping));
        if(found === undefined) {
            current.push(tlookup);
        }
    }

    //get all of the actual fields that are provided via inheritance
    resolveTransitiveProvidesDecls(ttype: TypeSignature, tconstrain: TemplateConstraintScope): TypeLookupInfo[] {
        const dprovides = this.resolveDirectProvidesDecls(ttype, tconstrain);

        let pdecls: TypeLookupInfo[] = [];
        for(let i = 0; i < dprovides.length; ++i) {
            const pinfo = dprovides[i];
            
            TypeCheckerRelations.addResolvedTLookup(pinfo, pdecls);

            const tprovides = this.resolveTransitiveProvidesDecls(pinfo.tsig.remapTemplateBindings(pinfo.mapping), tconstrain);
            for(let j = 0; j < tprovides.length; ++j) {
                TypeCheckerRelations.addResolvedTLookup(tprovides[j], pdecls);
            }
        }

        return pdecls;
    }

    //get all of the actual fields that are provided via inheritance
    resolveAllInheritedFieldDecls(ttype: TypeSignature, tconstrain: TemplateConstraintScope): MemberLookupInfo<MemberFieldDecl>[] {
        const pdecls = this.resolveTransitiveProvidesDecls(ttype, tconstrain);

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
                ;
            }
        }

        return allfields;
    }

    generateAllFieldBNamesInfo(ttype: NominalTypeSignature, tconstrain: TemplateConstraintScope, mfields: MemberFieldDecl[]): {name: string, type: TypeSignature}[] {
        const ifields = this.resolveAllInheritedFieldDecls(ttype, tconstrain);

        const ibnames = ifields.map((mf) => { return {name: mf.member.name, type: mf.member.declaredType.remapTemplateBindings(mf.typeinfo.mapping)}; });
        const mbnames = mfields.map((mf) => { return {name: mf.name, type: mf.declaredType}; });

        return [...ibnames, ...mbnames];
    }

    generateAllFieldBNamesInfoWOptInitializer(ttype: NominalTypeSignature, tconstrain: TemplateConstraintScope, mfields: MemberFieldDecl[]): {name: string, type: TypeSignature, hasdefault: boolean}[] {
        const ifields = this.resolveAllInheritedFieldDecls(ttype, tconstrain);

        const ibnames = ifields.map((mf) => { return {name: mf.member.name, type: mf.member.declaredType.remapTemplateBindings(mf.typeinfo.mapping), hasdefault: mf.member.defaultValue !== undefined}; });
        const mbnames = mfields.map((mf) => { return {name: mf.name, type: mf.declaredType, hasdefault: mf.defaultValue !== undefined}; });

        return [...ibnames, ...mbnames];
    }

    //get all of the actual fields that are provided via inheritance
    resolveAllInheritedValidatorDecls(ttype: TypeSignature, tconstrain: TemplateConstraintScope): {invariants: MemberLookupInfo<InvariantDecl>[], validators: MemberLookupInfo<ValidateDecl>[]} {
        const pdecls = this.resolveTransitiveProvidesDecls(ttype, tconstrain);

        let allinvariants: MemberLookupInfo<InvariantDecl>[] = [];
        let allvalidators: MemberLookupInfo<ValidateDecl>[] = [];
        for(let i = 0; i < pdecls.length; ++i) {
            const pdecl = pdecls[i];

            allinvariants = allinvariants.concat(pdecl.tsig.decl.invariants.map((f) => new MemberLookupInfo<InvariantDecl>(pdecl, f)));
            allvalidators = allvalidators.concat(pdecl.tsig.decl.validates.map((f) => new MemberLookupInfo<ValidateDecl>(pdecl, f)));
        }

        return {invariants: allinvariants, validators: allvalidators};
    }

    hasChecksOnConstructor(ttype: NominalTypeSignature, tconstrain: TemplateConstraintScope): boolean {
        if(ttype.decl.validates.length !== 0 || ttype.decl.invariants.length !== 0) {
            return true;
        }

        const ichecks = this.resolveAllInheritedValidatorDecls(ttype, tconstrain);
        return ichecks.invariants.length !== 0 || ichecks.validators.length !== 0;
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
