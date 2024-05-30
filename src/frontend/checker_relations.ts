import {strict as assert} from "assert";

import { EListTypeSignature, ErrorTypeSignature, FullyQualifiedNamespace, NominalTypeSignature, TemplateConstraintScope, TemplateNameMapper, TemplateTypeSignature, TypeSignature } from "./type";
import { AbstractNominalTypeDecl, MemberFieldDecl, NamespaceDeclaration } from "./assembly";
import { AccessNamespaceConstantExpression, AccessStaticFieldExpression, Expression } from "./body";

class TypeLookupInfo {
    readonly ttype: AbstractNominalTypeDecl;
    readonly mapping: TemplateNameMapper;

    constructor(ttype: AbstractNominalTypeDecl,  mapping: TemplateNameMapper) {
        this.ttype = ttype;
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

abstract class RegexValidatorPack {
}

class SingleRegexValidatorPack extends RegexValidatorPack {
    readonly vre: string;

    constructor(vre: string) {
        super();
        this.vre = vre;
    }
}

class AndRegexValidatorPack extends RegexValidatorPack {
    readonly validators: RegexValidatorPack[];

    constructor(validators: RegexValidatorPack[]) {
        super();
        this.validators = validators;
    }
}

class OrRegexValidatorPack extends RegexValidatorPack {
    readonly validators: RegexValidatorPack[];

    constructor(validators: RegexValidatorPack[]) {
        super();
        this.validators = validators;
    }
}

class TypeCheckerRelations {
    refineType(src: TypeSignature, refine: TypeSignature): { overlap: TypeSignature | undefined, remain: TypeSignature | undefined } {
        //If src is an error then just return error for both
        if(src instanceof ErrorTypeSignature) {
            return { overlap: src, remain: src };
        }

        //If the refinement is indeterminate (an error) then just nop and return src as the option for both
        if(refine instanceof ErrorTypeSignature) {
            return { overlap: src, remain: src };
        }


        //now do the actual cases
        xxxx;
    }

    //Check is t1 is a subtype of t2
    isSubtypeOf(t1: TypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert((t1 instanceof ErrorTypeSignature) || (t2 instanceof ErrorTypeSignature), "Checking subtypes on errors");

        xxxx;
    }

    //Check if t1 and t2 are the same type
    areSameTypes(t1: TypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert((t1 instanceof ErrorTypeSignature) || (t2 instanceof ErrorTypeSignature), "Checking subtypes on errors");

        xxxx;
    }

    //Check if t1 is the type None (exactly)
    isNoneType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        xxxx;
    }

    //Check if t includes None (e.g. None is a subtype of t)
    includesNoneType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        xxxx;
    }

    //Check if t1 is the type Nothing (exactly)
    isNothingType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        xxxx;
    }

    //Check if t incudes Nothing (e.g. Nothing is a subtype of t)
    includesNothingType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        xxxx;
    }

    //Check if t is the type Bool (exactly)
    isBooleanType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    //Check if t is the type Void (exactly)
    isVoidType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    //Check is this type is unique (i.e. not a union or concept type)
    isUniqueType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    //Check if this type is unique and a numeric type of some sort (either primitive number or a typedecl of a numeric type)
    isUniqueNumericType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        
        //check special TNumeric template as well as the specific possibilities
        xxxx;
    }

    //Check if this type is a primitive type in Core
    isPrimitiveType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    //Check if this type is a typedecl of some sort
    isTypeDeclType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    //Get the base primitive type of a typedecl (resolving through typedecls and aliases as needed)
    getTypeDeclBasePrimitiveType(t: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    //Check if this type is a valid type to have as a provids type -- must be a unique CONCEPT type
    isValidProvidesType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    //Check if this type is a KeyType (e.g. a subtype of KeyType)
    isKeyType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    //If possible resolve this type as an elist type
    tryResolveAsEListType(vtype: TypeSignature, tconstrain: TemplateConstraintScope): EListTypeSignature | undefined {
        xxxx;
    }

    getStringOfType(vtype: TypeSignature): TypeSignature {
        //TODO: given a validator type return a StringOf<vtype> type reference
        xxxx;
    }

    getASCIIStringOfType(vtype: TypeSignature): TypeSignature {
        //TODO: given a validator type return a StringOf<vtype> type reference
        xxxx;
    }

    getEventListOf(vtype: TypeSignature): TypeSignature {
        //return the event list type of the given type
        xxxx;
    }

    getNominalTypeForDecl(enclns: NamespaceDeclaration, tdecl: AbstractNominalTypeDecl): TypeSignature {
        const tterms = tdecl.terms.map((tterm) => new TemplateTypeSignature(tdecl.sinfo, tterm.name));
        return new NominalTypeSignature(tdecl.sinfo, enclns.fullnamespace.ns, [{tname: tdecl.name, terms: tterms}], [{name: "T", type: new TemplateTypeSignature(tdecl.sinfo, "T")}], undefined, tdecl)
    }

    getNominalTypeForNestedDecl(enclns: NamespaceDeclaration, encldecl: AbstractNominalTypeDecl, tdecl: AbstractNominalTypeDecl): TypeSignature {
        xxxx; //for the nested API adn APIResult types
    }

    compileTimeReduceConstantExpression(exp: Expression): [Expression, TypeSignature | undefined, TemplateNameMapper] | undefined {
        if(exp.isLiteralExpression()) {
            return [exp, undefined, TemplateNameMapper.createEmpty()];
        }
        else if (exp instanceof AccessNamespaceConstantExpression) {
            const nsresl = this.resolveNamespaceConstant(exp.ns, exp.name);
            if(nsresl === undefined) {
                return undefined;
            }

            const nresolve = this.compileTimeReduceConstantExpression(nsresl.value.exp);
            if(nresolve === undefined) {
                return undefined;
            }

            return [nresolve[0], nsresl.declaredType, TemplateNameMapper.createEmpty()];
        }
        else if (exp instanceof AccessStaticFieldExpression) {
            if(this.resolveEnumName(exp.stype, exp.name) !== undefined) {
                return [exp, exp.stype, TemplateNameMapper.createEmpty()];
            }
            else
            {
                const cdecl = this.resolveTypeConstant(exp.stype, exp.name);
                if(cdecl === undefined) {
                    return undefined;
                }

                const nresolve = this.compileTimeReduceConstantExpression(cdecl.member.value.exp);
                if(nresolve === undefined) {
                    return undefined;
                }

                return [nresolve[0], cdecl.member.declaredType, cdecl.mapping];
            }
        }
        else {
            return undefined;
        }
    }

    resolveStringRegexValidatorInfo(ttype: TypeSignature): RegexValidatorPack | undefined {
        //TODO: from the assembly resolve the 
        xxxx;
    }

    resolveNamespaceConstant(ns: FullyQualifiedNamespace, name: string): NamespaceConstDecl | undefined {
        xxxx;
    }

    resolveNamespaceFunction(ns: FullyQualifiedNamespace, name: string): NamespaceFunctionDecl | undefined {
        xxxx;
    }

    resolveEnumName(tsig: TypeSignature, name: string): MemberLookupInfo<string> | undefined {
        xxxx;
    }

    resolveTypeConstant(tsig: TypeSignature, name: string): MemberLookupInfo<ConstMemberDecl> | undefined {
        xxxx;
    }

    resolveTypeField(tsig: TypeSignature, name: string): MemberLookupInfo<MemberFieldDecl> | undefined {
        xxxx;
    }

    resolveTypeMethodDeclaration(tsig: TypeSignature, name: string): MemberLookupInfo<MemberMethodDecl> | undefined {
        xxxx;
    }

    resolveTypeMethodImplementation(tsig: TypeSignature, name: string): MemberLookupInfo<MemberMethodDecl> | undefined {
        xxxx;
    }

    resolveTypeFunction(ns: FullyQualifiedNamespace, name: string): MemberLookupInfo<TypeFunctionDecl> | undefined {
        xxxx;
    }

    //get all of the actual concepts + template mappings that are provided by a type
    resolveAllProvidesDecls(provides: TypeSignature[], tconstrain: TemplateConstraintScope): TypeLookupInfo[] {
        xxxx;
    }

    //get all of the actual fields that are provided via inheritance
    resolveAllInheritedFieldDecls(provides: TypeSignature[], tconstrain: TemplateConstraintScope): MemberLookupInfo<MemberFieldDecl>[] {
        xxxx;
    }

    generateAllFieldBNamesInfo(tdecl: AbstractNominalTypeDecl, mfields: MemberFieldDecl[], tconstrain: TemplateConstraintScope): {name: string, type: TypeSignature}[] {
        const ifields = this.resolveAllInheritedFieldDecls(tdecl.provides, tconstrain);

        const ibnames = ifields.map((mf) => { return {name: mf.member.name, type: mf.member.declaredType.remapTemplateBindings(mf.typeinfo.mapping)}; });
        const mbnames = mfields.map((mf) => { return {name: mf.name, type: mf.declaredType}; });

        return [...ibnames, ...mbnames];
    }

    //Compute the upper bound of two types for use in control-flow join types
    joinTypes(t1: TypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        assert(t1 instanceof ErrorTypeSignature, "Checking subtypes on errors");
        assert(t2 instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }
}


/*
    getAllOOFields(ttype: TypeSignature, ooptype: OOPTypeDecl, oobinds: Map<string, ResolvedType>, fmap?: Map<string, [ResolvedType, OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>): Map<string, [ResolvedType, OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]> {
        assert(!ooptype.attributes.includes("__constructable"), "Needs to be handled as special case");

        let declfields = fmap || new Map<string, [ResolvedType, OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>();

        //Important to do traversal in Left->Right Topmost traversal order
        const rprovides = this.resolveProvides(ooptype, TemplateBindScope.createBaseBindScope(oobinds));
        rprovides.forEach((provide) => {
            const concept = (provide.options[0] as ResolvedConceptAtomType).conceptTypes[0];
            declfields = this.getAllOOFields(provide, concept.concept, concept.binds, declfields);
        });

        ooptype.memberFields.forEach((mf) => {
            if (!declfields.has(mf.name)) {
                declfields.set(mf.name, [ttype, ooptype, mf, oobinds]);
            }
        });

        return declfields;
    }

    getAllInvariantProvidingTypesInherit(ttype: ResolvedType, ooptype: OOPTypeDecl, oobinds: Map<string, ResolvedType>, invprovs?: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][]): [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][] {
        let declinvs: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][] = [...(invprovs || [])];

        if (declinvs.find((dd) => dd[0].typeID === ttype.typeID)) {
            return declinvs;
        }

        const rprovides = this.resolveProvides(ooptype, TemplateBindScope.createBaseBindScope(oobinds));
        rprovides.forEach((provide) => {
            const concept = (provide.options[0] as ResolvedConceptAtomType).conceptTypes[0];
            declinvs = this.getAllInvariantProvidingTypesInherit(provide, concept.concept, concept.binds, declinvs);
        });


        if (ooptype.invariants.length !== 0 || ooptype.validates.length !== 0) {
            declinvs.push([ttype, ooptype, oobinds]);
        }

        return declinvs;
    }

    getAllInvariantProvidingTypesTypedecl(ttype: ResolvedType, ooptype: OOPTypeDecl, oobinds: Map<string, ResolvedType>, invprovs?: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][]): [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][] {
        let declinvs: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][] = [...(invprovs || [])];

        if (declinvs.find((dd) => dd[0].typeID === ttype.typeID)) {
            return declinvs;
        }

        if (ttype.tryGetUniqueEntityTypeInfo() instanceof ResolvedTypedeclEntityAtomType) {
            const ccdecl = ttype.tryGetUniqueEntityTypeInfo() as ResolvedTypedeclEntityAtomType;
            const oftype = ResolvedType.createSingle(ccdecl.valuetype);

            declinvs = this.getAllInvariantProvidingTypesTypedecl(oftype, ccdecl.valuetype.object, ccdecl.valuetype.getBinds(), declinvs);
        }

        if ((ooptype.invariants.length !== 0 || ooptype.validates.length !== 0)
            || (ooptype.attributes.includes("__stringof_type") || ooptype.attributes.includes("__asciistringof_type"))
            || (ooptype.attributes.includes("__path_type") || ooptype.attributes.includes("__pathfragment_type") || ooptype.attributes.includes("__pathglob_type"))
        ) {
            declinvs.push([ttype, ooptype, oobinds]);
        }

        return declinvs;
    }

    entityTypeConstructorHasInvariants(ttype: ResolvedType, ooptype: OOPTypeDecl, oobinds: Map<string, ResolvedType>): boolean {
        const ccdecls = this.getAllInvariantProvidingTypesInherit(ttype, ooptype, oobinds);
        return ccdecls.some((ccd) => {
            return ccd[1].invariants.some((ii) => isBuildLevelEnabled(ii.level, this.m_buildLevel));
        });
    }

    typedeclTypeConstructorHasInvariants(ttype: ResolvedType, ooptype: OOPTypeDecl): boolean {
        const ccdecls = this.getAllInvariantProvidingTypesTypedecl(ttype, ooptype, new Map<string, ResolvedType>());
        return ccdecls.some((ccd) => {
            return ccd[1].invariants.some((ii) => isBuildLevelEnabled(ii.level, this.m_buildLevel));
        });
    }

    typedeclTypeConstructorFromValueHasInvariants(ttype: ResolvedType, ooptype: OOPTypeDecl): boolean {
        const ccdecls = this.getAllInvariantProvidingTypesTypedecl(ttype, ooptype, new Map<string, ResolvedType>());
        return ccdecls.some((ccd) => {
            return ccd[1].invariants.some((ii) => isBuildLevelEnabled(ii.level, this.m_buildLevel));
        });
    }

    ////
    //Type representation, normalization, and operations
    private resolveTemplateBinds(sinfo: SourceInfo, declterms: TemplateTermDecl[], giventerms: TypeSignature[], binds: TemplateBindScope): Map<string, ResolvedType> {
        let fullbinds = new Map<string, ResolvedType>();

        for (let i = 0; i < declterms.length; ++i) {
            const ttype = this.normalizeTypeOnly(giventerms[i], binds);
            this.raiseErrorIf(sinfo, ttype.isInvalidType(), `Could not resolve template for ${declterms[i].name} given binding as ${giventerms[i].getDiagnosticName()}`)

            fullbinds.set(declterms[i].name, ttype);
        }

        return fullbinds;
    }

    private tryGetMemberImpl_helper<T extends OOMemberDecl>(ttype: ResolvedType, ooptype: OOPTypeDecl, oobinds: Map<string, ResolvedType>, fnlookup: (tt: OOPTypeDecl) => T | undefined): OOMemberLookupInfo<T>[] | ResolveResultFlag {
        const mdecl = fnlookup(ooptype);
        if(mdecl !== undefined) {
            if(mdecl.hasAttribute("abstract")) {
                return ResolveResultFlag.notfound;
            }
            else {
                return [new OOMemberLookupInfo<T>(ttype, ooptype, oobinds, mdecl)];
            }
        }

        const rprovides = this.resolveProvides(ooptype, TemplateBindScope.createBaseBindScope(oobinds));
        if(rprovides.length === 0) {
            return ResolveResultFlag.notfound;
        }

        const options = rprovides.map((provide) => {
            const concept = (provide.options[0] as ResolvedConceptAtomType).conceptTypes[0];
            return this.tryGetMemberImpl_helper<T>(provide, concept.concept, concept.binds, fnlookup);
        })
        .filter((opt) => Array.isArray(opt));

        let impls: OOMemberLookupInfo<T>[] = [];
        for(let i = 0; i < options.length; ++i) {
            const newopts = (options[i] as OOMemberLookupInfo<T>[]).filter((opt) => !impls.some((info) => info.ttype.typeID === opt.ttype.typeID));
            impls.push(...newopts);
        }

        return impls;
    }

    private tryGetMemberDecls_helper<T extends OOMemberDecl>(name: string, ttype: ResolvedType, ooptype: OOPTypeDecl, oobinds: Map<string, ResolvedType>, fnlookup: (tt: OOPTypeDecl) => T | undefined): OOMemberLookupInfo<T>[] | ResolveResultFlag {
        const mdecl = fnlookup(ooptype);
        if(mdecl !== undefined) {
            if(mdecl.hasAttribute("abstract") || mdecl.hasAttribute("virtual")) {
                return [new OOMemberLookupInfo<T>(ttype, ooptype, oobinds, mdecl)];
            }
        }

        const rprovides = this.resolveProvides(ooptype, TemplateBindScope.createBaseBindScope(oobinds));
        if(rprovides.length === 0) {
            return ResolveResultFlag.notfound;
        }

        const options = rprovides.map((provide) => {
            const concept = (provide.options[0] as ResolvedConceptAtomType).conceptTypes[0];
            return this.tryGetMemberDecls_helper<T>(name, provide, concept.concept, concept.binds, fnlookup);
        });

        if(options.includes(ResolveResultFlag.failure)) {
            return ResolveResultFlag.failure;
        }

        if (options.includes(ResolveResultFlag.notfound)) {
            if (mdecl !== undefined && !mdecl.hasAttribute("override")) {
                return [new OOMemberLookupInfo<T>(ttype, ooptype, oobinds, mdecl)];
            }
        }

        const ropts = options.filter((opt) => opt !== ResolveResultFlag.failure && opt !== ResolveResultFlag.notfound) as OOMemberLookupInfo<T>[][];
        if(ropts.length === 0) {
            return ResolveResultFlag.notfound;
        }

        let decls: OOMemberLookupInfo<T>[] = [];
        for(let i = 0; i < ropts.length; ++i) {
            const newopts = ropts[i].filter((opt) => !decls.some((info) => info.ttype.typeID === opt.ttype.typeID));
            decls.push(...newopts);
        }

        return decls;
    }

    //When resolving a member on a concept we must find a unique decl and 0 or more implementations
    //const/function/field lookups will assert that an implementation was found -- method/operator lookups may be dynamic and just find a declration
    resolveMemberFromConceptAtom<T extends OOMemberDecl> (sinfo: SourceInfo, ttype: ResolvedType, atom: ResolvedConceptAtomType, name: string, fnlookup: (tt: OOPTypeDecl) => T | undefined): OOMemberResolution<T> | ResolveResultFlag {
        //decls
        const declsopts = atom.conceptTypes
            .map((cpt) => this.tryGetMemberDecls_helper(name, ResolvedType.createSingle(ResolvedConceptAtomType.create([cpt])), cpt.concept, cpt.binds, fnlookup))
            .filter((opt) => opt !== ResolveResultFlag.notfound);

        //Lookup failed
        if(declsopts.some((opt) => opt === ResolveResultFlag.failure)) {
            return ResolveResultFlag.failure;
        }

        let decls: OOMemberLookupInfo<T>[] = [];
        for (let i = 0; i < declsopts.length; ++i) {
            const newopts = (declsopts[i] as OOMemberLookupInfo<T>[]).filter((opt) => !decls.some((info) => info.ttype.typeID === opt.ttype.typeID));
            decls.push(...newopts);
        }

        if (decls.length === 0) {
            this.raiseError(sinfo, `Missing declaraton for ${name} on type ${atom.typeID}`);
            return ResolveResultFlag.failure;
        }

        if (decls.length > 1) {
            this.raiseError(sinfo, `Multiple declaratons possible for ${name} on type ${atom.typeID}`);
            return ResolveResultFlag.failure;
        }

        //impls
        const implopts = atom.conceptTypes
            .map((cpt) => this.tryGetMemberImpl_helper(ResolvedType.createSingle(ResolvedConceptAtomType.create([cpt])), cpt.concept, cpt.binds, fnlookup))
            .filter((opt) => opt !== ResolveResultFlag.notfound);

        //Lookup failed
        if(implopts.some((opt) => opt === ResolveResultFlag.failure)) {
            return ResolveResultFlag.failure;
        }

        //ok not to find an implementation

        let impls: OOMemberLookupInfo<T>[] = [];
        for (let i = 0; i < implopts.length; ++i) {
            const newopts = (implopts[i] as OOMemberLookupInfo<T>[]).filter((opt) => !impls.some((info) => info.ttype.typeID === opt.ttype.typeID));
            impls.push(...newopts);
        }

        return new OOMemberResolution<T>(decls[0], impls, impls.length > 0);
    }

    //When resolving a member on an entity we must find a unique decl and a unique or more implementation
    //const/function/field/method lookups will assert that an implementation was found
    resolveMemberFromEntityAtom<T extends OOMemberDecl> (sinfo: SourceInfo, ttype: ResolvedType, atom: ResolvedEntityAtomType, name: string, fnlookup: (tt: OOPTypeDecl) => T | undefined): OOMemberResolution<T> | ResolveResultFlag {
        //decls
        const decls = this.tryGetMemberDecls_helper(name, ResolvedType.createSingle(atom), atom.object, atom.getBinds(), fnlookup);
        
        //Lookup failed
        if(decls === ResolveResultFlag.notfound) {
            this.raiseError(sinfo, `Cannot resolve ${name} on type ${atom.typeID}`);
            return ResolveResultFlag.failure;
        }

        if(decls === ResolveResultFlag.failure) {
            return ResolveResultFlag.failure;
        }

        if (decls.length === 0) {
            this.raiseError(sinfo, `Missing declaraton for ${name} on type ${atom.typeID}`);
            return ResolveResultFlag.failure;
        }

        if (decls.length > 1) {
            this.raiseError(sinfo, `Multiple declaratons possible for ${name} on type ${atom.typeID}`);
            return ResolveResultFlag.failure;
        }

        //impls
        const impls = this.tryGetMemberImpl_helper(ResolvedType.createSingle(atom), atom.object, atom.getBinds(), fnlookup);

        //Lookup failed
        if(impls === ResolveResultFlag.failure) {
            return ResolveResultFlag.failure;
        }

        return new OOMemberResolution<T>(decls[0], impls !== ResolveResultFlag.notfound ? impls : [], impls !== ResolveResultFlag.notfound);
    }

    //When resolving a member on an task we must find a unique decl and implementation
    //const/function lookups will assert that an implementation was found
    resolveMemberFromTaskAtom<T extends OOMemberDecl> (sinfo: SourceInfo, ttype: ResolvedType, atom: ResolvedTaskAtomType, name: string, fnlookup: (tt: OOPTypeDecl) => T | undefined): OOMemberResolution<T> | ResolveResultFlag {
        //decls
        const decls = this.tryGetMemberDecls_helper(name, ResolvedType.createSingle(atom), atom.task, atom.binds, fnlookup);
        
        //Lookup failed
        if(decls === ResolveResultFlag.notfound) {
            this.raiseError(sinfo, `Cannot resolve ${name} on type ${atom.typeID}`);
            return ResolveResultFlag.failure;
        }

        if(decls === ResolveResultFlag.failure) {
            return ResolveResultFlag.failure;
        }

        if (decls.length === 0) {
            this.raiseError(sinfo, `Missing declaraton for ${name} on type ${atom.typeID}`);
            return ResolveResultFlag.failure;
        }

        if (decls.length > 1) {
            this.raiseError(sinfo, `Multiple declaratons possible for ${name} on type ${atom.typeID}`);
            return ResolveResultFlag.failure;
        }

        //impls
        const impls = this.tryGetMemberImpl_helper(ResolvedType.createSingle(atom), atom.task, atom.binds, fnlookup);

        //Lookup failed
        if(impls === ResolveResultFlag.failure) {
            return ResolveResultFlag.failure;
        }

        return new OOMemberResolution<T>(decls[0], impls !== ResolveResultFlag.notfound ? impls : [], impls !== ResolveResultFlag.notfound);
    }

    resolveMember<T extends OOMemberDecl>(sinfo: SourceInfo, ttype: ResolvedType, name: string, fnlookup: (tt: OOPTypeDecl) => T | undefined): OOMemberResolution<T> | ResolveResultFlag {
        const sopts = ttype.options.map((atom) => {
            if (atom instanceof ResolvedEntityAtomType) {
                return this.resolveMemberFromEntityAtom<T>(sinfo, ResolvedType.createSingle(atom), atom, name, fnlookup);
            }
            else if(atom instanceof ResolvedTaskAtomType) {
                return this.resolveMemberFromTaskAtom(sinfo, ResolvedType.createSingle(atom), atom, name, fnlookup);
            }
            else if (atom instanceof ResolvedConceptAtomType) {
                return this.resolveMemberFromConceptAtom<T>(sinfo, ResolvedType.createSingle(atom), atom, name, fnlookup);
            }
            else {
                this.raiseError(sinfo, `Cannot resolve ${name} on type ${atom.typeID}`);
                return ResolveResultFlag.failure;
            }
        });

        if(sopts.some((opt) => opt === ResolveResultFlag.failure)) {
            return ResolveResultFlag.failure;
        }

        let decls: OOMemberLookupInfo<T>[] = [];
        let impls: OOMemberLookupInfo<T>[] = [];
        let totalresolve = true;
        for (let i = 0; i < sopts.length; ++i) {
            const declopt = (sopts[i] as OOMemberResolution<T>).decl;
            const implopts = (sopts[i] as OOMemberResolution<T>).impl;

            if(!decls.some((info) => info.ttype.typeID === declopt.ttype.typeID)) {
                decls.push(declopt);
            }

            const newimpls = implopts.filter((opt) => !impls.some((info) => info.ttype.typeID === opt.ttype.typeID));;
            impls.push(...newimpls);

            totalresolve = totalresolve && (sopts[i] as OOMemberResolution<T>).totalimpls;
        }

        if(decls.length !== 1) {
            this.raiseError(sinfo, `Multiple declaratons possible for ${name} on type ${ttype.typeID}`);
            return ResolveResultFlag.failure;
        }

        return new OOMemberResolution<T>(decls[0], impls, totalresolve);
    }

    resolveMemberConst(sinfo: SourceInfo, ttype: ResolvedType, name: string): OOMemberLookupInfo<StaticMemberDecl> | undefined {
        const resl = this.resolveMember<StaticMemberDecl>(sinfo, ttype, name, (tt: OOPTypeDecl) => tt.staticMembers.find((sm) => sm.name === name));
        if(resl === ResolveResultFlag.failure || resl === ResolveResultFlag.notfound) {
            return undefined;
        }

        if(!resl.totalimpls) {
            return undefined;
        }

        if(resl.impl.length !== 1) {
            this.raiseError(sinfo, `Multuple constant values found for ${name} on type ${ttype.typeID} -- ${resl.impl.map((ii) => ii.ttype.typeID).join(", ")}`);
            return undefined;
        }

        return resl.impl[0];
    }

    resolveMemberFunction(sinfo: SourceInfo, ttype: ResolvedType, name: string): OOMemberLookupInfo<StaticFunctionDecl> | undefined {
        const resl = this.resolveMember<StaticFunctionDecl>(sinfo, ttype, name, (tt: OOPTypeDecl) => tt.staticFunctions.find((sf) => sf.name === name));
        if(resl === ResolveResultFlag.failure || resl === ResolveResultFlag.notfound) {
            return undefined;
        }

        if(!resl.totalimpls) {
            return undefined;
        }

        if(resl.impl.length !== 1) {
            this.raiseError(sinfo, `Multuple member function implementations found for ${name} on type ${ttype.typeID} -- ${resl.impl.map((ii) => ii.ttype.typeID).join(", ")}`);
            return undefined;
        }

        return resl.impl[0];
    }

    resolveMemberField(sinfo: SourceInfo, ttype: ResolvedType, name: string): OOMemberLookupInfo<MemberFieldDecl> | undefined {
        const resl = this.resolveMember<MemberFieldDecl>(sinfo, ttype, name, (tt: OOPTypeDecl) => tt.memberFields.find((sm) => sm.name === name));
        if(resl === ResolveResultFlag.failure || resl === ResolveResultFlag.notfound) {
            return undefined;
        }

        if(!resl.totalimpls) {
            return undefined;
        }

        if(resl.impl.length !== 1) {
            this.raiseError(sinfo, `Multuple member field versions found for ${name} on type ${ttype.typeID} -- ${resl.impl.map((ii) => ii.ttype.typeID).join(", ")}`);
            return undefined;
        }

        return resl.impl[0];
    }

    resolveMemberMethod(sinfo: SourceInfo, ttype: ResolvedType, name: string): OOMemberResolution<MemberMethodDecl> | undefined {
        const resl = this.resolveMember<MemberMethodDecl>(sinfo, ttype, name, (tt: OOPTypeDecl) => tt.memberMethods.find((mf) => mf.name === name));
        if(resl === ResolveResultFlag.failure || resl === ResolveResultFlag.notfound) {
            return undefined;
        }

        return resl;
    }

    resolveProvides(tt: OOPTypeDecl, binds: TemplateBindScope): ResolvedType[] {
        let scpt: [ResolvedConceptAtomTypeEntry, TypeConditionRestriction | undefined][] = [];
        for (let i = 0; i < tt.provides.length; ++i) {
            const rsig = this.normalizeTypeOnly(tt.provides[i][0], binds);
            if(rsig.options.length !== 1 || !(rsig.options[0] instanceof ResolvedConceptAtomType)) {
                this.raiseError(tt.sourceLocation, `provides types must be a concept -- got ${rsig.typeID}`);
                return [];
            }

            const flatcpts = rsig.options[0].conceptTypes.map((rcpte) => [rcpte, tt.provides[i][1]] as [ResolvedConceptAtomTypeEntry, TypeConditionRestriction | undefined]);
            scpt.push(...flatcpts)
        }


        let oktypes: ResolvedType[] = [];
        
        for (let i = 0; i < scpt.length; ++i) {
            const rsig = ResolvedType.createSingle(ResolvedConceptAtomType.create([scpt[i][0]]));
            const pcond = scpt[i][1];
            if(pcond === undefined) {
                oktypes.push(rsig);
            }
            else {
                const allok = pcond.constraints.every((consinfo) => {
                    const constype = this.normalizeTypeOnly(consinfo.t, binds)
                    return this.subtypeOf(constype, this.normalizeTypeOnly(consinfo.tconstraint, binds));
                });

                if(allok) {
                    oktypes.push(rsig);
                }
            }
        }

        return oktypes;
    }
    */

export {
    RegexValidatorPack, SingleRegexValidatorPack, AndRegexValidatorPack, OrRegexValidatorPack,
    TypeLookupInfo, MemberLookupInfo,
    TypeCheckerRelations
};
