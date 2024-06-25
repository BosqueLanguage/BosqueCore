import assert from "node:assert";

import { AutoTypeSignature, EListTypeSignature, ErrorTypeSignature, FullyQualifiedNamespace, LambdaParameterSignature, LambdaTypeSignature, NominalParsedTypeSignature, NominalTypeSignature, NoneableTypeSignature, RecordTypeSignature, NominalResolvedTypeSignature, StringTemplateTypeSignature, TemplateConstraintScope, TemplateNameMapper, TemplateTypeSignature, TupleTypeSignature, TypeSignature, UnionTypeSignature, VoidTypeSignature } from "./type.js";
import { AbstractConceptTypeDecl, AbstractEntityTypeDecl, AbstractNominalTypeDecl, AdditionalTypeDeclTag, Assembly, ConceptTypeDecl, ConstMemberDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, EntityTypeDecl, EnumTypeDecl, ErrTypeDecl, CRegexValidatorTypeDecl, InternalEntityTypeDecl, MemberFieldDecl, MethodDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, OkTypeDecl, OptionTypeDecl, PathValidatorTypeDecl, PrimitiveEntityTypeDecl, RegexValidatorTypeDecl, ResultTypeDecl, SomethingTypeDecl, TaskDecl, TemplateTermDeclExtraTag, TypeFunctionDecl, TypedeclTypeDecl } from "./assembly.js";
import { SourceInfo } from "./build_decls.js";
import { EListStyleTypeInferContext, SimpleTypeInferContext, TypeInferContext } from "./checker_environment.js";

class TypeLookupInfo {
    readonly tsig: TypeSignature;
    readonly ttype: AbstractNominalTypeDecl;
    readonly mapping: TemplateNameMapper;

    constructor(tsig: TypeSignature, ttype: AbstractNominalTypeDecl,  mapping: TemplateNameMapper) {
        this.tsig = tsig;
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

class ErrorRegexValidatorPack extends RegexValidatorPack {
}

class SingleRegexValidatorPack extends RegexValidatorPack {
    readonly vre: string;

    constructor(vre: string) {
        super();
        this.vre = vre;
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
    readonly assembly: Assembly;
    readonly wellknowntypes: Map<string, TypeSignature>;

    readonly memoizedTypeEqualRelation: Map<string, boolean> = new Map<string, boolean>();
    readonly memoizedTypeSubtypeRelation: Map<string, boolean> = new Map<string, boolean>();

    constructor(assembly: Assembly, wellknowntypes: Map<string, TypeSignature>) {
        this.assembly = assembly;
        this.wellknowntypes = wellknowntypes;
    }

    static computeNameMapperFromDirectNominalParserTypeSignatureInfo(nsig: NominalParsedTypeSignature): TemplateNameMapper {
        let mapping = new Map<string, TypeSignature>();

        const sigterms: TypeSignature[] = [];
        for(let i = 0; i < nsig.tscope.length; ++i) {
            for(let j = 0; j < nsig.tscope[i].tterms.length; ++j) {
                sigterms.push(nsig.tscope[i].tterms[j]);
            }
        }

        if(nsig.resolvedinfo.aliasopt !== undefined) {
            const tparams = nsig.resolvedinfo.aliasopt.terms;
            for(let i = 0; i < tparams.length; ++i) {
                mapping.set(tparams[i].name, sigterms[i] || new TemplateTypeSignature(nsig.sinfo, tparams[i].name));
            }
        }
        else {
            if((nsig.resolvedinfo.declopt as AbstractNominalTypeDecl).isSpecialResultEntity()) {
                mapping.set("T", sigterms[0] || new TemplateTypeSignature(nsig.sinfo, "T"));
                mapping.set("E", sigterms[1] || new TemplateTypeSignature(nsig.sinfo, "E"));
            }
            else if((nsig.resolvedinfo.declopt as AbstractNominalTypeDecl).isSpecialResultEntity()) {
                mapping.set("T", sigterms[0] || new TemplateTypeSignature(nsig.sinfo, "T"));
            }
            else {
                const tparams = (nsig.resolvedinfo.declopt as AbstractNominalTypeDecl).terms;
                for(let i = 0; i < tparams.length; ++i) {
                    mapping.set(tparams[i].name, sigterms[i] || new TemplateTypeSignature(nsig.sinfo, tparams[i].name));
                }
            }
        }

        return TemplateNameMapper.createInitialMapping(mapping);
    }

    private aliasResolveTypeSignature(tsig: TypeSignature): TypeSignature {
        let isig: TypeSignature | undefined = undefined;
        let nsig: TypeSignature = tsig;
        while(isig === undefined || isig.tkeystr !== nsig.tkeystr) {
            isig = nsig;

            if(isig instanceof NominalParsedTypeSignature) {
                if(isig.resolvedinfo.aliasopt !== undefined) {
                    const remapper = TypeCheckerRelations.computeNameMapperFromDirectNominalParserTypeSignatureInfo(isig);
                    nsig = this.aliasResolveTypeSignature(isig.resolvedinfo.aliasopt.boundType.remapTemplateBindings(remapper));
                }
                else {
                    nsig = new NominalResolvedTypeSignature(tsig.sinfo, isig.resolvedinfo.declopt as AbstractNominalTypeDecl, isig.tscope.flatMap((ts) => ts.tterms));
                }
            }
            else {
                nsig = isig;
            }  
        }
        
        return nsig;
    }

    private flattenTypeSignature(tsig: TypeSignature): TypeSignature[] {
        if(tsig instanceof NoneableTypeSignature) {
            return [...this.flattenTypeSignature(tsig.type), this.wellknowntypes.get("None") as TypeSignature];
        }
        if(tsig instanceof UnionTypeSignature) {
            return tsig.types.flatMap((t) => this.flattenTypeSignature(t));
        }
        else {
            return [tsig];
        }
    }

    private unflattenTypeSignature(sinfo: SourceInfo, tsigl: TypeSignature[]): TypeSignature {
        if(tsigl.length === 1) {
            return tsigl[0];
        }
        else if(tsigl.length === 2 && tsigl.some((t) => t.tkeystr === "None")) {
            return new NoneableTypeSignature(sinfo, tsigl.find((t) => t.tkeystr !== "None") as TypeSignature);
        }
        else {
            return new UnionTypeSignature(sinfo, tsigl);
        }
    }

    private simplifyUnionType(sinfo: SourceInfo, tl: TypeSignature[], tconstrain: TemplateConstraintScope): TypeSignature {
        assert(!tl.some((t) => t instanceof UnionTypeSignature), "Should be a flat list of types");
        assert(!tl.some((t) => t instanceof NoneableTypeSignature), "Should be a flat list of types");

        //check for None+Some -> Any
        if(tl.some((tt) => this.isSubtypeOf(this.wellknowntypes.get("None") as TypeSignature, tt, tconstrain)) && tl.some((tt) => this.isSubtypeOf(this.wellknowntypes.get("Some") as TypeSignature, tt, tconstrain))) {
            return this.wellknowntypes.get("Any") as TypeSignature;
        }

        //check for complete set of datatype members
        const dts = tl.map((t) => this.aliasResolveTypeSignature(t)).filter((t) => (t instanceof NominalResolvedTypeSignature) && (t.decl instanceof DatatypeMemberEntityTypeDecl));
        if(dts.length !== 0) {
            for(let i = 0; i < dts.length; ++i) {
                const ndts = dts[i] as NominalResolvedTypeSignature;
                const pptype = (ndts.decl as DatatypeMemberEntityTypeDecl).parentTypeDecl;
                
                const allmembers = pptype.associatedMemberEntityDecls.every((mem) => {
                    const tmem = new NominalResolvedTypeSignature(mem.sinfo, mem, ndts.alltermargs);
                    return tl.some((t) => this.areSameTypes(t, tmem, tconstrain));  
                });

                if(allmembers) {
                    const realptype = new NominalResolvedTypeSignature(ndts.sinfo, pptype, ndts.alltermargs);
                    tl.push(realptype);
                }
            }
        }

        //check for Nothing+Something -> Option
        const somethings = tl.map((t) => this.aliasResolveTypeSignature(t)).filter((t) => (t instanceof NominalResolvedTypeSignature) && (t.decl instanceof SomethingTypeDecl));
        if(this.includesNothingType(tt, tconstrain)) {
            const somethings = tl.filter((t) => this.isSomethingType(t, tconstrain)).map((t) => this.getOptionTypeForSomethingT(this.normalizeTypeSignature(t, tconstrain), tconstrain));
            tl.push(...somethings);
        }

        //check for Ok+Err -> Result
        if(tl.some((t) => this.isOkType(t, tconstrain)) && tl.some((t) => this.isErrType(t, tconstrain))) {
            const okts = tl.filter((t) => this.isOkType(t, tconstrain));
            const errts = tl.filter((t) => this.isErrType(t, tconstrain));

            const okres = okts.map((t) => this.getResultTypeForOkTE(this.normalizeTypeSignature(t, tconstrain), tconstrain));
            const errres = errts.map((t) => this.getResultTypeForErrorTE(this.normalizeTypeSignature(t, tconstrain), tconstrain));

            const nres = okres.filter((t) => errres.some((et) => this.areSameTypes(t, et, tconstrain)));
            tl.push(...nres);
        }

        xxxx;

        let restypel = [tl[0]];
        for(let i = 1; i < tl.length; ++i) {
            const ntt = tl[i];

            const findres = restypel.findIndex((rt) => this.isSubtypeOf(ntt, rt, tconstrain));
            if(findres === -1) {
                //not a subtype of any of the existing types -- filter any types that are subtypes of ntt and then add ntt
                restypel = [...restypel.filter((rt) => !this.isSubtypeOf(rt, ntt, tconstrain)), ntt];
            }
        }
        restypel.sort((a, b) => a.tkeystr.localeCompare(b.tkeystr));

        if(restypel.length === 1) {
            return restypel[0];
        }
        else if(restypel.length === 2 && restypel.some((t) => t.tkeystr === "None")) {
            return new NoneableTypeSignature(tt.sinfo, restypel.find((t) => t.tkeystr !== "None") as TypeSignature);
        }
        else {
            return new UnionTypeSignature(tt.sinfo, restypel);
        }
    }

    /**
     * Given a type signature that is nested just do the simplification steps (don't try and resolve any aliases or templates)
     */
    private normalizeTypeSignatureNoResolve(tsig: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        if(tsig instanceof ErrorTypeSignature || tsig instanceof VoidTypeSignature || tsig instanceof AutoTypeSignature) {
            return tsig;
        }
        else if(tsig instanceof TemplateTypeSignature) {
            return tsig;
        }
        else if(tsig instanceof NominalParsedTypeSignature) {
            const rttypes = tsig.tscope.map((ts) => {
                return { tname: ts.tname, tterms: ts.tterms.map((t) => this.normalizeTypeSignatureNoResolve(t, tconstrain)) };
            });

            return new NominalParsedTypeSignature(tsig.sinfo, tsig.ns, rttypes, tsig.resolvedinfo);
        }
        else if(tsig instanceof NominalResolvedTypeSignature) {
            const rttypes = tsig.alltermargs.map((ts) => {
                return this.normalizeTypeSignatureNoResolve(ts, tconstrain);
            });

            return new NominalResolvedTypeSignature(tsig.sinfo, tsig.decl, rttypes);
        }
        else if(tsig instanceof TupleTypeSignature) {
            const rttypes = tsig.entries.map((ts) => {
                return this.normalizeTypeSignatureNoResolve(ts, tconstrain)
            });

            return new TupleTypeSignature(tsig.sinfo, rttypes);
        }
        else if(tsig instanceof RecordTypeSignature) {
            const rttypes = tsig.entries.map((ts) => {
                return [ts[0], this.normalizeTypeSignatureNoResolve(ts[1], tconstrain)] as [string, TypeSignature];
            }).sort((a, b) => a[0].localeCompare(b[0]));

            return new RecordTypeSignature(tsig.sinfo, rttypes);
        }
        else if(tsig instanceof EListTypeSignature) {
            const rttypes = tsig.entries.map((ts) => {
                return this.normalizeTypeSignatureNoResolve(ts, tconstrain)
            });

            return new EListTypeSignature(tsig.sinfo, rttypes);
        }
        else if(tsig instanceof StringTemplateTypeSignature) {
            const rttypes = tsig.argtypes.map((ts) => {
                return this.normalizeTypeSignatureNoResolve(ts, tconstrain)
            });

            return new StringTemplateTypeSignature(tsig.sinfo, tsig.kind, rttypes);
        }
        else if(tsig instanceof LambdaTypeSignature) {
            const rparams = tsig.params.map((pp) => {
                return new LambdaParameterSignature(this.normalizeTypeSignatureNoResolve(pp.type, tconstrain), pp.isRefParam, pp.isRestParam);
            });

            return new LambdaTypeSignature(tsig.sinfo, tsig.recursive, tsig.name, rparams, this.normalizeTypeSignatureNoResolve(tsig.resultType, tconstrain));
        }
        else if(tsig instanceof NoneableTypeSignature) {
            const ots = this.normalizeTypeSignatureNoResolve(tsig.type, tconstrain);
            if(ots instanceof UnionTypeSignature) {
                return this.simplifyUnionType(tsig.sinfo, [...ots.types, this.wellknowntypes.get("None") as TypeSignature], tconstrain);
            }
            else {
                return this.simplifyUnionType(tsig.sinfo, [ots, this.wellknowntypes.get("None") as TypeSignature], tconstrain);
            }
        }
        else if(tsig instanceof UnionTypeSignature) {
            const ntypes = tsig.types.map((ts) => this.normalizeTypeSignatureNoResolve(ts, tconstrain));
            return this.simplifyUnionType(tsig.sinfo, ntypes, tconstrain);
        }
        else {
            assert(false, "Unknown type signature");
        }
    }

    normalizeTypeSignature(tsig: TypeSignature, tconstrain: TemplateConstraintScope, instantiatetemplate: boolean): TypeSignature {
        let isig: TypeSignature | undefined = undefined;
        let nsig = tsig;
        while(isig === undefined || isig.tkeystr !== nsig.tkeystr) {
            isig = nsig;

            if(instantiatetemplate && (isig instanceof TemplateTypeSignature)) {
                const rr = tconstrain.resolveConstraint(isig.name);
                if(rr === undefined) {
                    nsig = isig;
                }
                else {
                    nsig = rr.tconstraint;
                }
            }
            else if(isig instanceof NominalParsedTypeSignature) {
                if(isig.resolvedinfo.aliasopt !== undefined) {
                    const remapper = TypeCheckerRelations.computeNameMapperFromDirectNominalParserTypeSignatureInfo(isig);
                    nsig = this.normalizeTypeSignature(isig.resolvedinfo.aliasopt.boundType.remapTemplateBindings(remapper), tconstrain, instantiatetemplate);
                }
                else {
                    nsig = new NominalResolvedTypeSignature(tsig.sinfo, isig.resolvedinfo.declopt as AbstractNominalTypeDecl, isig.tscope.flatMap((ts) => ts.tterms));
                }
            }
            else {
                nsig = isig;
            }
    
            nsig = this.normalizeTypeSignatureNoResolve(nsig, tconstrain);    
        }
        
        return nsig;
    }

    private static areSameNameLists(nl1: string[], nl2: string[]): boolean {
        if(nl1.length !== nl2.length) {
            return false;
        }

        for(let i = 0; i < nl1.length; ++i) {
            if(nl1[i] !== nl2[i]) {
                return false;
            }
        }

        return true;
    }

    private areSameTypeScopeTemplateLists(tscope1: {tname: string, terms: TypeSignature[]}[], tscope2: {tname: string, terms: TypeSignature[]}[], tconstrain: TemplateConstraintScope): boolean {
        if(tscope1.length !== tscope2.length) {
            return false;
        }

        for(let i = 0; i < tscope1.length; ++i) {
            if(!this.areSameTypeSignatureLists(tscope1[i].terms, tscope2[i].terms, tconstrain)) {
                return false;
            }
        }

        return true;
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

    private templateIsSubtypeOf(t1: TemplateTypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        const cons = tconstrain.resolveConstraint(t1.name);
        return cons !== undefined && this.isSubtypeOf(cons.tconstraint, t2, tconstrain);
    }

    private nominalIsSubtypeOf(t1: NominalTypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        const tmapping = TypeCheckerRelations.computeNameMapperFromDirectTypeSignatureInfo(t1);

        const specialprovides = this.resolveSpecialProvidesDecls(t1, tconstrain).map((t) => t.remapTemplateBindings(tmapping));
        const regularprovides = (t1.resolvedDeclaration as AbstractNominalTypeDecl).provides.map((t) => t.remapTemplateBindings(tmapping));

        return [...specialprovides, ...regularprovides].some((t) => this.isSubtypeOf(t, t2, tconstrain));
    }

    private tupleIsSubtypeOf(t1: TupleTypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        if(t2 instanceof NominalTypeSignature) {
            return this.isSubtypeOf(this.wellknowntypes.get("Some") as NominalTypeSignature, t2, tconstrain);
        }
        else if(t2 instanceof NoneableTypeSignature) {
            return this.isSubtypeOf(t1, t2.type, tconstrain);
        }
        else if(t2 instanceof UnionTypeSignature) {
            return t2.types.some((t) => this.isSubtypeOf(t1, t, tconstrain));
        }
        else {
            return false;
        }
    }

    private recordIsSubtypeOf(t1: RecordTypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        if(t2 instanceof NominalTypeSignature) {
            return this.isSubtypeOf(this.wellknowntypes.get("Some") as NominalTypeSignature, t2, tconstrain);
        }
        else if(t2 instanceof NoneableTypeSignature) {
            return this.isSubtypeOf(t1, t2.type, tconstrain);
        }
        else if(t2 instanceof UnionTypeSignature) {
            return t2.types.some((t) => this.isSubtypeOf(t1, t, tconstrain));
        }
        else {
            return false;
        }
    }

    private stringTemplateIsSubtypeOf(t1: StringTemplateTypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        if(t2 instanceof NominalTypeSignature) {
            return this.isSubtypeOf(t1.kind === "utf8" ? this.wellknowntypes.get("TemplateString") as NominalTypeSignature : this.wellknowntypes.get("TemplateCString") as NominalTypeSignature, t2, tconstrain);
        }
        else if(t2 instanceof NoneableTypeSignature) {
            return this.isSubtypeOf(t1, t2.type, tconstrain);
        }
        else if(t2 instanceof UnionTypeSignature) {
            return t2.types.some((t) => this.isSubtypeOf(t1, t, tconstrain));
        }
        else {
            return false;
        }
    }

    private noneableIsSubtypeOf(t1: NoneableTypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        return this.isSubtypeOf(this.wellknowntypes.get("None") as TypeSignature, t2, tconstrain) && this.isSubtypeOf(t1.type, t2, tconstrain);
    }

    private unionIsSubtypeOf(t1: UnionTypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        return t1.types.every((t) => this.isSubtypeOf(t, t2, tconstrain));
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
        if(t2.tkeystr === "Any") {
            res = true;
        }
        else if(this.areSameTypes(t1, t2, tconstrain)) {
            res = true;
        }
        else {
            if(t1 instanceof TemplateTypeSignature) {
                res = this.templateIsSubtypeOf(t1, t2, tconstrain);
            }
            else if(t1 instanceof NominalParsedTypeSignature) {
                res = this.nominalParsedIsSubtypeOf(t1, nt2, tconstrain);
            }
            else if(t1 instanceof NominalResolvedTypeSignature) {
                res = this.nominalResolvedIsSubtypeOf(t1, nt2, tconstrain);
            }
            else if(t1 instanceof TupleTypeSignature) {
                res = this.tupleIsSubtypeOf(t1, t2, tconstrain);
            }
            else if(t1 instanceof RecordTypeSignature) {
                res = this.recordIsSubtypeOf(t1, t2, tconstrain);
            }
            else if (t1 instanceof StringTemplateTypeSignature) {
                res = this.stringTemplateIsSubtypeOf(t1, t2, tconstrain);
            }
            else if(t1 instanceof NoneableTypeSignature) {
                res = this.noneableIsSubtypeOf(t1, t2, tconstrain);
            }
            else if(t1 instanceof UnionTypeSignature) {
                res = this.unionIsSubtypeOf(t1, t2, tconstrain);
            }
            else {
                res = false;
            }
        }

        this.memoizedTypeSubtypeRelation.set(kstr, res);
        return res;
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

        let res = false
        if(t1 instanceof VoidTypeSignature && t2 instanceof VoidTypeSignature) {
            res = true;
        }
        else if(t1 instanceof TemplateTypeSignature && t2 instanceof TemplateTypeSignature) {
            res = (t1.name === t2.name);
        }
        else if(nt1 instanceof NominalTypeSignature && nt2 instanceof NominalTypeSignature) {
            if(!TypeCheckerRelations.areSameNameLists(nt1.ns, nt2.ns)) {
                res = false;
            }
            else {
                const rd1 = nt1.resolvedDeclaration as AbstractNominalTypeDecl;
                const rd2 = nt2.resolvedDeclaration as AbstractNominalTypeDecl;
                res = (rd1.name === rd2.name) && this.areSameTypeScopeTemplateLists(nt1.tscope, nt2.tscope, tconstrain);
            }
        }
        else if(t1 instanceof TupleTypeSignature && t2 instanceof TupleTypeSignature) {
            res = this.areSameTypeSignatureLists(t1.entries, t2.entries, tconstrain);
        }
        else if(t1 instanceof RecordTypeSignature && t2 instanceof RecordTypeSignature) {
            const stl1 = [...t1.entries].sort((a, b) => a[0].localeCompare(b[0]));
            const stl2 = [...t2.entries].sort((a, b) => a[0].localeCompare(b[0]));

            const samenames = TypeCheckerRelations.areSameNameLists(stl1.map((st) => st[0]), stl2.map((st) => st[0]));
            const sametypes = this.areSameTypeSignatureLists(stl1.map((st) => st[1]), stl2.map((st) => st[1]), tconstrain);

            res = samenames && sametypes;
        }
        else if(t1 instanceof EListTypeSignature && t2 instanceof EListTypeSignature) {
            res = this.areSameTypeSignatureLists(t1.entries, t2.entries, tconstrain);
        }
        else if(t1 instanceof StringTemplateTypeSignature && t2 instanceof StringTemplateTypeSignature) {
            res = (t1.kind === t2.kind) && this.areSameTypeSignatureLists(t1.argtypes, t2.argtypes, tconstrain);
        }
        else if(t1 instanceof LambdaTypeSignature && t2 instanceof LambdaTypeSignature) {
            if(t1.recursive !== t2.recursive || t1.name !== t2.name) {
                res = false;
            }
            else {
                const okargs = this.areSameFunctionParamLists(t1.params, t2.params, tconstrain);
                const okres = this.areSameTypes(t1.resultType, t2.resultType, tconstrain);

                res = okargs && okres;
            }
        }
        else if(t1 instanceof NoneableTypeSignature && t2 instanceof NoneableTypeSignature) {
            res = this.areSameTypes(t1.type, t2.type, tconstrain);
        }
        else if(nt1 instanceof UnionTypeSignature && nt2 instanceof UnionTypeSignature) {
            const tl1: TypeSignature[] = [];
            TypeCheckerRelations.flattenUnionType(nt1, tl1);

            const tl2: TypeSignature[] = [];
            TypeCheckerRelations.flattenUnionType(nt2, tl2);

            if(tl1.length !== tl2.length) {
                res = false;
            }
            else {
                res = tl1.every((t1) => tl2.some((t2) => this.areSameTypes(t1, t2, tconstrain)));
            }
        }
        else if(t1 instanceof NoneableTypeSignature && t2 instanceof UnionTypeSignature) {
            res = this.areSameTypes(new UnionTypeSignature(nt2.sinfo, nt1.type, this.wellknowntypes.get("None") as TypeSignature), nt2, tconstrain);
        }
        else if(t1 instanceof UnionTypeSignature && t2 instanceof NoneableTypeSignature) {
            res = this.areSameTypes(nt1, new UnionTypeSignature(nt1.sinfo, nt2.type, this.wellknowntypes.get("None") as TypeSignature), tconstrain);
        }
        else {
            ; //for all other cases res stays false
        }

        this.memoizedTypeEqualRelation.set(kstr, res);
        return res;
    }

    

    //Check if this type is a KeyType (e.g. a subtype of KeyType)
    isKeyType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        return this.isSubtypeOf(t, this.wellknowntypes.get("KeyType") as TypeSignature, tconstrain);
    }

    //Check is this type is unique (i.e. not a union or concept type)
    isUniqueType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        const ntype = this.normalizeTypeSignature(t, tconstrain);

        if(ntype instanceof NominalTypeSignature) {
            return ntype.resolvedDeclaration instanceof AbstractEntityTypeDecl;
        }
        else if(ntype instanceof TemplateTypeSignature) {
            const tcs = tconstrain.resolveConstraint(ntype.name);
            return tcs !== undefined && tcs.extraTags.includes(TemplateTermDeclExtraTag.Unique);
        }
        else if((ntype instanceof TupleTypeSignature) || ntype instanceof RecordTypeSignature || ntype instanceof EListTypeSignature) {
            return true;
        }
        else if(ntype instanceof StringTemplateTypeSignature) {
            return true;
        }
        else {
            return false;
        }
    }

    //Check is this type is unique (i.e. not a union or concept type)
    isAtomicType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        const ntype = this.normalizeTypeSignature(t, tconstrain);

        if(ntype instanceof NominalTypeSignature) {
            return true
        }
        else if(ntype instanceof TemplateTypeSignature) {
            const tcs = tconstrain.resolveConstraint(ntype.name);
            return tcs !== undefined && tcs.extraTags.includes(TemplateTermDeclExtraTag.Atomic);
        }
        else if((ntype instanceof TupleTypeSignature) || ntype instanceof RecordTypeSignature || ntype instanceof EListTypeSignature) {
            return true;
        }
        else if(ntype instanceof StringTemplateTypeSignature) {
            return true;
        }
        else {
            return false;
        }
    }

    //Check if this type is unique and a numeric type of some sort (either primitive number or a typedecl of a numeric type)
    isUniqueNumericType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");
        
        return this.isUniqueType(t, tconstrain) && this.isSubtypeOf(t, this.wellknowntypes.get("Numeric") as TypeSignature, tconstrain);
    }

    //Check if this type is a primitive type in Core
    isPrimitiveType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        const tnorm = this.normalizeTypeSignature(t, tconstrain);
        if(!(tnorm instanceof NominalTypeSignature)) {
            return false;
        }

        return tnorm.resolvedDeclaration instanceof PrimitiveEntityTypeDecl;

    }

    //Check if we can assign this type as the RHS of a typedecl declaration
    isTypedeclableType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        const tnorm = this.normalizeTypeSignature(t, tconstrain);
        if(!(tnorm instanceof NominalTypeSignature)) {
            return false;
        }

        const tdecl = tnorm.resolvedDeclaration as AbstractNominalTypeDecl;
        if(tdecl instanceof EnumTypeDecl) {
            return true;
        }
        else if(tdecl instanceof TypedeclTypeDecl) {
            return true;
        }
        else if(tdecl instanceof InternalEntityTypeDecl) {
            return tdecl.attributes.find((attr) => attr.name === "__typedeclable") !== undefined;
        }
        else {
            return false;
        }
    }

    //Check if this type is a valid event type
    isEventDataType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        const ttnorm = this.normalizeTypeSignatureIncludingTemplate(t, tconstrain);
        if(!(ttnorm instanceof NominalTypeSignature)) {
            return false;
        }

        return (ttnorm.resolvedDeclaration as AbstractNominalTypeDecl).etag === AdditionalTypeDeclTag.Event;
    }

    //Check if this type is a valid status
    isStatusDataType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        const ttnorm = this.normalizeTypeSignatureIncludingTemplate(t, tconstrain);
        if(!(ttnorm instanceof NominalTypeSignature)) {
            return false;
        }

        return (ttnorm.resolvedDeclaration as AbstractNominalTypeDecl).etag === AdditionalTypeDeclTag.Status;
    }

    //Check if this type is a valid type to have as a provides type -- must be a unique CONCEPT type
    isValidProvidesType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t instanceof ErrorTypeSignature), "Checking subtypes on errors");

        const ttnorm = this.normalizeTypeSignature(t, tconstrain);
        if(!(ttnorm instanceof NominalTypeSignature)) {
            return false;
        }

        return ttnorm.resolvedDeclaration instanceof AbstractConceptTypeDecl;
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

    private refineTuple(src: TupleTypeSignature, refine: TypeSignature, tconstrain: TemplateConstraintScope): { overlap: TypeSignature | undefined, remain: TypeSignature | undefined } {
        if(this.isSubtypeOf(src, refine, tconstrain)) {
            return { overlap: src, remain: undefined };
        }
        else {
            return { overlap: undefined, remain: src };
        }
    }

    private refineRecord(src: RecordTypeSignature, refine: TypeSignature, tconstrain: TemplateConstraintScope): { overlap: TypeSignature | undefined, remain: TypeSignature | undefined } {
        if(this.isSubtypeOf(src, refine, tconstrain)) {
            return { overlap: src, remain: undefined };
        }
        else {
            return { overlap: undefined, remain: src };
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

    resolveSpecialProvidesDecls(t: NominalTypeSignature, tconstrain: TemplateConstraintScope): TypeSignature[] {
        const tdecl = t.resolvedDeclaration as AbstractNominalTypeDecl;

        if(tdecl instanceof EnumTypeDecl) {
            return [this.wellknowntypes.get("KeyType") as TypeSignature, this.wellknowntypes.get("Some") as TypeSignature];
        }
        else if(tdecl instanceof RegexValidatorTypeDecl) {
            return [this.wellknowntypes.get("RegexValidator") as TypeSignature];
        }
        else if(tdecl instanceof CRegexValidatorTypeDecl) {
            return [this.wellknowntypes.get("CRegexValidator") as TypeSignature];
        }
        else if(tdecl instanceof PathValidatorTypeDecl) {
            return [this.wellknowntypes.get("PathValidator") as TypeSignature];
        }
        else if(tdecl instanceof DatatypeMemberEntityTypeDecl) {
            return [new NominalTypeSignature(t.sinfo, t.ns, [{tname: tdecl.parentTypeDecl.name, terms: t.tscope[0].terms}], undefined, tdecl.parentTypeDecl)];
        }
        else if(tdecl instanceof TypedeclTypeDecl) {
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
    resolveAllProvidesDecls(provides: TypeSignature[], tconstrain: TemplateConstraintScope): TypeLookupInfo[] {
        const pdecls: TypeLookupInfo[] = [];
        for(let i = 0; i < provides.length; ++i) {
            const pnorm = this.normalizeTypeSignature(provides[i], tconstrain);
            if(!(pnorm instanceof NominalTypeSignature) || !(pnorm.resolvedDeclaration instanceof AbstractConceptTypeDecl)) {
                continue;
            }

            const pdecl = pnorm.resolvedDeclaration as ConceptTypeDecl;
            const pterms = TypeCheckerRelations.computeNameMapperFromDirectTypeSignatureInfo(pnorm);
            pdecls.push(new TypeLookupInfo(pnorm, pdecl, pterms));

            //now add all of the inherited concepts
            for(let j = 0; j < pdecl.provides.length; ++j) {
                const pdecls2 = this.resolveAllProvidesDecls([pdecl.provides[j]], tconstrain);

                //but filter out any duplicates
                for(let k = 0; k < pdecls2.length; ++k) {
                    const dupl = pdecls.find((pd) => this.areSameTypes(pnorm, pdecls2[k].tsig, tconstrain));
                    if(dupl === undefined) {
                        pdecls.push(...pdecls2);
                    }
                }
            }
        }

        return pdecls;
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
