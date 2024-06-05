import {strict as assert} from "assert";

import { AutoTypeSignature, EListTypeSignature, ErrorTypeSignature, FullyQualifiedNamespace, FunctionParameter, LambdaTypeSignature, NominalTypeSignature, NoneableTypeSignature, RecordTypeSignature, StringTemplateTypeSignature, TemplateConstraintScope, TemplateNameMapper, TemplateTypeSignature, TupleTypeSignature, TypeSignature, UnionTypeSignature, VoidTypeSignature } from "./type";
import { AbstractConceptTypeDecl, AbstractEntityTypeDecl, AbstractNominalTypeDecl, AdditionalTypeDeclTag, Assembly, ConceptTypeDecl, ConstMemberDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, EntityTypeDecl, EnumTypeDecl, ErrTypeDecl, ExRegexValidatorTypeDecl, InternalEntityTypeDecl, MemberFieldDecl, MethodDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, OkTypeDecl, OptionTypeDecl, PathValidatorTypeDecl, PrimitiveEntityTypeDecl, RegexValidatorTypeDecl, ResultTypeDecl, SomethingTypeDecl, TaskDecl, TypeFunctionDecl, TypedeclTypeDecl } from "./assembly";
import { SourceInfo } from "./build_decls";

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

    private static flattenUnionType(tt: UnionTypeSignature, into: TypeSignature[]) {
        if(tt.ltype instanceof UnionTypeSignature) {
            this.flattenUnionType(tt.ltype, into);
        }
        else {
            into.push(tt.ltype);
        }

        if(tt.rtype instanceof UnionTypeSignature) {
            this.flattenUnionType(tt.rtype, into);
        }
        else {
            into.push(tt.rtype);
        }
    }

    private static treeifyUnionType(sinfo: SourceInfo, tl: TypeSignature[]): UnionTypeSignature {
        if(tl.length === 2) {
            return new UnionTypeSignature(tl[0].sinfo, tl[0], tl[1]);
        }
        else {
            return new UnionTypeSignature(tl[0].sinfo, tl[0], this.treeifyUnionType(sinfo, tl.slice(1)));
        }
    }

    private simplifyUnionType(tt: UnionTypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        const tl: TypeSignature[] = [];
        TypeCheckerRelations.flattenUnionType(tt, tl);

        //check for None+Some -> Any
        if(this.includesNoneType(tt, tconstrain) && this.isSubtypeOf(this.wellknowntypes.get("Some") as TypeSignature, tt, tconstrain)) {
            return this.wellknowntypes.get("Any") as TypeSignature;
        }

        //check for complete set of datatype members
        const dts = tl.map((t) => this.normalizeTypeSignature(t, tconstrain)).filter((t) => (t instanceof NominalTypeSignature) && (t.resolvedDeclaration instanceof DatatypeMemberEntityTypeDecl));
        if(dts.length !== 0) {
            for(let i = 0; i < dts.length; ++i) {
                const pptype = ((dts[i] as NominalTypeSignature).resolvedDeclaration as DatatypeMemberEntityTypeDecl).parentTypeDecl;
                const realmapper = TypeCheckerRelations.computeNameMapperFromDirectResolvedTerms((dts[i] as NominalTypeSignature).resolvedTerms);
                const realptype = pptype.remapTemplateBindings(realmapper);

                const allmembers = ((realptype as NominalTypeSignature).resolvedDeclaration as DatatypeTypeDecl).associatedMemberEntityDecls.every((mem) => {
                    const realmem = mem.remapTemplateBindings(realmapper);
                    return tl.some((t) => this.areSameTypes(t, realmem, tconstrain));  
                });

                if(allmembers) {
                    tl.push(realptype);
                }
            }
        }

        //check for Nothing+Something -> Option
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

        let restypel = [tl[0]];
        for(let i = 1; i < tl.length; ++i) {
            const ntt = tl[i];

            const findres = restypel.findIndex((rt) => this.isSubtypeOf(ntt, rt, tconstrain));
            if(findres === -1) {
                //not a subtype of any of the existing types

                //filter any types that are subtypes of ntt and then add ntt
                restypel = [...restypel.filter((rt) => !this.isSubtypeOf(rt, ntt, tconstrain)), ntt];
            }
        }

        if(restypel.length === 1) {
            return restypel[0];
        }
        else if(restypel.length === 2 && restypel.some((t) => this.isNoneType(t, tconstrain))) {
            return new NoneableTypeSignature(tt.sinfo, restypel.find((t) => !this.isNoneType(t, tconstrain)) as TypeSignature);
        }
        else {
            return TypeCheckerRelations.treeifyUnionType(tt.sinfo, restypel);
        }
    }

    private static computeNameMapperFromDirectResolvedTerms(directResolved: {name: string, type: TypeSignature}[]): TemplateNameMapper {
        let mapping = new Map<string, TypeSignature>();
        directResolved.forEach((tterm) => mapping.set(tterm.name, tterm.type));

        return TemplateNameMapper.createInitialMapping(mapping);
    }

    /**
     * Given a the signature resolve it (at the top-level) with any aliases or union / intersection simplifications
     */
    normalizeTypeSignature(tsig: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        if(tsig instanceof ErrorTypeSignature || tsig instanceof VoidTypeSignature || tsig instanceof AutoTypeSignature) {
            return tsig;
        }
        else if(tsig instanceof TemplateTypeSignature) {
            return tsig;
        }
        else if(tsig instanceof NominalTypeSignature) {
            if(tsig.resolvedTypedef === undefined) {
                return tsig;
            }
            else {
                const remapper = TypeCheckerRelations.computeNameMapperFromDirectResolvedTerms(tsig.resolvedTerms);
                return this.normalizeTypeSignature(tsig.resolvedTypedef.boundType.remapTemplateBindings(remapper), tconstrain);
            }
        }
        else if(tsig instanceof TupleTypeSignature || tsig instanceof RecordTypeSignature || tsig instanceof EListTypeSignature) {
            return tsig;
        }
        else if(tsig instanceof StringTemplateTypeSignature) {
            return tsig;
        }
        else if(tsig instanceof LambdaTypeSignature) {
            return tsig;
        }
        else if(tsig instanceof NoneableTypeSignature) {
            const ots = this.normalizeTypeSignature(tsig.type, tconstrain);
            if(this.includesNoneType(ots, tconstrain)) {
                return ots;
            }
            else if(this.isSomeType(ots, tconstrain)) {
                return this.wellknowntypes.get("Any") as TypeSignature;
            }
            else {
                return new NoneableTypeSignature(tsig.sinfo, ots);
            }
        }
        else if(tsig instanceof UnionTypeSignature) {
            const lnorm = this.normalizeTypeSignature(tsig.ltype, tconstrain);
            const rnorm = this.normalizeTypeSignature(tsig.rtype, tconstrain);

            return this.simplifyUnionType(new UnionTypeSignature(tsig.sinfo, lnorm, rnorm), tconstrain);
        }
        else {
            assert(false, "Unknown type signature");
        }
    }

    /**
     * Given a the signature resolve it (at the top-level) with any aliases or union / intersection simplifications AND resolve any (top-level) template types to their restrictions
     */
    private normalizeTypeSignatureIncludingTemplate(tsig: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        if(tsig instanceof ErrorTypeSignature || tsig instanceof VoidTypeSignature || tsig instanceof AutoTypeSignature) {
            return tsig;
        }
        else if(tsig instanceof TemplateTypeSignature) {
            const rr = tconstrain.resolveConstraint(tsig.name);
            if(rr === undefined) {
                return tsig;
            }
            else {
                return this.normalizeTypeSignatureIncludingTemplate(rr, tconstrain);
            }
        }
        else if(tsig instanceof NominalTypeSignature) {
            if(tsig.resolvedTypedef === undefined) {
                return tsig;
            }
            else {
                const remapper = TypeCheckerRelations.computeNameMapperFromDirectResolvedTerms(tsig.resolvedTerms);
                return this.normalizeTypeSignatureIncludingTemplate(tsig.resolvedTypedef.boundType.remapTemplateBindings(remapper), tconstrain);
            }
        }
        else if(tsig instanceof TupleTypeSignature || tsig instanceof RecordTypeSignature || tsig instanceof EListTypeSignature) {
            return tsig;
        }
        else if(tsig instanceof StringTemplateTypeSignature) {
            return tsig;
        }
        else if(tsig instanceof LambdaTypeSignature) {
            return tsig;
        }
        else if(tsig instanceof NoneableTypeSignature) {
            const ots = this.normalizeTypeSignatureIncludingTemplate(tsig.type, tconstrain);
            if(this.includesNoneType(ots, tconstrain)) {
                return ots;
            }
            else if(this.isSomeType(ots, tconstrain)) {
                return this.wellknowntypes.get("Any") as TypeSignature;
            }
            else {
                return new NoneableTypeSignature(tsig.sinfo, ots);
            }
        }
        else if(tsig instanceof UnionTypeSignature) {
            const lnorm = this.normalizeTypeSignatureIncludingTemplate(tsig.ltype, tconstrain);
            const rnorm = this.normalizeTypeSignatureIncludingTemplate(tsig.rtype, tconstrain);

            return this.simplifyUnionType(new UnionTypeSignature(tsig.sinfo, lnorm, rnorm), tconstrain);
        }
        else {
            assert(false, "Unknown type signature");
        }
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
            const opts = srcdecl.associatedMemberEntityDecls.map((mem) => this.refineNominal(mem, refine, tconstrain));
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

    private areSameTerms(terms1: {name: string, type: TypeSignature}[], terms2: {name: string, type: TypeSignature}[], tconstrain: TemplateConstraintScope): boolean {
        if(terms1.length !== terms2.length) {
            return false;
        }

        for(let i = 0; i < terms1.length; ++i) {
            assert(terms1[i].name === terms2[i].name, "Mismatched terms in nominal type");

            if(!this.areSameTypes(terms1[i].type, terms2[i].type, tconstrain)) {
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

    private areSameFunctionParamLists(tl1: FunctionParameter[], tl2: FunctionParameter[], tconstrain: TemplateConstraintScope): boolean {
        if(tl1.length !== tl2.length) {
            return false;
        }

        for(let i = 0; i < tl1.length; ++i) {
            if(tl1[i].name !== tl2[i].name || tl1[i].isRefParam !== tl2[i].isRefParam || tl1[i].isSpreadParam !== tl2[i].isSpreadParam) {
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
        return cons !== undefined && this.isSubtypeOf(cons, t2, tconstrain);
    }

    private nominalIsSubtypeOf(t1: NominalTypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        const tmapping = TypeCheckerRelations.computeNameMapperFromDirectResolvedTerms(t1.resolvedTerms);

        const specialprovides = this.resolveSpecialProvidesDecls(t1.resolvedDeclaration as AbstractNominalTypeDecl, tconstrain).map((t) => t.remapTemplateBindings(tmapping));
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
            return this.isSubtypeOf(t1, t2.ltype, tconstrain) || this.isSubtypeOf(t1, t2.rtype, tconstrain);
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
            return this.isSubtypeOf(t1, t2.ltype, tconstrain) || this.isSubtypeOf(t1, t2.rtype, tconstrain);
        }
        else {
            return false;
        }
    }

    private stringTemplateIsSubtypeOf(t1: StringTemplateTypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        if(t2 instanceof NominalTypeSignature) {
            return this.isSubtypeOf(t1.kind === "utf8" ? this.wellknowntypes.get("TemplateString") as NominalTypeSignature : this.wellknowntypes.get("ExTemplateString") as NominalTypeSignature, t2, tconstrain);
        }
        else if(t2 instanceof NoneableTypeSignature) {
            return this.isSubtypeOf(t1, t2.type, tconstrain);
        }
        else if(t2 instanceof UnionTypeSignature) {
            return this.isSubtypeOf(t1, t2.ltype, tconstrain) || this.isSubtypeOf(t1, t2.rtype, tconstrain);
        }
        else {
            return false;
        }
    }

    private noneableIsSubtypeOf(t1: NoneableTypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        return this.includesNoneType(t2, tconstrain) && this.isSubtypeOf(t1.type, t2, tconstrain);
    }

    private unionIsSubtypeOf(t1: UnionTypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        return this.isSubtypeOf(t1.ltype, t2, tconstrain) && this.isSubtypeOf(t1.rtype, t2, tconstrain);
    }

    //Check is t1 is a subtype of t2 -- template types are expanded when needed in this check
    isSubtypeOf(t1: TypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(!(t1 instanceof ErrorTypeSignature) && !(t2 instanceof ErrorTypeSignature), "Checking subtypes on errors");
        assert(!(t1 instanceof AutoTypeSignature) && !(t2 instanceof AutoTypeSignature), "Checking subtypes on auto");

        const nt1 = this.normalizeTypeSignature(t1, tconstrain);
        const nt2 = this.normalizeTypeSignature(t2, tconstrain);
        
        const kstr = `(${nt1.emit(true)} <: ${nt2.emit(true)})`;
        const memoval = this.memoizedTypeSubtypeRelation.get(kstr);
        if(memoval !== undefined) {
            return memoval;
        }

        let res = false;
        if(this.isAnyType(nt2, tconstrain)) {
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
            else if(nt1 instanceof TupleTypeSignature) {
                res = this.tupleIsSubtypeOf(nt1, nt2, tconstrain);
            }
            else if(nt1 instanceof RecordTypeSignature) {
                res = this.recordIsSubtypeOf(nt1, nt2, tconstrain);
            }
            else if (nt1 instanceof StringTemplateTypeSignature) {
                res = this.stringTemplateIsSubtypeOf(nt1, nt2, tconstrain);
            }
            else if(nt1 instanceof NoneableTypeSignature) {
                res = this.noneableIsSubtypeOf(nt1, nt2, tconstrain);
            }
            else if(nt1 instanceof UnionTypeSignature) {
                res = this.unionIsSubtypeOf(nt1, nt2, tconstrain);
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

        const nt1 = this.normalizeTypeSignature(t1, tconstrain);
        const nt2 = this.normalizeTypeSignature(t2, tconstrain);

        const kstr = `(${nt1.emit(true)} <> ${nt2.emit(true)})`;
        const memoval = this.memoizedTypeEqualRelation.get(kstr);
        if(memoval !== undefined) {
            return memoval;
        }

        let res = false
        if(nt1 instanceof VoidTypeSignature && nt2 instanceof VoidTypeSignature) {
            res = true;
        }
        else if(nt1 instanceof TemplateTypeSignature && nt2 instanceof TemplateTypeSignature) {
            res = (nt1.name === nt2.name);
        }
        else if(nt1 instanceof NominalTypeSignature && nt2 instanceof NominalTypeSignature) {
            if(!TypeCheckerRelations.areSameNameLists(nt1.ns, nt2.ns)) {
                res = false;
            }
            else {
                const rd1 = nt1.resolvedDeclaration as AbstractNominalTypeDecl;
                const rd2 = nt2.resolvedDeclaration as AbstractNominalTypeDecl;
                res = (rd1.name === rd2.name) && this.areSameTerms(nt1.resolvedTerms, nt2.resolvedTerms, tconstrain);
            }
        }
        else if(nt1 instanceof TupleTypeSignature && nt2 instanceof TupleTypeSignature) {
            res = this.areSameTypeSignatureLists(nt1.entries, nt2.entries, tconstrain);
        }
        else if(nt1 instanceof RecordTypeSignature && nt2 instanceof RecordTypeSignature) {
            const stl1 = [...nt1.entries].sort((a, b) => a[0].localeCompare(b[0]));
            const stl2 = [...nt2.entries].sort((a, b) => a[0].localeCompare(b[0]));

            const samenames = TypeCheckerRelations.areSameNameLists(stl1.map((st) => st[0]), stl2.map((st) => st[0]));
            const sametypes = this.areSameTypeSignatureLists(stl1.map((st) => st[1]), stl2.map((st) => st[1]), tconstrain);

            res = samenames && sametypes;
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
        else if(nt1 instanceof NoneableTypeSignature && nt2 instanceof UnionTypeSignature) {
            res = this.areSameTypes(new UnionTypeSignature(nt2.sinfo, nt1.type, this.wellknowntypes.get("None") as TypeSignature), nt2, tconstrain);
        }
        else if(nt1 instanceof UnionTypeSignature && nt2 instanceof NoneableTypeSignature) {
            res = this.areSameTypes(nt1, new UnionTypeSignature(nt1.sinfo, nt2.type, this.wellknowntypes.get("None") as TypeSignature), tconstrain);
        }
        else {
            ; //for all other cases res stays false
        }

        this.memoizedTypeEqualRelation.set(kstr, res);
        return res;
    }

    //Check if t1 is the type Any (exactly)
    isAnyType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        
        return this.areSameTypes(t, this.wellknowntypes.get("Any") as TypeSignature, tconstrain);
    }

    //Check if t1 is the type None (exactly)
    isNoneType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        
        return this.areSameTypes(t, this.wellknowntypes.get("None") as TypeSignature, tconstrain);
    }

    //Check if t1 is the type Nothing (exactly)
    isNothingType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        
        return this.areSameTypes(t, this.wellknowntypes.get("Nothing") as TypeSignature, tconstrain);
    }

    //Check if t1 is the type Some (exactly)
    isSomeType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        
        return this.areSameTypes(t, this.wellknowntypes.get("Some") as TypeSignature, tconstrain);
    }

    //Check if t1 is the type Something<T> (exactly)
    isSomethingType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        
        const frt = this.normalizeTypeSignature(t, tconstrain);
        if(!(frt instanceof NominalTypeSignature)) {
            return false;
        }

        assert(frt.resolvedDeclaration !== undefined);
        const tdecl = frt.resolvedDeclaration as AbstractNominalTypeDecl;
        return tdecl instanceof SomethingTypeDecl;
    }

    isOkType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        
        const frt = this.normalizeTypeSignature(t, tconstrain);
        if(!(frt instanceof NominalTypeSignature)) {
            return false;
        }

        assert(frt.resolvedDeclaration !== undefined);
        const tdecl = frt.resolvedDeclaration as AbstractNominalTypeDecl;
        return tdecl instanceof OkTypeDecl;
    }

    isErrType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        
        const frt = this.normalizeTypeSignature(t, tconstrain);
        if(!(frt instanceof NominalTypeSignature)) {
            return false;
        }

        assert(frt.resolvedDeclaration !== undefined);
        const tdecl = frt.resolvedDeclaration as AbstractNominalTypeDecl;
        return tdecl instanceof ErrTypeDecl;
    }

    //Check if t is the type Bool (exactly)
    isBooleanType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        return this.areSameTypes(t, this.wellknowntypes.get("Bool") as TypeSignature, tconstrain);
    }

    //Check if t is the type Void (exactly)
    isVoidType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        return this.areSameTypes(t, this.wellknowntypes.get("Void") as TypeSignature, tconstrain);
    }

    //Check if t includes None (e.g. None is a subtype of t)
    includesNoneType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        
        return this.isSubtypeOf(this.wellknowntypes.get("None") as TypeSignature, t, tconstrain);
    }

    //Check if t incudes Nothing (e.g. Nothing is a subtype of t)
    includesNothingType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        
        return this.isSubtypeOf(this.wellknowntypes.get("Nothing") as TypeSignature, t, tconstrain);
    }

    //Check is this type is unique (i.e. not a union or concept type)
    isUniqueType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        const ntype = this.normalizeTypeSignature(t, tconstrain);

        if(ntype instanceof NominalTypeSignature) {
            return ntype.resolvedDeclaration instanceof AbstractEntityTypeDecl;
        }
        else if((ntype instanceof TupleTypeSignature) || ntype instanceof RecordTypeSignature || ntype instanceof EListTypeSignature) {
            return true;
        }
        else if(ntype instanceof StringTemplateTypeSignature) {
            return true;
        }
        else if(ntype instanceof LambdaTypeSignature) {
            return true;
        }
        else {
            return false;
        }
    }

    //Check if this type is unique and a numeric type of some sort (either primitive number or a typedecl of a numeric type)
    static readonly _s_tnumericTemplateNameRE = /^[A-Z]Numeric$/;
    isUniqueNumericType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        
        const tnorm = this.normalizeTypeSignature(t, tconstrain);
        if(tnorm instanceof NominalTypeSignature) {
            const tdecl = tnorm.resolvedDeclaration as AbstractNominalTypeDecl;
            return tdecl.attributes.find((attr) => attr.name === "__numeric") !== undefined;
        }
        else if(tnorm instanceof TypedeclTypeDecl) {
            const btype = this.getTypeDeclBasePrimitiveType(tnorm, tconstrain);
            return btype !== undefined && this.isUniqueNumericType(btype, tconstrain);
        }
        else if(tnorm instanceof TemplateTypeSignature) {
            return TypeCheckerRelations._s_tnumericTemplateNameRE.test(tnorm.name);
        }
        else {
            return false;
        }
    }

    //Check if this type is a primitive type in Core
    isPrimitiveType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

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
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        const ttnorm = this.normalizeTypeSignatureIncludingTemplate(t, tconstrain);
        if(!(ttnorm instanceof NominalTypeSignature)) {
            return false;
        }

        return (ttnorm.resolvedDeclaration as AbstractNominalTypeDecl).etag === AdditionalTypeDeclTag.Event;
    }

    //Check if this type is a valid status
    isStatusDataType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        const ttnorm = this.normalizeTypeSignatureIncludingTemplate(t, tconstrain);
        if(!(ttnorm instanceof NominalTypeSignature)) {
            return false;
        }

        return (ttnorm.resolvedDeclaration as AbstractNominalTypeDecl).etag === AdditionalTypeDeclTag.Status;
    }

    //Check if this type is a valid type to have as a provides type -- must be a unique CONCEPT type
    isValidProvidesType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

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
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        const ttnorm = this.normalizeTypeSignature(t, tconstrain);
        if(ttnorm instanceof UnionTypeSignature) {
            return true;
        }
        else if(ttnorm instanceof NoneableTypeSignature) {
            return true;
        }
        else if(ttnorm instanceof NominalTypeSignature) {
            return ttnorm.resolvedDeclaration instanceof AbstractConceptTypeDecl;
        }
        else {
            return false;
        }
    }

    //Check if this type is a KeyType (e.g. a subtype of KeyType)
    isKeyType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        return this.isSubtypeOf(t, this.wellknowntypes.get("KeyType") as TypeSignature, tconstrain);
    }

    //Check if this type is a typedecl of some sort
    isTypeDeclType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        const tnorm = this.normalizeTypeSignature(t, tconstrain);
        return tnorm instanceof TypedeclTypeDecl;
    }

    //Get the assigned value type of a typedecl (resolving as needed)
    getTypeDeclValueType(t: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature | undefined {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        const tnorm = this.normalizeTypeSignature(t, tconstrain);
        if(!(tnorm instanceof NominalTypeSignature)) {
            return undefined;
        }

        const tdecl = tnorm.resolvedDeclaration as AbstractNominalTypeDecl;
        if(tdecl instanceof TypedeclTypeDecl) {
            const remapper = TypeCheckerRelations.computeNameMapperFromDirectResolvedTerms(tnorm.resolvedTerms);
            return tdecl.valuetype.remapTemplateBindings(remapper);
        }
        else {
            return undefined;
        }
    }

    private getTypeDeclBasePrimitiveType_Helper(t: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature | undefined {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        const tnorm = this.normalizeTypeSignature(t, tconstrain);
        if(!(tnorm instanceof NominalTypeSignature)) {
            return undefined;
        }

        const tdecl = tnorm.resolvedDeclaration as AbstractNominalTypeDecl;
        if(tdecl instanceof EnumTypeDecl) {
            return tnorm;
        }
        else if(tdecl instanceof TypedeclTypeDecl) {
            const remapper = TypeCheckerRelations.computeNameMapperFromDirectResolvedTerms(tnorm.resolvedTerms);
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
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

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

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "StringOf", terms: [vtype]}], [{name: "T", type: vtype}], undefined, stringofdecl);
    }

    getExStringOfType(vtype: TypeSignature): TypeSignature {
        const corens = this.assembly.getCoreNamespace();
        const stringofdecl = corens.typedecls.find((tdecl) => tdecl.name === "ExStringOf");

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "ExStringOf", terms: [vtype]}], [{name: "T", type: vtype}], undefined, stringofdecl);
    }

    getEventListOf(vtype: TypeSignature): TypeSignature {
        const corens = this.assembly.getCoreNamespace();
        const stringofdecl = corens.typedecls.find((tdecl) => tdecl.name === "EventList");

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "EventList", terms: [vtype]}], [{name: "T", type: vtype}], undefined, stringofdecl);
    }

    //given a type that is of the form Something<T> return the corresponding type Option<T>
    private getOptionTypeForSomethingT(vtype: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        const ttype = (vtype as NominalTypeSignature).resolvedTerms.find((tterm) => tterm.name === "T")!.type;

        const corens = this.assembly.getCoreNamespace();
        const optiondecl = corens.typedecls.find((tdecl) => tdecl.name === "Option");

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "Option", terms: [ttype]}], [{name: "T", type: ttype}], undefined, optiondecl);
    }

    //given a type that is of the form Option<T> return the corresponding type Something<T>
    private getSomethingTypeForOptionT(vtype: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        const ttype = (vtype as NominalTypeSignature).resolvedTerms.find((tterm) => tterm.name === "T")!.type;

        const corens = this.assembly.getCoreNamespace();
        const somethingdecl = corens.typedecls.find((tdecl) => tdecl.name === "Something");

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "Something", terms: [ttype]}], [{name: "T", type: ttype}], undefined, somethingdecl);
    }

    private getResultTypeForErrorTE(vtype: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        const ttype = (vtype as NominalTypeSignature).resolvedTerms.find((tterm) => tterm.name === "T")!.type;
        const etype = (vtype as NominalTypeSignature).resolvedTerms.find((tterm) => tterm.name === "E")!.type;

        const corens = this.assembly.getCoreNamespace();
        const resultdecl = corens.typedecls.find((tdecl) => tdecl.name === "Result");

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "Result", terms: [ttype, etype]}], [{name: "T", type: ttype}, {name: "E", type: etype}], undefined, resultdecl);
    }

    private getResultTypeForOkTE(vtype: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        const ttype = (vtype as NominalTypeSignature).resolvedTerms.find((tterm) => tterm.name === "T")!.type;

        const corens = this.assembly.getCoreNamespace();
        const resultdecl = corens.typedecls.find((tdecl) => tdecl.name === "Result");

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "Result", terms: [ttype, this.wellknowntypes.get("None") as TypeSignature]}], [{name: "T", type: ttype}, {name: "E", type: this.wellknowntypes.get("None") as TypeSignature}], undefined, resultdecl);
    }

    private getErrorTypeForResultTE(vtype: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        const ttype = (vtype as NominalTypeSignature).resolvedTerms.find((tterm) => tterm.name === "T")!.type;
        const etype = (vtype as NominalTypeSignature).resolvedTerms.find((tterm) => tterm.name === "E")!.type;

        const corens = this.assembly.getCoreNamespace();
        const errdecl = (corens.typedecls.find((tdecl) => tdecl.name === "Result") as ResultTypeDecl).nestedEntityDecls.find((tdecl) => tdecl.name === "Err") as ErrTypeDecl;

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "Result", terms: [ttype, etype]}, {tname: "Err", terms: []}], [{name: "T", type: ttype}, {name: "E", type: etype}], undefined, errdecl);
    }

    private getOkTypeForResultTE(vtype: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        const ttype = (vtype as NominalTypeSignature).resolvedTerms.find((tterm) => tterm.name === "T")!.type;
        const etype = (vtype as NominalTypeSignature).resolvedTerms.find((tterm) => tterm.name === "E")!.type;

        const corens = this.assembly.getCoreNamespace();
        const okdecl = (corens.typedecls.find((tdecl) => tdecl.name === "Result") as ResultTypeDecl).nestedEntityDecls.find((tdecl) => tdecl.name === "Ok") as OkTypeDecl;

        return new NominalTypeSignature(vtype.sinfo, ["Core"], [{tname: "Result", terms: [ttype, etype]}, {tname: "Ok", terms: []}], [{name: "T", type: ttype}, {name: "E", type: etype}], undefined, okdecl);
    }

    getNominalTypeForDecl(enclns: NamespaceDeclaration, tdecl: AbstractNominalTypeDecl): TypeSignature {
        const tterms = tdecl.terms.map((tterm) => new TemplateTypeSignature(tdecl.sinfo, tterm.name));
        const ttresolved = tterms.map((tterm) => { return {name: tterm.name, type: new TemplateTypeSignature(tdecl.sinfo, tterm.name)}; });

        return new NominalTypeSignature(tdecl.sinfo, enclns.fullnamespace.ns, [{tname: tdecl.name, terms: tterms}], ttresolved, undefined, tdecl);
    }

    getNominalTypeForNestedDecl(enclns: NamespaceDeclaration, encldecl: AbstractNominalTypeDecl, tdecl: AbstractNominalTypeDecl): TypeSignature {
        const tterms = encldecl.terms.map((tterm) => new TemplateTypeSignature(tdecl.sinfo, tterm.name));
        const ttresolved = encldecl.terms.map((tterm) => { return {name: tterm.name, type: new TemplateTypeSignature(tdecl.sinfo, tterm.name)}; });

        return new NominalTypeSignature(tdecl.sinfo, enclns.fullnamespace.ns, [{tname: encldecl.name, terms: tterms}, {tname: tdecl.name, terms: []}], ttresolved, undefined, tdecl);
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
            else if(tnorm.resolvedDeclaration instanceof ExRegexValidatorTypeDecl) {
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
            const tlinfo = new TypeLookupInfo(tn, tdecl, TypeCheckerRelations.computeNameMapperFromDirectResolvedTerms(tn.resolvedTerms));
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
            const tlinfo = new TypeLookupInfo(tn, tdecl, TypeCheckerRelations.computeNameMapperFromDirectResolvedTerms(tn.resolvedTerms));
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
            const tlinfo = new TypeLookupInfo(tn, tdecl, TypeCheckerRelations.computeNameMapperFromDirectResolvedTerms(tn.resolvedTerms));
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
            const tlinfo = new TypeLookupInfo(tn, tdecl, TypeCheckerRelations.computeNameMapperFromDirectResolvedTerms(tn.resolvedTerms));
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
            const tlinfo = new TypeLookupInfo(tn, tdecl, TypeCheckerRelations.computeNameMapperFromDirectResolvedTerms(tn.resolvedTerms));
            return new MemberLookupInfo<TypeFunctionDecl>(tlinfo, cci);
        }
        else {
            assert(false, "Need to handle inherited constants");
        }
    }

    resolveSpecialProvidesDecls(t: AbstractNominalTypeDecl, tconstrain: TemplateConstraintScope): TypeSignature[] {
        const tdecl = t as AbstractNominalTypeDecl;

        if(tdecl instanceof EnumTypeDecl) {
            return [this.wellknowntypes.get("KeyType") as TypeSignature, this.wellknowntypes.get("Some") as TypeSignature];
        }
        else if(tdecl instanceof RegexValidatorTypeDecl) {
            return [this.wellknowntypes.get("RegexValidator") as TypeSignature];
        }
        else if(tdecl instanceof ExRegexValidatorTypeDecl) {
            return [this.wellknowntypes.get("ExRegexValidator") as TypeSignature];
        }
        else if(tdecl instanceof PathValidatorTypeDecl) {
            return [this.wellknowntypes.get("PathValidator") as TypeSignature];
        }
        else if(tdecl instanceof DatatypeMemberEntityTypeDecl) {
            return [tdecl.parentTypeDecl];
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
            const pterms = TypeCheckerRelations.computeNameMapperFromDirectResolvedTerms(pnorm.resolvedTerms);
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
                assert(false, "Need to handle inherited constants");
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

    //Compute the upper bound of two types for use in control-flow join types
    joinTypes(t1: TypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        assert(t1 instanceof ErrorTypeSignature, "Checking subtypes on errors");
        assert(t2 instanceof ErrorTypeSignature, "Checking subtypes on errors");

        return this.simplifyUnionType(new UnionTypeSignature(t1.sinfo, t1, t2), tconstrain);
    }
}

export {
    RegexValidatorPack, ErrorRegexValidatorPack, SingleRegexValidatorPack, OrRegexValidatorPack,
    TypeLookupInfo, MemberLookupInfo,
    TypeCheckerRelations
};
