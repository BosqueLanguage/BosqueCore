import { IRRegex, IRSourceInfo } from "./irsupport";
import { IRNominalTypeSignature, IRTypeSignature } from "./irtype";
import { IRBlockStatement, IRBody, IRSimpleExpression, IRStatement } from "./irbody";

abstract class IRConditionDecl {
    readonly file: string;
    readonly sinfo: IRSourceInfo;

    readonly diagnosticTag: string | undefined;
    
    readonly stmts: IRStatement[];
    readonly value: IRSimpleExpression;

    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, stmts: IRStatement[], value: IRSimpleExpression) {
        this.file = file;
        this.sinfo = sinfo;
        
        this.diagnosticTag = diagnosticTag;

        this.stmts = stmts;
        this.value = value;
    }
}

class IRPreConditionDecl extends IRConditionDecl {
    readonly ikey: string;
    readonly requiresidx: number;
    
    readonly issoft: boolean;

    constructor(file: string, sinfo: IRSourceInfo, tag: string | undefined, ikey: string, requiresidx: number, issoft: boolean, stmts: IRStatement[], value: IRSimpleExpression) {
        super(file, sinfo, tag, stmts, value);
        this.ikey = ikey;
        this.requiresidx = requiresidx;
        this.issoft = issoft;
    }
}

class IRPostConditionDecl extends IRConditionDecl {
    readonly ikey: string;
    readonly ensuresidx: number;
    
    readonly issoft: boolean;
    
    constructor(file: string, sinfo: IRSourceInfo, tag: string | undefined, ikey: string, ensuresidx: number, issoft: boolean, stmts: IRStatement[], value: IRSimpleExpression) {
        super(file, sinfo, tag, stmts, value);
        this.ikey = ikey;
        this.ensuresidx = ensuresidx;
        this.issoft = issoft;
    }
}

class IRInvariantDecl extends IRConditionDecl {
    readonly tkey: string;
    readonly invariantidx: number;
    
    constructor(file: string, sinfo: IRSourceInfo, tag: string | undefined, tkey: string, invariantidx: number, stmts: IRStatement[], value: IRSimpleExpression) {
        super(file, sinfo, tag, stmts, value);
        this.tkey = tkey;
        this.invariantidx = invariantidx;
    }
}

class IRValidateDecl extends IRConditionDecl {
    readonly tkey: string;
    readonly validateidx: number;
    
    constructor(file: string, sinfo: IRSourceInfo, tag: string | undefined, tkey: string, validateidx: number, stmts: IRStatement[], value: IRSimpleExpression) {
        super(file, sinfo, tag, stmts, value);
        this.tkey = tkey;
        this.validateidx = validateidx;
    }
}

class IRDeclarationDocString {
    readonly text: string;

    constructor(text: string) {
        this.text = text;
    }
}

class IRDeclarationMetaTag {
    readonly name: string;
    readonly tags: {enumType: IRTypeSignature, tag: string}[];

    constructor(name: string, tags: {enumType: IRTypeSignature, tag: string}[]) {
        this.name = name;
        this.tags = tags;
    }
}

class IRConstantDecl {
    readonly ckey: string;

    readonly declaredType: IRTypeSignature;
    readonly stmts: IRStatement[];
    readonly value: IRSimpleExpression;

    readonly docstr: IRDeclarationDocString | undefined;

    constructor(ckey: string, declaredType: IRTypeSignature, stmts: IRStatement[], value: IRSimpleExpression, docstr: IRDeclarationDocString | undefined) {
        this.ckey = ckey;
        this.declaredType = declaredType;
        this.stmts = stmts;
        this.value = value;
        this.docstr = docstr;
    }
}

class IRInvokeParameterDecl {
    readonly name: string;
    readonly type: IRTypeSignature;
    readonly pkind: "ref" | "out" | "out?" | "inout" | undefined;

    readonly defaultValue: { stmts: IRStatement[], value: IRSimpleExpression } | undefined;
    
    constructor(name: string, type: IRTypeSignature, pkind: "ref" | "out" | "out?" | "inout" | undefined, defaultValue: { stmts: IRStatement[], value: IRSimpleExpression } | undefined) {
        this.name = name;
        this.type = type;
        this.pkind = pkind;
        this.defaultValue = defaultValue;
    }
}

abstract class IRInvokeMetaDecl {
    readonly ikey: string;

    readonly recursive: "recursive" | "recursive?" | undefined;
    readonly params: IRInvokeParameterDecl[];
    readonly resultType: IRTypeSignature;

    readonly preconditions: IRPreConditionDecl[];
    readonly postconditions: IRPostConditionDecl[];

    readonly docstr: IRDeclarationDocString | undefined;

    readonly file: string;
    readonly sinfo: IRSourceInfo;

    constructor(ikey: string, recursive: "recursive" | "recursive?" | undefined, params: IRInvokeParameterDecl[], resultType: IRTypeSignature, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo) {
        this.ikey = ikey;
        this.recursive = recursive;
        this.params = params;
        this.resultType = resultType;
        this.preconditions = preconditions;
        this.postconditions = postconditions;
        this.docstr = docstr;
        this.file = file;
        this.sinfo = sinfo;
    }
}

class TestAssociation {
    readonly file: string | undefined;
    readonly ns: string | undefined;
    readonly ontype: string | undefined;
    readonly onmember: string | undefined;

    constructor(file: string | undefined, ns: string | undefined, ontype: string | undefined, onmember: string | undefined) {
        this.file = file;
        this.ns = ns;
        this.ontype = ontype;
        this.onmember = onmember;
    }

    isMatchWith(tmatch: TestAssociation): boolean {
        if(tmatch.file !== undefined && this.file !== tmatch.file) {
            return false;
        }

        if(tmatch.ns !== undefined && this.ns !== tmatch.ns) {
            return false;
        }

        if(tmatch.ontype !== undefined && this.ontype !== tmatch.ontype) {
            return false;
        }

        if(tmatch.onmember !== undefined && this.onmember !== tmatch.onmember) {
            return false;
        }

        return true;
    }
}

class IRPredicateDecl extends IRInvokeMetaDecl {
    constructor(ikey: string, recursive: "recursive" | "recursive?" | undefined, params: IRInvokeParameterDecl[], resultType: IRTypeSignature, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo) {
        super(ikey, recursive, params, resultType, preconditions, postconditions, docstr, file, sinfo);
    }
}

class IRTestDecl extends IRInvokeMetaDecl {
    readonly testkind: "errtest" | "chktest";
    readonly association: TestAssociation[] | undefined;

    readonly body: IRBody;

    constructor(ikey: string, recursive: "recursive" | "recursive?" | undefined, params: IRInvokeParameterDecl[], resultType: IRTypeSignature, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, testkind: "errtest" | "chktest", association: TestAssociation[] | undefined, body: IRBody) {
        super(ikey, recursive, params, resultType, preconditions, postconditions, docstr, file, sinfo);
        this.testkind = testkind;
        this.association = association;
        this.body = body;
    }
}

class IRExampleDecl extends IRInvokeMetaDecl {
    readonly association: TestAssociation[] | undefined;

    readonly body: IRBody;

    constructor(ikey: string, recursive: "recursive" | "recursive?" | undefined, params: IRInvokeParameterDecl[], resultType: IRTypeSignature, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, association: TestAssociation[] | undefined, body: IRBody) {
        super(ikey, recursive, params, resultType, preconditions, postconditions, docstr, file, sinfo);
        this.association = association;
        this.body = body;
    }
} 

class IRInvokeDecl extends IRInvokeMetaDecl {
    readonly body: IRBody;

    constructor(ikey: string, recursive: "recursive" | "recursive?" | undefined, params: IRInvokeParameterDecl[], resultType: IRTypeSignature, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, body: IRBody) {
        super(ikey, recursive, params, resultType, preconditions, postconditions, docstr, file, sinfo);
        this.body = body;
    }
}

class IRTaskActionDecl extends IRInvokeMetaDecl {
    readonly body: IRBody;

    constructor(ikey: string, recursive: "recursive" | "recursive?" | undefined, params: IRInvokeParameterDecl[], resultType: IRTypeSignature, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, body: IRBody) {
        super(ikey, recursive, params, resultType, preconditions, postconditions, docstr, file, sinfo);
        this.body = body;
    }
}

class IRMemberFieldDecl {
    readonly fkey: string;

    readonly enclosingType: IRNominalTypeSignature;
    readonly name: string;
    readonly declaredType: IRTypeSignature;
    readonly defaultValue: { stmts: IRStatement[], value: IRSimpleExpression } | undefined;

    readonly docstr: IRDeclarationDocString | undefined;
    readonly metatags: IRDeclarationMetaTag[];

    constructor(fkey: string, enclosingType: IRNominalTypeSignature, name: string, declaredType: IRTypeSignature, defaultValue: { stmts: IRStatement[], value: IRSimpleExpression } | undefined, docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[]) {
        this.fkey = fkey;
        this.enclosingType = enclosingType;
        this.name = name;
        this.declaredType = declaredType;
        this.defaultValue = defaultValue;

        this.docstr = docstr;
        this.metatags = metatags;
    }
}

abstract class IRAbstractNominalTypeDecl {
    readonly tkey: string;

    readonly invariants: IRInvariantDecl[];
    readonly validates: IRValidateDecl[];
    readonly fields: IRMemberFieldDecl[];

    readonly etag: "std" | "status" | "event";

    readonly saturatedProvides: IRTypeSignature[];
    readonly saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string }[];

    readonly allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[];
    readonly allValidates: { containingtype: IRNominalTypeSignature, ii: number }[];
    
    //TODO vtable info here

    readonly docstr: IRDeclarationDocString | undefined;
    readonly metatags: IRDeclarationMetaTag[];

    readonly file: string;
    readonly sinfo: IRSourceInfo;

    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        this.tkey = tkey;
        this.invariants = invariants;
        this.validates = validates;
        this.fields = fields;
        this.etag = etag;
        this.saturatedProvides = saturatedProvides;
        this.saturatedBFieldInfo = saturatedBFieldInfo;
        this.allInvariants = allInvariants;
        this.allValidates = allValidates;
        this.docstr = docstr;
        this.metatags = metatags;

        //TODO vtable info here

        this.file = file;
        this.sinfo = sinfo;
    }
}

abstract class IRAbstractEntityTypeDecl extends IRAbstractNominalTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, invariants, validates, fields, etag, saturatedProvides, saturatedBFieldInfo, allInvariants, allValidates, docstr, metatags, file, sinfo);
    }
}

class IREnumTypeDecl extends IRAbstractEntityTypeDecl {
    readonly members: string[];

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], file: string, sinfo: IRSourceInfo, members: string[]) {
        super(tkey, [], [], [], "std", saturatedProvides, [], [], [], undefined, [], file, sinfo);
        this.members = members;
    }
}

class IRTypedeclTypeDecl extends IRAbstractEntityTypeDecl {
    readonly valuetype: IRTypeSignature;
    
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], saturatedProvides: IRTypeSignature[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, valuetype: IRTypeSignature) {
        super(tkey, invariants, validates, [], "std", saturatedProvides, [], allInvariants, allValidates, docstr, metatags, file, sinfo);
        this.valuetype = valuetype;
    }
}

class IRTypedeclCStringDecl extends IRAbstractEntityTypeDecl {
    readonly rechk: IRRegex;
    
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], saturatedProvides: IRTypeSignature[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, rechk: IRRegex) {
        super(tkey, invariants, validates, [], "std", saturatedProvides, [], allInvariants, allValidates, docstr, metatags, file, sinfo);
        this.rechk = rechk;
    }
}

class IRTypedeclStringDecl extends IRAbstractEntityTypeDecl {
    readonly rechk: IRRegex;
    
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], saturatedProvides: IRTypeSignature[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, rechk: IRRegex) {
        super(tkey, invariants, validates, [], "std", saturatedProvides, [], allInvariants, allValidates, docstr, metatags, file, sinfo);
        this.rechk = rechk;
    }
}

//TODO: Path typedecl

abstract class IRInternalEntityTypeDecl extends IRAbstractEntityTypeDecl {
    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, [], [], [], "std", saturatedProvides, [], [], [], docstr, metatags, file, sinfo);
    }
}

class IRPrimitiveEntityTypeDecl extends IRInternalEntityTypeDecl {
    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo) {
        super(tkey, [], docstr, [], file, sinfo);
    }
}

abstract class IRConstructableTypeDecl extends IRInternalEntityTypeDecl {
    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo) {
        super(tkey, saturatedProvides, docstr, [], file, sinfo);
    }
}

class IROkTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
    }
}

class IRFailTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
    }
}

class IRAPIErrorTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
    }
}

class IRAPIRejectedTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
    }
}

class IRAPIDeniedTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
    }
}

class IRAPIFlaggedTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
    }
}

class IRAPISuccessTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
    }
}

class IRSomeTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ttype = ttype;
    }
}

class IRMapEntryTypeDecl extends IRConstructableTypeDecl {
    readonly ktype: IRTypeSignature;
    readonly vtype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ktype: IRTypeSignature, vtype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ktype = ktype;
        this.vtype = vtype;
    }
}

abstract class IRAbstractCollectionTypeDecl extends IRInternalEntityTypeDecl {
    readonly oftype: IRTypeSignature;

    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature) {
        super(tkey, [], docstr, [], file, sinfo);
        this.oftype = oftype;
    }
}

class IRListTypeDecl extends IRAbstractCollectionTypeDecl {
    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature) {
        super(tkey, docstr, file, sinfo, oftype);
    }
}

class IRStackTypeDecl extends IRAbstractCollectionTypeDecl {
    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature) {
        super(tkey, docstr, file, sinfo, oftype);
    }
}

class IRQueueTypeDecl extends IRAbstractCollectionTypeDecl {
    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature) {
        super(tkey, docstr, file, sinfo, oftype);
    }
}

class IRSetTypeDecl extends IRAbstractCollectionTypeDecl {
    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature) {
        super(tkey, docstr, file, sinfo, oftype);
    }
}

class IRMapTypeDecl extends IRAbstractCollectionTypeDecl {
    readonly ktype: IRTypeSignature;
    readonly vtype: IRTypeSignature;

    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature, ktype: IRTypeSignature, vtype: IRTypeSignature) {
        super(tkey, docstr, file, sinfo, oftype);
        this.ktype = ktype;
        this.vtype = vtype;
    }
}

class IREventListTypeDecl extends IRInternalEntityTypeDecl {
    readonly etype: IRTypeSignature;

    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, etype: IRTypeSignature) {
        super(tkey, [], docstr, [], file, sinfo);
        this.etype = etype;
    }
}

class IREntityTypeDecl extends IRAbstractEntityTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, invariants, validates, fields, etag, saturatedProvides, saturatedBFieldInfo, allInvariants, allValidates, docstr, metatags, file, sinfo);
    }
}

abstract class IRAbstractConceptTypeDecl extends IRAbstractNominalTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, invariants, validates, fields, "std", saturatedProvides, saturatedBFieldInfo, [], [], docstr, metatags, file, sinfo);
    }
}

abstract class IRInternalConceptTypeDecl extends IRAbstractConceptTypeDecl {
    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, [], [], [], [], [], docstr, metatags, file, sinfo);
    }
}

class IROptionTypeDecl extends IRInternalConceptTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly sometype: IRTypeSignature;

    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, sometype: IRTypeSignature) {
        super(tkey, docstr, [], file, sinfo);
        this.ttype = ttype;
        this.sometype = sometype;
    }
}

class IRResultTypeDecl extends IRInternalConceptTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    readonly oktype: IRTypeSignature;
    readonly failtype: IRTypeSignature;

    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature, oktype: IRTypeSignature, failtype: IRTypeSignature) {
        super(tkey, docstr, [], file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
        this.oktype = oktype;
        this.failtype = failtype;
    }
}

class IRAPIResultTypeDecl extends IRInternalConceptTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    readonly errortype: IRTypeSignature;
    readonly rejectedtype: IRTypeSignature;
    readonly deniedtype: IRTypeSignature;
    readonly flaggedtype: IRTypeSignature;
    readonly successtype: IRTypeSignature;

    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature, errortype: IRTypeSignature, rejectedtype: IRTypeSignature, deniedtype: IRTypeSignature, flaggedtype: IRTypeSignature, successtype: IRTypeSignature) {
        super(tkey, docstr, [], file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
        this.errortype = errortype;
        this.rejectedtype = rejectedtype;
        this.deniedtype = deniedtype;
        this.flaggedtype = flaggedtype;
        this.successtype = successtype;
    }
}

class IRConceptTypeDecl extends IRAbstractConceptTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, invariants, validates, fields, saturatedProvides, saturatedBFieldInfo, docstr, metatags, file, sinfo);
    }
}

class DatatypeMemberEntityTypeDecl extends AbstractEntityTypeDecl {
    readonly fields: MemberFieldDecl[] = [];
    readonly parentTypeDecl: DatatypeTypeDecl;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, etag: AdditionalTypeDeclTag, parentTypeDecl: DatatypeTypeDecl) {
        super(file, sinfo, attributes, ns, name, etag);

        this.parentTypeDecl = parentTypeDecl;
    }

    emit(fmt: CodeFormatter): string {
        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        if(this.fields.length !== 0) {
            bg.push(this.fields.map((ff) => ff.emit(fmt)));
        }
        fmt.indentPop();

        return this.name + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class DatatypeTypeDecl extends AbstractConceptTypeDecl {
}

class EnvironmentVariableInformation {
    readonly evname: string; //identifier or cstring
    readonly evtype: TypeSignature;
    readonly required: boolean;
    readonly optdefault: Expression | undefined;

    constructor(evname: string, evtype: TypeSignature, required: boolean, optdefault: Expression | undefined) {
        this.evname = evname;
        this.evtype = evtype;
        this.required = required;
        this.optdefault = optdefault;
    }

    emit(fmt: CodeFormatter): string {
        const optional = this.required ? "" : "?";
        if(this.optdefault === undefined) {
            return fmt.indent(`${this.evname}${optional}: ${this.evtype.emit()}`);
        }
        else {
            return fmt.indent(`${this.evname}${optional}: ${this.evtype.emit()} = ${this.optdefault.emit(true, fmt)}`);
        }
    }
}

class ResourceInformation {
    readonly pathglobs: { pg: Expression[], optas: Expression | undefined }[]; //Literal glob, constant refernence, or env var reference

    constructor(pathglobs: { pg: Expression[], optas: Expression | undefined }[]) {
        this.pathglobs = pathglobs;
    }

    static emitSingleRInfo(fmt: CodeFormatter, pg: Expression[], optas: Expression | undefined): string {
        if(optas === undefined) {
            if(pg.length === 1) {
                return fmt.indent(pg[0].emit(true, fmt));
            }
            else {
                return fmt.indent(`[${pg.map((pge) => pge.emit(true, fmt)).join(", ")}]`);
            }
        }
        else {
            if(pg.length === 1) {
                return fmt.indent(`${pg[0].emit(true, fmt)} as ${optas.emit(true, fmt)}`);
            }
            else {
                return fmt.indent(`[${pg.map((pge) => pge.emit(true, fmt)).join(", ")}] as ${optas.emit(true, fmt)}`);
            }
        }
    }
}

class APIDecl extends AbstractCoreDecl {
    readonly params: InvokeParameterDecl[];    
    readonly resultType: TypeSignature;
    readonly eventType: TypeSignature | undefined;

    readonly preconditions: PreConditionDecl[];
    readonly postconditions: PostConditionDecl[];

    readonly configs: TaskConfiguration;

    readonly statusinfo: TypeSignature[];
    readonly envreqs: EnvironmentVariableInformation[];
    readonly resourcereqs: ResourceInformation;

    readonly body: BodyImplementation;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, params: InvokeParameterDecl[], resultType: TypeSignature, eventType: TypeSignature | undefined, preconds: PreConditionDecl[], postconds: PostConditionDecl[], configs: TaskConfiguration, statusinfo: TypeSignature[], envreqs: EnvironmentVariableInformation[], resourcereqs: ResourceInformation, body: BodyImplementation) {
        super(file, sinfo, attributes, name);

        this.params = params;
        this.resultType = resultType;
        this.eventType = eventType;

        this.preconditions = preconds;
        this.postconditions = postconds

        this.configs = configs;

        this.statusinfo = statusinfo;
        this.envreqs = envreqs;
        this.resourcereqs = resourcereqs;

        this.body = body;
    }

    emitMetaInfo(fmt: CodeFormatter): string | undefined {
        fmt.indentPush();

        let prec: string[] = [];
        if(this.preconditions.length !== 0) {
            prec = this.preconditions.map((pc) => fmt.indent(pc.emit(fmt)));
        }

        let postc: string[] = [];
        if(this.postconditions.length !== 0) {
            postc = this.postconditions.map((pc) => fmt.indent(pc.emit(fmt)));
        }

        let configs: string[] = [];
        if(this.configs !== undefined) {
            configs = [fmt.indent(`configs { ${this.configs.emit()} }`)];
        }

        let status: string[] = [];
        if(this.statusinfo.length !== 0) {
            status = [fmt.indent(`status ${this.statusinfo.map((so) => so.emit()).join(" | ")};`)];
        }

        let resources: string[] = [];
        if(this.resourcereqs.pathglobs.length !== 0) {
            const rrs = this.resourcereqs.pathglobs.map((rr) => ResourceInformation.emitSingleRInfo(fmt, rr.pg, rr.optas));
            resources = [fmt.indent(`resource { ${rrs.join(", ")} }`)];
        }
        
        let evs: string[] = [];
        if(this.envreqs.length !== 0) {
            const vvl = this.envreqs.map((ev) => ev.emit(fmt));
            evs = [fmt.indent(`env { ${vvl.join(", ")} }`)];
        }

        fmt.indentPop();
        if(prec.length === 0 && postc.length === 0 && status.length === 0 && evs.length === 0) {
            return undefined;
        }
        else {
            return [...prec, ...postc, ...configs, ...status, ...evs, ...resources].join("\n");
        }
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        const params = this.params.map((p) => p.emit(fmt)).join(", ");
        const result = this.resultType.emit();

        const minfo = this.emitMetaInfo(fmt);
        return `${attrs}api ${this.name}(${params}): ${result}${this.eventType !== undefined ? ", " + this.eventType.emit() : ""} ${this.body.emit(fmt, minfo)}`;
    }
}

class AgentDecl extends AbstractCoreDecl {
    readonly params: InvokeParameterDecl[];    
    readonly resultType: TypeSignature | undefined; //This may be set on a per call-site basis
    readonly eventType: TypeSignature | undefined;

    readonly preconditions: PreConditionDecl[];
    readonly postconditions: PostConditionDecl[];

    readonly configs: TaskConfiguration;

    readonly statusinfo: TypeSignature[];
    readonly envreqs: EnvironmentVariableInformation[];
    readonly resourcereqs: ResourceInformation;

    readonly body: BodyImplementation;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, params: InvokeParameterDecl[], resultType: TypeSignature | undefined, eventType: TypeSignature | undefined, preconds: PreConditionDecl[], postconds: PostConditionDecl[], configs: TaskConfiguration, statusinfo: TypeSignature[], envreqs: EnvironmentVariableInformation[], resourcereqs: ResourceInformation, body: BodyImplementation) {
        super(file, sinfo, attributes, name);

        this.params = params;
        this.resultType = resultType;
        this.eventType = eventType;

        this.preconditions = preconds;
        this.postconditions = postconds

        this.configs = configs;

        this.statusinfo = statusinfo;
        this.envreqs = envreqs;
        this.resourcereqs = resourcereqs;

        this.body = body;
    }

    emitMetaInfo(fmt: CodeFormatter): string | undefined {
        fmt.indentPush();

        let prec: string[] = [];
        if(this.preconditions.length !== 0) {
            prec = this.preconditions.map((pc) => fmt.indent(pc.emit(fmt)));
        }

        let postc: string[] = [];
        if(this.postconditions.length !== 0) {
            postc = this.postconditions.map((pc) => fmt.indent(pc.emit(fmt)));
        }

        let configs: string[] = [];
        if(this.configs !== undefined) {
            configs = [fmt.indent(`configs { ${this.configs.emit()} }`)];
        }

        let status: string[] = [];
        if(this.statusinfo.length !== 0) {
            status = [fmt.indent(`status ${this.statusinfo.map((so) => so.emit()).join(" | ")};`)];
        }

        let resources: string[] = [];
        if(this.resourcereqs.pathglobs.length !== 0) {
            const rrs = this.resourcereqs.pathglobs.map((rr) => ResourceInformation.emitSingleRInfo(fmt, rr.pg, rr.optas));
            resources = [fmt.indent(`resource { ${rrs.join(", ")} }`)];
        }
        
        let evs: string[] = [];
        if(this.envreqs.length !== 0) {
            const vvl = this.envreqs.map((ev) => ev.emit(fmt));
            evs = [fmt.indent(`env{ ${vvl.join(", ")} }`)];
        }

        fmt.indentPop();
        if(prec.length === 0 && postc.length === 0 && status.length === 0 && evs.length === 0) {
            return undefined;
        }
        else {
            return [...prec, ...postc, ...configs, ...status, ...evs, ...resources].join("\n");
        }
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        const params = this.params.map((p) => p.emit(fmt)).join(", ");
        const iresult = this.resultType === undefined ? "<T>" : "";
        const eresult = this.resultType !== undefined ? (": " + this.resultType.emit()) : "";
        const eevent = this.eventType !== undefined ? (this.resultType !== undefined ? ", " : " ") + this.eventType.emit() : "";

        const minfo = this.emitMetaInfo(fmt);
        return `${attrs}agent ${this.name}${iresult}(${params})${eresult}${eevent} ${this.body.emit(fmt, minfo)}`;
    }
}

class TaskDecl extends AbstractNominalTypeDecl {
    readonly fields: MemberFieldDecl[] = [];
    readonly selfmethods: TaskMethodDecl[] = [];
    readonly actions: TaskActionDecl[] = [];

    readonly configs: TaskConfiguration = new TaskConfiguration(undefined, undefined, undefined);

    readonly statusinfo: TypeSignature[] = [];
    readonly envreqs: EnvironmentVariableInformation[] = [];
    readonly resourcereqs: ResourceInformation = new ResourceInformation([]);
    readonly eventinfo: TypeSignature[] = [];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string) {
        super(file, sinfo, attributes, ns, name, AdditionalTypeDeclTag.Std);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const mg: string[][] = [];
        
        const confstr = this.configs.emit();
        if(confstr !== undefined) {
            mg.push([fmt.indent(`configs { ${confstr} }`)]);
        }

        if(this.statusinfo.length !== 0) {
            mg.push([fmt.indent(`status ${this.statusinfo.map((so) => so.emit()).join(" | ")};`)]);
        }

        if(this.resourcereqs.pathglobs.length !== 0) {
            const rrs = this.resourcereqs.pathglobs.map((rr) => ResourceInformation.emitSingleRInfo(fmt, rr.pg, rr.optas));
            mg.push([fmt.indent(`resource { ${rrs.join(", ")} }`)]);
        }
        
        if(this.envreqs.length !== 0) {
            const vvl = this.envreqs.map((ev) => ev.emit(fmt));
            mg.push([fmt.indent(`env{ ${vvl.join(", ")} }`)]);
        }

        if(this.eventinfo.length !== 0) {
            mg.push([fmt.indent(`event ${this.eventinfo.map((et) => et.emit()).join(" | ")};`)]);
        }

        if(this.fields.length !== 0) {
            mg.push(this.fields.map((ff) => ff.emit(fmt)));
        }
        if(this.selfmethods.length !== 0) {
            mg.push(this.selfmethods.map((sm) => sm.emit(fmt)));
        }
        if(this.actions.length !== 0) {
            mg.push(this.actions.map((act) => act.emit(fmt)));
        }
        fmt.indentPop();

        let rootdecl = attrs + "task " + this.name + this.emitTerms(); 

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        let etail = "";
        if(bg.length !== 0) {
            etail = " {\n" + this.joinBodyGroups([...mg, ...bg]) + fmt.indent("\n}");
        }

        return `${rootdecl}${etail}`;
    }
}

class IRAssembly {
    readonly regexps: IRRegex[];

    constructor(regexps: IRRegex[]) {
        this.regexps = regexps;
    }
}

export {
    IRPreConditionDecl, IRPostConditionDecl, IRInvariantDecl, IRValidateDecl,
    IRDeclarationDocString, IRDeclarationMetaTag,
    IRConstantDecl,
    IRInvokeParameterDecl, IRInvokeMetaDecl, TestAssociation,
    IRPredicateDecl, IRTestDecl, IRExampleDecl, IRInvokeDecl, IRTaskActionDecl,
    IRMemberFieldDecl,
    IRAbstractNominalTypeDecl, IRAbstractEntityTypeDecl, 
    IREnumTypeDecl, 
    IRTypedeclTypeDecl, IRTypedeclCStringDecl, IRTypedeclStringDecl,
    IRInternalEntityTypeDecl, IRPrimitiveEntityTypeDecl, IRConstructableTypeDecl, 
    IROkTypeDecl, IRFailTypeDecl,
    IRAPIDeniedTypeDecl, IRAPIErrorTypeDecl, IRAPIRejectedTypeDecl, IRAPIFlaggedTypeDecl, IRAPISuccessTypeDecl,
    IRSomeTypeDecl, IRMapEntryTypeDecl,
    IRAbstractCollectionTypeDecl, IRListTypeDecl, IRStackTypeDecl, IRQueueTypeDecl, IRSetTypeDecl, IRMapTypeDecl,
    IREventListTypeDecl,
    IREntityTypeDecl,
    IRAbstractConceptTypeDecl, IRInternalConceptTypeDecl,
    IROptionTypeDecl, IRResultTypeDecl, IRAPIResultTypeDecl, 
    IRConceptTypeDecl,
    IRAssembly
};