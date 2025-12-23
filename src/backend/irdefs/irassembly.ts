import { IRRegex, IRSourceInfo } from "./irsupport.js";
import { IRDashResultTypeSignature, IREListTypeSignature, IRFormatTypeSignature, IRLambdaParameterPackTypeSignature, IRNominalTypeSignature, IRTypeSignature } from "./irtype.js";
import { IRBody, IRLiteralCRegexExpression, IRLiteralUnicodeRegexExpression, IRSimpleExpression, IRStatement } from "./irbody.js";

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

class IRTestAssociation {
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

    isMatchWith(tmatch: IRTestAssociation): boolean {
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
    readonly association: IRTestAssociation[] | undefined;

    readonly body: IRBody;

    constructor(ikey: string, recursive: "recursive" | "recursive?" | undefined, params: IRInvokeParameterDecl[], resultType: IRTypeSignature, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, testkind: "errtest" | "chktest", association: IRTestAssociation[] | undefined, body: IRBody) {
        super(ikey, recursive, params, resultType, preconditions, postconditions, docstr, file, sinfo);
        this.testkind = testkind;
        this.association = association;
        this.body = body;
    }
}

class IRExampleDecl extends IRInvokeMetaDecl {
    readonly association: IRTestAssociation[] | undefined;

    readonly body: IRBody;

    constructor(ikey: string, recursive: "recursive" | "recursive?" | undefined, params: IRInvokeParameterDecl[], resultType: IRTypeSignature, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, association: IRTestAssociation[] | undefined, body: IRBody) {
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

    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, members: string[]) {
        super(tkey, [], [], [], "std", [], [], [], [], docstr, [], file, sinfo);
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
    readonly rechk: IRLiteralCRegexExpression | undefined;
    
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], saturatedProvides: IRTypeSignature[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, rechk: IRLiteralCRegexExpression | undefined) {
        super(tkey, invariants, validates, [], "std", saturatedProvides, [], allInvariants, allValidates, docstr, metatags, file, sinfo);
        this.rechk = rechk;
    }
}

class IRTypedeclStringDecl extends IRAbstractEntityTypeDecl {
    readonly rechk: IRLiteralUnicodeRegexExpression | undefined;
    
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], saturatedProvides: IRTypeSignature[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, rechk: IRLiteralUnicodeRegexExpression | undefined) {
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

class IRDatatypeMemberEntityTypeDecl extends IRAbstractEntityTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, invariants, validates, fields, etag, saturatedProvides, saturatedBFieldInfo, allInvariants, allValidates, docstr, metatags, file, sinfo);
    }
}

class IRDatatypeTypeDecl extends IRAbstractConceptTypeDecl {
    readonly dataelems: IRTypeSignature[];

    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, dataelems: IRTypeSignature[]) {
        super(tkey, invariants, validates, fields, saturatedProvides, saturatedBFieldInfo, docstr, metatags, file, sinfo);
        this.dataelems = dataelems;
    }
}

class IREnvironmentVariableInformation {
    readonly evname: string; //identifier or cstring
    readonly evtype: IRTypeSignature;
    readonly required: boolean;
    readonly optdefault: { stmts: IRStatement[], value: IRSimpleExpression } | undefined;

    constructor(evname: string, evtype: IRTypeSignature, required: boolean, optdefault: { stmts: IRStatement[], value: IRSimpleExpression } | undefined) {
        this.evname = evname;
        this.evtype = evtype;
        this.required = required;
        this.optdefault = optdefault;
    }
}

class IRResourceInformation {
    //TODO: fill this in
}


class IRTaskConfiguration {
    timeout: number | undefined;
    retry: {delay: number, tries: number} | undefined;
    priority: "immediate" | "fast" | "normal" | "longrunning" | "background" | "optional" | undefined;

    constructor(timeout: number | undefined, retry: {delay: number, tries: number} | undefined, priority: "immediate" | "fast" | "normal" | "longrunning" | "background" | "optional" | undefined) {
        this.timeout = timeout;
        this.retry = retry;
        this.priority = priority;
    }
}

class IRAPIDecl {
    readonly ikey: string;

    readonly params: IRInvokeParameterDecl[];    
    readonly resultType: IRTypeSignature;
    readonly eventType: IRTypeSignature | undefined;

    readonly preconditions: IRPreConditionDecl[];
    readonly postconditions: IRPostConditionDecl[];

    readonly configs: IRTaskConfiguration;

    readonly statusinfo: IRTypeSignature[];
    readonly envreqs: IREnvironmentVariableInformation[];
    readonly resourcereqs: IRResourceInformation;

    readonly body: IRBody;

    readonly docstr: IRDeclarationDocString | undefined;
    readonly metatags: IRDeclarationMetaTag[];

    readonly file: string;
    readonly sinfo: IRSourceInfo;

    constructor(ikey: string, params: IRInvokeParameterDecl[], resultType: IRTypeSignature, eventType: IRTypeSignature | undefined, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], configs: IRTaskConfiguration, statusinfo: IRTypeSignature[], envreqs: IREnvironmentVariableInformation[], resourcereqs: IRResourceInformation, body: IRBody, docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        this.ikey = ikey;
        this.params = params;
        this.resultType = resultType;
        this.eventType = eventType;
        this.preconditions = preconditions;
        this.postconditions = postconditions;
        this.configs = configs;
        this.statusinfo = statusinfo;
        this.envreqs = envreqs;
        this.resourcereqs = resourcereqs;
        this.body = body;
        this.docstr = docstr;
        this.metatags = metatags;
        this.file = file;
        this.sinfo = sinfo;
    }
}

class IRAgentDecl {
    readonly ikey: string;

    readonly params: IRInvokeParameterDecl[];    
    readonly resultType: IRTypeSignature | undefined; //This may be set on a per call-site basis
    readonly eventType: IRTypeSignature | undefined;

    readonly preconditions: IRPreConditionDecl[];
    readonly postconditions: IRPostConditionDecl[];

    readonly configs: IRTaskConfiguration;

    readonly statusinfo: IRTypeSignature[];
    readonly envreqs: IREnvironmentVariableInformation[];
    readonly resourcereqs: IRResourceInformation;

    readonly body: IRBody;

    readonly docstr: IRDeclarationDocString | undefined;
    readonly metatags: IRDeclarationMetaTag[];

    readonly file: string;
    readonly sinfo: IRSourceInfo;

    constructor(ikey: string, params: IRInvokeParameterDecl[], resultType: IRTypeSignature | undefined, eventType: IRTypeSignature | undefined, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], configs: IRTaskConfiguration, statusinfo: IRTypeSignature[], envreqs: IREnvironmentVariableInformation[], resourcereqs: IRResourceInformation, body: IRBody, docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        this.ikey = ikey;
        this.params = params;
        this.resultType = resultType;
        this.eventType = eventType;
        this.preconditions = preconditions;
        this.postconditions = postconditions;
        this.configs = configs;
        this.statusinfo = statusinfo;
        this.envreqs = envreqs;
        this.resourcereqs = resourcereqs;
        this.body = body;
        this.docstr = docstr;
        this.metatags = metatags;
        this.file = file;
        this.sinfo = sinfo;
    }
}

class IRTaskDecl {
    readonly tkey: string;

    readonly invariants: IRInvariantDecl[];
    readonly fields: IRMemberFieldDecl[];

    readonly docstr: IRDeclarationDocString | undefined;
    readonly metatags: IRDeclarationMetaTag[];

    readonly file: string;
    readonly sinfo: IRSourceInfo;

    readonly configs: IRTaskConfiguration;

    readonly statusinfo: IRTypeSignature[];
    readonly envreqs: IREnvironmentVariableInformation[];
    readonly resourcereqs: IRResourceInformation;
    readonly eventinfo: IRTypeSignature[];

    readonly imain: string; //invoke key of main task action
    readonly icleanup: {
        onterminate: string | undefined //invoke key of on-terminate action -- when we have a cancel/timeout/or parent abort that we cooperatively check and we are graceful in cleanup
        onerror: string | undefined //invoke key of on-error action -- when we abort from a runtime failure and we are bailing
        ondrop: string | undefined //invoke key of on-drop action -- when we have completed but our result is unused and we gracefully clean up
    };

    constructor(tkey: string, invariants: IRInvariantDecl[], fields: IRMemberFieldDecl[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, configs: IRTaskConfiguration, statusinfo: IRTypeSignature[], envreqs: IREnvironmentVariableInformation[], resourcereqs: IRResourceInformation, eventinfo: IRTypeSignature[], imain: string, icleanup: { onterminate: string | undefined; onerror: string | undefined; ondrop: string | undefined; }) {
        this.tkey = tkey;
        this.invariants = invariants;
        this.fields = fields;
        this.docstr = docstr;
        this.metatags = metatags;
        this.file = file;
        this.sinfo = sinfo;
        
        this.configs = configs;
        this.statusinfo = statusinfo;
        this.envreqs = envreqs;
        this.resourcereqs = resourcereqs;
        this.eventinfo = eventinfo;

        this.imain = imain;
        this.icleanup = icleanup;
    }
}

class IRAssembly {
    readonly regexps: IRRegex[] = [];

    readonly constants: IRConstantDecl[] = [];

    readonly tests: IRTestDecl[] = [];
    readonly examples: IRExampleDecl[] = [];

    readonly predicates: IRPredicateDecl[] = [];
    readonly invokes: IRInvokeDecl[] = [];
    readonly taskactions: IRTaskActionDecl[] = [];

    readonly primitives: IRPrimitiveEntityTypeDecl[] = [];
    readonly constructables: IRConstructableTypeDecl[] = [];
    readonly collections: IRAbstractCollectionTypeDecl[] = [];
    readonly eventlists: IREventListTypeDecl[] = [];

    readonly enums: IREnumTypeDecl[] = [];
    readonly typedecls: IRTypedeclTypeDecl[] = [];
    readonly cstringoftypedecls: IRTypedeclCStringDecl[] = [];
    readonly stringoftypedecls: IRTypedeclStringDecl[] = [];

    readonly entities: IREntityTypeDecl[] = [];
    readonly datamembers: IRDatatypeMemberEntityTypeDecl[] = [];

    readonly pconcepts: IRInternalConceptTypeDecl[] = [];
    readonly concepts: IRConceptTypeDecl[] = [];
    readonly datatypes: IRDatatypeTypeDecl[] = [];

    readonly apis: IRAPIDecl[] = [];
    readonly agents: IRAgentDecl[] = [];
    readonly tasks: IRTaskDecl[] = [];

    readonly alltypes: Map<string, IRAbstractNominalTypeDecl> = new Map<string, IRAbstractNominalTypeDecl>();
    readonly allinvokes: Map<string, IRInvokeMetaDecl> = new Map<string, IRInvokeMetaDecl>();

    readonly elists: IREListTypeSignature[] = [];
    readonly dashtypes: IRDashResultTypeSignature[] = [];
    readonly formats: IRFormatTypeSignature[] = [];
    readonly lpacks: IRLambdaParameterPackTypeSignature[] = [];

    readonly supertypes: Map<string, IRTypeSignature[]> = new Map<string, IRTypeSignature[]>();
    readonly subtypes: Map<string, IRTypeSignature[]> = new Map<string, IRTypeSignature[]>();

    readonly concretesubtypes: Map<string, IRTypeSignature[]> = new Map<string, IRTypeSignature[]>(); 

    readonly typefieldTopo: IRTypeSignature[][] = [];

    constructor() {
    }
}

export {
    IRPreConditionDecl, IRPostConditionDecl, IRInvariantDecl, IRValidateDecl,
    IRDeclarationDocString, IRDeclarationMetaTag,
    IRConstantDecl,
    IRInvokeParameterDecl, IRInvokeMetaDecl, IRTestAssociation,
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
    IRDatatypeMemberEntityTypeDecl, IRDatatypeTypeDecl,
    IREnvironmentVariableInformation, IRResourceInformation, IRTaskConfiguration,
    IRAPIDecl, IRAgentDecl, IRTaskDecl,
    IRAssembly
};