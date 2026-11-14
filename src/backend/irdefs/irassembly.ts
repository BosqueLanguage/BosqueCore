import { IRCRegex, IRURegex, IRSourceInfo, IRCodeFileInfo } from "./irsupport.js";
import { IRDashResultTypeSignature, IREListTypeSignature, IRFormatTypeSignature, IRLambdaParameterPackTypeSignature, IRNominalTypeSignature, IRTypeSignature } from "./irtype.js";
import { IRBody, IRImmediateExpression, IRLiteralCRegexExpression, IRLiteralFormatCStringExpression, IRLiteralFormatStringExpression, IRLiteralUnicodeRegexExpression, IRSimpleExpression, IRStatement } from "./irbody.js";

import assert from "node:assert";

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
    readonly skind: "lcapture" | "this" | "self" | undefined;

    readonly defaultValue: { stmts: IRStatement[], value: IRSimpleExpression } | undefined;
    
    constructor(name: string, type: IRTypeSignature, pkind: "ref" | "out" | "out?" | "inout" | undefined, skind: "lcapture" | "this" | "self" | undefined, defaultValue: { stmts: IRStatement[], value: IRSimpleExpression } | undefined) {
        this.name = name;
        this.type = type;
        this.pkind = pkind;
        this.skind = skind;
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
    readonly fname: string;
    readonly declaredType: IRTypeSignature;
    readonly defaultValue: { stmts: IRStatement[], value: IRSimpleExpression, isconst: boolean } | undefined;

    readonly docstr: IRDeclarationDocString | undefined;
    readonly metatags: IRDeclarationMetaTag[];

    constructor(fkey: string, enclosingType: IRNominalTypeSignature, fname: string, declaredType: IRTypeSignature, defaultValue: { stmts: IRStatement[], value: IRSimpleExpression, isconst: boolean } | undefined, docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[]) {
        this.fkey = fkey;
        this.enclosingType = enclosingType;
        this.fname = fname;
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
    readonly saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[];

    readonly allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[];
    readonly allValidates: { containingtype: IRNominalTypeSignature, ii: number }[];
    
    //TODO vtable info here

    readonly docstr: IRDeclarationDocString | undefined;
    readonly metatags: IRDeclarationMetaTag[];

    readonly file: string;
    readonly sinfo: IRSourceInfo;

    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
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

    abstract getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[];

    static jsonEmitMeta_IRAbstractNominalTypeDecl(tsig: IRAbstractNominalTypeDecl): object {
        return { 
            tkey: tsig.tkey, 

            //readonly invariants: IRInvariantDecl[];
            //readonly validates: IRValidateDecl[];
            //readonly fields: IRMemberFieldDecl[];

            //readonly etag: "std" | "status" | "event";

            //readonly saturatedProvides: IRTypeSignature[];
            //readonly saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[];

            //readonly allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[];
            //readonly allValidates: { containingtype: IRNominalTypeSignature, ii: number }[];
    
            //TODO vtable info here

            docstr: tsig.docstr == undefined ? null : ["some", tsig.docstr.text],
            //readonly metatags: IRDeclarationMetaTag[];

            file: tsig.file,
            sinfo: tsig.sinfo.jsonEmit()
        };
    }

    static jsonParseMeta_IRAbstractNominalTypeDecl(obj: any): [string, IRInvariantDecl[], IRValidateDecl[], IRMemberFieldDecl[], "std" | "status" | "event", IRTypeSignature[], { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], { containingtype: IRNominalTypeSignature, ii: number }[], { containingtype: IRNominalTypeSignature, ii: number }[], IRDeclarationDocString | undefined, IRDeclarationMetaTag[], string, IRSourceInfo] {
        return [
            obj.tkey,
            [], //obj.invariants,
            [], //obj.validates,
            [], //obj.fields,
            "std", //obj.etag,
            [], //obj.saturatedProvides,
            [], //obj.saturatedBFieldInfo,
            [], //obj.allInvariants,
            [], //obj.allValidates,
            obj.docstr == null ? undefined : new IRDeclarationDocString(obj.docstr[1]),
            [], //obj.metatags,
            obj.file,
            IRSourceInfo.jsonParse(obj.sinfo)
        ]
    }

    static jsonEmit_IRAbstractNominalTypeDecl(tsig: IRAbstractNominalTypeDecl): object {
        if(tsig instanceof IREnumTypeDecl) {
            return ["Assembly::EnumTypeDecl", IREnumTypeDecl.jsonEmit_IREnumTypeDecl(tsig)];
        }
        else if(tsig instanceof IRTypedeclSimpleTypeDecl) {
            return ["Assembly::TypedeclSimpleTypeDecl", IRTypedeclSimpleTypeDecl.jsonEmit_IRTypedeclSimpleTypeDecl(tsig)];
        }
        else if(tsig instanceof IRTypedeclBoundedTypeDecl) {
            return ["Assembly::TypedeclBoundedTypeDecl", IRTypedeclBoundedTypeDecl.jsonEmit_IRTypedeclBoundedTypeDecl(tsig)];
        }
        else if(tsig instanceof IRTypedeclCStringTypeDecl) {
            return ["Assembly::TypedeclCStringTypeDecl", IRTypedeclCStringTypeDecl.jsonEmit_IRTypedeclCStringTypeDecl(tsig)];
        }
        else if(tsig instanceof IRTypedeclStringTypeDecl) {
            return ["Assembly::TypedeclStringTypeDecl", IRTypedeclStringTypeDecl.jsonEmit_IRTypedeclStringTypeDecl(tsig)];
        }
        else if(tsig instanceof IRPrimitiveEntityTypeDecl) {
            return ["Assembly::PrimitiveEntityTypeDecl", IRPrimitiveEntityTypeDecl.jsonEmit_IRPrimitiveEntityTypeDecl(tsig)];
        }
        else if(tsig instanceof IROkTypeDecl) {
            return ["Assembly::OkTypeDecl", IROkTypeDecl.jsonEmit_IROkTypeDecl(tsig)];
        }
        else if(tsig instanceof IRFailTypeDecl) {
            return ["Assembly::FailTypeDecl", IRFailTypeDecl.jsonEmit_IRFailTypeDecl(tsig)];
        }
        else if(tsig instanceof IRAPIErrorTypeDecl) {
            return ["Assembly::APIErrorTypeDecl", IRAPIErrorTypeDecl.jsonEmit_IRAPIErrorTypeDecl(tsig)];
        }
        else if(tsig instanceof IRAPIRejectedTypeDecl) {
            return ["Assembly::APIRejectedTypeDecl", IRAPIRejectedTypeDecl.jsonEmit_IRAPIRejectedTypeDecl(tsig)];
        }
        else if(tsig instanceof IRAPIDeniedTypeDecl) {
            return ["Assembly::APIDeniedTypeDecl", IRAPIDeniedTypeDecl.jsonEmit_IRAPIDeniedTypeDecl(tsig)];
        }
        else if(tsig instanceof IRAPIDroppedTypeDecl) {
            return ["Assembly::APIDroppedTypeDecl", IRAPIDroppedTypeDecl.jsonEmit_IRAPIDroppedTypeDecl(tsig)];
        }
        else if(tsig instanceof IRAPISuccessTypeDecl) {
            return ["Assembly::APISuccessTypeDecl", IRAPISuccessTypeDecl.jsonEmit_IRAPISuccessTypeDecl(tsig)];
        }
        else if(tsig instanceof IRMapEntryTypeDecl) {
            return ["Assembly::MapEntryTypeDecl", IRMapEntryTypeDecl.jsonEmit_IRMapEntryTypeDecl(tsig)];
        }
        else if(tsig instanceof IRListTypeDecl) {
            return ["Assembly::ListTypeDecl", IRListTypeDecl.jsonEmit_IRListTypeDecl(tsig)];
        }
        else if(tsig instanceof IRStackTypeDecl) {
            return ["Assembly::StackTypeDecl", IRStackTypeDecl.jsonEmit_IRStackTypeDecl(tsig)];
        }
        else if(tsig instanceof IRQueueTypeDecl) {
            return ["Assembly::QueueTypeDecl", IRQueueTypeDecl.jsonEmit_IRQueueTypeDecl(tsig)];
        }
        else if(tsig instanceof IRSetTypeDecl) {
            return ["Assembly::SetTypeDecl", IRSetTypeDecl.jsonEmit_IRSetTypeDecl(tsig)];
        }
        else if(tsig instanceof IRMapTypeDecl) {
            return ["Assembly::MapTypeDecl", IRMapTypeDecl.jsonEmit_IRMapTypeDecl(tsig)];
        }
        else if(tsig instanceof IREventListTypeDecl) {
            return ["Assembly::EventListTypeDecl", IREventListTypeDecl.jsonEmit_IREventListTypeDecl(tsig)];
        }
        else if(tsig instanceof IREntityTypeDecl) {
            return ["Assembly::EntityTypeDecl", IREntityTypeDecl.jsonEmit_IREntityTypeDecl(tsig)];
        }
        else if(tsig instanceof IROptionTypeDecl) {
            return ["Assembly::OptionTypeDecl", IROptionTypeDecl.jsonEmit_IROptionTypeDecl(tsig)];
        }
        else if(tsig instanceof IRResultTypeDecl) {
            return ["Assembly::ResultTypeDecl", IRResultTypeDecl.jsonEmit_IRResultTypeDecl(tsig)];
        }
        else if(tsig instanceof IRAPIResultTypeDecl) {
            return ["Assembly::APIResultTypeDecl", IRAPIResultTypeDecl.jsonEmit_IRAPIResultTypeDecl(tsig)];
        }
        else if(tsig instanceof IRConceptTypeDecl) {
            return ["Assembly::ConceptTypeDecl", IRConceptTypeDecl.jsonEmit_IRConceptTypeDecl(tsig)];
        }
        else if(tsig instanceof IRDatatypeMemberEntityTypeDecl) {
            return ["Assembly::DatatypeMemberEntityTypeDecl", IRDatatypeMemberEntityTypeDecl.jsonEmit_IRDatatypeMemberEntityTypeDecl(tsig)];
        }
        else if(tsig instanceof IRDatatypeTypeDecl) {
            return ["Assembly::DatatypeTypeDecl", IRDatatypeTypeDecl.jsonEmit_IRDatatypeTypeDecl(tsig)];
        }
        else {
            assert(false, "Unknown IRAbstractNominalTypeDecl subclass");
        }
    }

    static jsonParse_IRAbstractNominalTypeDecl(obj: any): IRAbstractNominalTypeDecl {
        const kind = (obj as any[])[0] as string;
        const data = (obj as any[])[1];

        if(kind === "Assembly::EnumTypeDecl") {
            return IREnumTypeDecl.jsonParse_IREnumTypeDecl(data);
        }
        else if(kind === "Assembly::TypedeclSimpleTypeDecl") {
            return IRTypedeclSimpleTypeDecl.jsonParse_IRTypedeclSimpleTypeDecl(data);
        }
        else if(kind === "Assembly::TypedeclBoundedTypeDecl") {
            return IRTypedeclBoundedTypeDecl.jsonParse_IRTypedeclBoundedTypeDecl(data);
        }
        else if(kind === "Assembly::TypedeclCStringTypeDecl") {
            return IRTypedeclCStringTypeDecl.jsonParse_IRTypedeclCStringTypeDecl(data);
        }
        else if(kind === "Assembly::TypedeclStringTypeDecl") {
            return IRTypedeclStringTypeDecl.jsonParse_IRTypedeclStringTypeDecl(data);
        }
        else if(kind === "Assembly::PrimitiveEntityTypeDecl") {
            return IRPrimitiveEntityTypeDecl.jsonParse_IRPrimitiveEntityTypeDecl(data);
        }
        else if(kind === "Assembly::OkTypeDecl") {
            return IROkTypeDecl.jsonParse_IROkTypeDecl(data);
        }
        else if(kind === "Assembly::FailTypeDecl") {
            return IRFailTypeDecl.jsonParse_IRFailTypeDecl(data);
        }
        else if(kind === "Assembly::APIErrorTypeDecl") {
            return IRAPIErrorTypeDecl.jsonParse_IRAPIErrorTypeDecl(data);
        }
        else if(kind === "Assembly::APIRejectedTypeDecl") {
            return IRAPIRejectedTypeDecl.jsonParse_IRAPIRejectedTypeDecl(data);
        }
        else if(kind === "Assembly::APIDeniedTypeDecl") {
            return IRAPIDeniedTypeDecl.jsonParse_IRAPIDeniedTypeDecl(data);
        }
        else if(kind === "Assembly::APIDroppedTypeDecl") {
            return IRAPIDroppedTypeDecl.jsonParse_IRAPIDroppedTypeDecl(data);
        }
        else if(kind === "Assembly::APISuccessTypeDecl") {
            return IRAPISuccessTypeDecl.jsonParse_IRAPISuccessTypeDecl(data);
        }
        else if(kind === "Assembly::MapEntryTypeDecl") {
            return IRMapEntryTypeDecl.jsonParse_IRMapEntryTypeDecl(data);
        }
        else if(kind === "Assembly::ListTypeDecl") {
            return IRListTypeDecl.jsonParse_IRListTypeDecl(data);
        }
        else if(kind === "Assembly::StackTypeDecl") {
            return IRStackTypeDecl.jsonParse_IRStackTypeDecl(data);
        }
        else if(kind === "Assembly::QueueTypeDecl") {
            return IRQueueTypeDecl.jsonParse_IRQueueTypeDecl(data);
        }
        else if(kind === "Assembly::SetTypeDecl") {
            return IRSetTypeDecl.jsonParse_IRSetTypeDecl(data);
        }
        else if(kind === "Assembly::MapTypeDecl") {
            return IRMapTypeDecl.jsonParse_IRMapTypeDecl(data);
        }
        else if(kind === "Assembly::EventListTypeDecl") {
            return IREventListTypeDecl.jsonParse_IREventListTypeDecl(data);
        }
        else if(kind === "Assembly::EntityTypeDecl") {
            return IREntityTypeDecl.jsonParse_IREntityTypeDecl(data);
        }
        else if(kind === "Assembly::OptionTypeDecl") {
            return IROptionTypeDecl.jsonParse_IROptionTypeDecl(data);
        }
        else if(kind === "Assembly::ResultTypeDecl") {
            return IRResultTypeDecl.jsonParse_IRResultTypeDecl(data);
        }
        else if(kind === "Assembly::APIResultTypeDecl") {
            return IRAPIResultTypeDecl.jsonParse_IRAPIResultTypeDecl(data);
        }
        else if(kind === "Assembly::ConceptTypeDecl") {
            return IRConceptTypeDecl.jsonParse_IRConceptTypeDecl(data);
        }
        else if(kind === "Assembly::DatatypeMemberEntityTypeDecl") {
            return IRDatatypeMemberEntityTypeDecl.jsonParse_IRDatatypeMemberEntityTypeDecl(data);
        }
        else if(kind === "Assembly::DatatypeTypeDecl") {
            return IRDatatypeTypeDecl.jsonParse_IRDatatypeTypeDecl(data);
        }
        else {
            assert(false, "Unknown IRAbstractNominalTypeDecl kind");
        }
    }
}

abstract class IRAbstractEntityTypeDecl extends IRAbstractNominalTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, invariants, validates, fields, etag, saturatedProvides, saturatedBFieldInfo, allInvariants, allValidates, docstr, metatags, file, sinfo);
    }

    static jsonEmit_IRAbstractEntityTypeDecl(tsig: IRAbstractEntityTypeDecl): object {
        return IRAbstractNominalTypeDecl.jsonEmit_IRAbstractNominalTypeDecl(tsig);
    }

    static jsonParse_IRAbstractEntityTypeDecl(obj: any): IRAbstractEntityTypeDecl {
        return IRAbstractNominalTypeDecl.jsonParse_IRAbstractNominalTypeDecl(obj) as IRAbstractEntityTypeDecl;
    }
}

class IREnumTypeDecl extends IRAbstractEntityTypeDecl {
    readonly members: string[];

    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, members: string[]) {
        super(tkey, [], [], [], "std", [], [], [], [], docstr, [], file, sinfo);
        this.members = members;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [];
    }

    static jsonEmit_IREnumTypeDecl(tsig: IREnumTypeDecl): object {
        return {
            ...IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig),
            members: tsig.members
        };
    }

    static jsonParse_IREnumTypeDecl(obj: any): IREnumTypeDecl {
        const ntdv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);
        const members = obj.members;

        return new IREnumTypeDecl(ntdv[0], ntdv[9], ntdv[11], ntdv[12], members);
    }
}

class IRTypedeclRngCheck {
    readonly min: IRImmediateExpression | undefined;
    readonly max: IRImmediateExpression | undefined;

    constructor(min: IRImmediateExpression | undefined, max: IRImmediateExpression | undefined) {
        this.min = min;
        this.max = max;
    }

    static jsonEmit_IRTypedeclRngCheck(rngchk: IRTypedeclRngCheck): object {
        return {
            min: rngchk.min === undefined ? null : ["some", IRImmediateExpression.jsonEmit_IRImmediateExpression(rngchk.min)],
            max: rngchk.max === undefined ? null : ["some", IRImmediateExpression.jsonEmit_IRImmediateExpression(rngchk.max)]
        };
    }

    static jsonParse_IRTypedeclRngCheck(obj: any): IRTypedeclRngCheck {
        return new IRTypedeclRngCheck(
            obj.min !== null ? IRImmediateExpression.jsonParse_IRImmediateExpression(obj.min[1]) : undefined,
            obj.max !== null ? IRImmediateExpression.jsonParse_IRImmediateExpression(obj.max[1]) : undefined
        );
    }
}

abstract class IRTypedeclAbstractTypeDecl extends IRAbstractEntityTypeDecl {
    readonly valuetype: IRTypeSignature;
    readonly iskeytype: boolean;
    readonly isnumerictype: boolean;

    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], saturatedProvides: IRTypeSignature[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, valuetype: IRTypeSignature, iskeytype: boolean, isnumerictype: boolean) {
        super(tkey, invariants, validates, [], "std", saturatedProvides, [], allInvariants, allValidates, docstr, metatags, file, sinfo);
        this.valuetype = valuetype;
        this.iskeytype = iskeytype;
        this.isnumerictype = isnumerictype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [];
    }

    static jsonEmit_IRTypedeclAbstractTypeDecl(tsig: IRTypedeclAbstractTypeDecl): object {
        return IRAbstractNominalTypeDecl.jsonEmit_IRAbstractNominalTypeDecl(tsig);
    }

    static jsonParse_IRTypedeclAbstractTypeDecl(obj: any): IRTypedeclAbstractTypeDecl {
        return IRAbstractNominalTypeDecl.jsonParse_IRAbstractNominalTypeDecl(obj) as IRTypedeclAbstractTypeDecl;
    }

    static jsonEmitMeta_IRTypedeclAbstractTypeDecl(tsig: IRTypedeclAbstractTypeDecl): object {
        return {
            valuetype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.valuetype),
            iskeytype: tsig.iskeytype,
            isnumerictype: tsig.isnumerictype
        }
    }

    static jsonParseMeta_IRTypedeclAbstractTypeDecl(obj: any): [IRTypeSignature, boolean, boolean] {
        return [
            IRTypeSignature.jsonParse_IRTypeSignature(obj.valuetype),
            obj.iskeytype,
            obj.isnumerictype
        ];
    }
}

class IRTypedeclSimpleTypeDecl extends IRTypedeclAbstractTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], saturatedProvides: IRTypeSignature[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, valuetype: IRTypeSignature, iskeytype: boolean, isnumerictype: boolean) {
        super(tkey, invariants, validates, saturatedProvides, allInvariants, allValidates, docstr, metatags, file, sinfo, valuetype, iskeytype, isnumerictype);
    }

    static jsonEmit_IRTypedeclSimpleTypeDecl(tsig: IRTypedeclSimpleTypeDecl): object {
        const ntdv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        const stt = IRTypedeclAbstractTypeDecl.jsonEmitMeta_IRTypedeclAbstractTypeDecl(tsig);

        return { ...ntdv, ...stt };
    }

    static jsonParse_IRTypedeclSimpleTypeDecl(obj: any): IRTypedeclSimpleTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);
        const stv = IRTypedeclAbstractTypeDecl.jsonParseMeta_IRTypedeclAbstractTypeDecl(obj);
        
        return new IRTypedeclSimpleTypeDecl(
            ntv[0], ntv[1], ntv[2], ntv[5], ntv[7], ntv[8], ntv[9], ntv[10], ntv[11], ntv[12], 
            ...stv
        );
    }
}

class IRTypedeclBoundedTypeDecl extends IRTypedeclAbstractTypeDecl {
    readonly rngchk: IRTypedeclRngCheck;
    
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], saturatedProvides: IRTypeSignature[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, valuetype: IRTypeSignature, iskeytype: boolean, isnumerictype: boolean, rngchk: IRTypedeclRngCheck) {
        super(tkey, invariants, validates, saturatedProvides, allInvariants, allValidates, docstr, metatags, file, sinfo, valuetype, iskeytype, isnumerictype);
        this.rngchk = rngchk;
    }

    static jsonEmit_IRTypedeclBoundedTypeDecl(tsig: IRTypedeclBoundedTypeDecl): object {
        const ntdv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        const stt = IRTypedeclAbstractTypeDecl.jsonEmitMeta_IRTypedeclAbstractTypeDecl(tsig);
        const rngchk = IRTypedeclRngCheck.jsonEmit_IRTypedeclRngCheck(tsig.rngchk);
        
        return { ...ntdv, ...stt, rngchk };
    }

    static jsonParse_IRTypedeclBoundedTypeDecl(obj: any): IRTypedeclBoundedTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);
        const stv = IRTypedeclAbstractTypeDecl.jsonParseMeta_IRTypedeclAbstractTypeDecl(obj);
        const rngchk = IRTypedeclRngCheck.jsonParse_IRTypedeclRngCheck(obj); 

        return new IRTypedeclBoundedTypeDecl(
            ntv[0], ntv[1], ntv[2], ntv[5], ntv[7], ntv[8], ntv[9], ntv[10], ntv[11], ntv[12], 
            ...stv,
            rngchk
        );
    }
}

class IRTypedeclCStringTypeDecl extends IRTypedeclAbstractTypeDecl {
    readonly rngchk: IRTypedeclRngCheck | undefined;
    readonly rechk: IRLiteralCRegexExpression | undefined;
    
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], saturatedProvides: IRTypeSignature[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, rngchk: IRTypedeclRngCheck | undefined, rechk: IRLiteralCRegexExpression | undefined) {
        super(tkey, invariants, validates, saturatedProvides, allInvariants, allValidates, docstr, metatags, file, sinfo, new IRNominalTypeSignature("CString"), true, false);
        this.rngchk = rngchk;
        this.rechk = rechk;
    }

    static jsonEmit_IRTypedeclCStringTypeDecl(tsig: IRTypedeclCStringTypeDecl): object {
        const ntdv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        const stt = IRTypedeclAbstractTypeDecl.jsonEmitMeta_IRTypedeclAbstractTypeDecl(tsig);
        const rngchk = tsig.rngchk === undefined ? null : ["some", IRTypedeclRngCheck.jsonEmit_IRTypedeclRngCheck(tsig.rngchk)];
        const rechk = tsig.rechk === undefined ? null : ["some", IRLiteralCRegexExpression.jsonEmit_IRLiteralCRegexExpression(tsig.rechk)];

        return { ...ntdv, ...stt, rngchk, rechk };
    }

    static jsonParse_IRTypedeclCStringTypeDecl(obj: any): IRTypedeclCStringTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);
        const rngchk = obj.rngchk === null ? undefined : IRTypedeclRngCheck.jsonParse_IRTypedeclRngCheck(obj.rngchk[1]);
        const rechk = obj.rechk === null ? undefined : IRLiteralCRegexExpression.jsonParse_IRLiteralCRegexExpression(obj.rechk[1]);

        return new IRTypedeclCStringTypeDecl(
            ntv[0], ntv[1], ntv[2], ntv[5], ntv[7], ntv[8], ntv[9], ntv[10], ntv[11], ntv[12], 
            rngchk,
            rechk
        );
    }
}

class IRTypedeclStringTypeDecl extends IRTypedeclAbstractTypeDecl {
    readonly rngchk: IRTypedeclRngCheck | undefined;
    readonly rechk: IRLiteralUnicodeRegexExpression | undefined;
    
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], saturatedProvides: IRTypeSignature[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, rngchk: IRTypedeclRngCheck | undefined, rechk: IRLiteralUnicodeRegexExpression | undefined) {
        super(tkey, invariants, validates, saturatedProvides, allInvariants, allValidates, docstr, metatags, file, sinfo, new IRNominalTypeSignature("String"), true, false);
        this.rngchk = rngchk;
        this.rechk = rechk;
    }

    static jsonEmit_IRTypedeclStringTypeDecl(tsig: IRTypedeclStringTypeDecl): object {
        const ntdv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        const stt = IRTypedeclAbstractTypeDecl.jsonEmitMeta_IRTypedeclAbstractTypeDecl(tsig);
        const rngchk = tsig.rngchk === undefined ? null : ["some", IRTypedeclRngCheck.jsonEmit_IRTypedeclRngCheck(tsig.rngchk)];
        const rechk = tsig.rechk === undefined ? null : ["some", IRLiteralUnicodeRegexExpression.jsonEmit_IRLiteralUnicodeRegexExpression(tsig.rechk)];

        return { ...ntdv, ...stt, rngchk, rechk };
    }

    static jsonParse_IRTypedeclStringTypeDecl(obj: any): IRTypedeclStringTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);
        const rngchk = obj.rngchk === null ? undefined : IRTypedeclRngCheck.jsonParse_IRTypedeclRngCheck(obj.rngchk[1]);
        const rechk = obj.rechk === null ? undefined : IRLiteralUnicodeRegexExpression.jsonParse_IRLiteralUnicodeRegexExpression(obj.rechk[1]);

        return new IRTypedeclStringTypeDecl(
            ntv[0], ntv[1], ntv[2], ntv[5], ntv[7], ntv[8], ntv[9], ntv[10], ntv[11], ntv[12], 
            rngchk,
            rechk
        );
    }
}

//TODO: Path typedecl

abstract class IRInternalEntityTypeDecl extends IRAbstractEntityTypeDecl {
    constructor(tkey: string, saturatedProvides: IRTypeSignature[], metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, [], [], [], "std", saturatedProvides, [], [], [], undefined, metatags, file, sinfo);
    }

    static jsonEmit_IRInternalEntityTypeDecl(tsig: IRInternalEntityTypeDecl): object {
        return IRAbstractNominalTypeDecl.jsonEmit_IRAbstractNominalTypeDecl(tsig);
    }

    static jsonParse_IRInternalEntityTypeDecl(obj: any): IRInternalEntityTypeDecl {
        return IRAbstractNominalTypeDecl.jsonParse_IRAbstractNominalTypeDecl(obj) as IRInternalEntityTypeDecl;
    }
}

class IRPrimitiveEntityTypeDecl extends IRInternalEntityTypeDecl {
    constructor(tkey: string, file: string, sinfo: IRSourceInfo) {
        super(tkey, [], [], file, sinfo);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [];
    }

    static jsonEmit_IRPrimitiveEntityTypeDecl(tsig: IRPrimitiveEntityTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        return ntv;
    }

    static jsonParse_IRPrimitiveEntityTypeDecl(obj: any): IRPrimitiveEntityTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);

        return new IRPrimitiveEntityTypeDecl(ntv[0], ntv[11], ntv[12]);
    }
}

abstract class IRConstructableTypeDecl extends IRInternalEntityTypeDecl {
    constructor(tkey: string, saturatedProvides: IRTypeSignature[], file: string, sinfo: IRSourceInfo) {
        super(tkey, saturatedProvides, [], file, sinfo);
    }

    static jsonEmit_IRConstructableTypeDecl(tsig: IRConstructableTypeDecl): object {
        return IRAbstractNominalTypeDecl.jsonEmit_IRAbstractNominalTypeDecl(tsig);
    }

    static jsonParse_IRConstructableTypeDecl(obj: any): IRConstructableTypeDecl {
        return IRAbstractNominalTypeDecl.jsonParse_IRAbstractNominalTypeDecl(obj) as IRConstructableTypeDecl;
    }
}

class IROkTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature) {
        super(tkey, saturatedProvides, file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype, this.etype];
    }

    static jsonEmit_IROkTypeDecl(tsig: IROkTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);

        return {
            ...ntv,
            ttype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.ttype),
            etype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.etype)
        }
    }

    static jsonParse_IROkTypeDecl(obj: any): IROkTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);

        return new IROkTypeDecl(ntv[0], ntv[5], ntv[11], ntv[12], IRTypeSignature.jsonParse_IRTypeSignature(obj.ttype), IRTypeSignature.jsonParse_IRTypeSignature(obj.etype));
    }
}

class IRFailTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature) {
        super(tkey, saturatedProvides, file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype, this.etype];
    }

    static jsonEmit_IRFailTypeDecl(tsig: IRFailTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);

        return {
            ...ntv,
            ttype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.ttype),
            etype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.etype)
        }
    }

    static jsonParse_IRFailTypeDecl(obj: any): IRFailTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);

        return new IRFailTypeDecl(ntv[0], ntv[5], ntv[11], ntv[12], IRTypeSignature.jsonParse_IRTypeSignature(obj.ttype), IRTypeSignature.jsonParse_IRTypeSignature(obj.etype));
    }
}

abstract class IRAPIResultEntityTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature) {
        super(tkey, saturatedProvides, file, sinfo);
        this.ttype = ttype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype];
    }

    static jsonEmit_IRAPIResultEntityTypeDecl(tsig: IRAPIResultEntityTypeDecl): object {
        return IRAbstractNominalTypeDecl.jsonEmit_IRAbstractNominalTypeDecl(tsig);
    }

    static jsonParse_IRAPIResultEntityTypeDecl(obj: any): IRAPIResultEntityTypeDecl {
        return IRAbstractNominalTypeDecl.jsonParse_IRAbstractNominalTypeDecl(obj) as IRAPIResultEntityTypeDecl;
    }

    static jsonEmitMeta_IRAPIResultEntityTypeDecl(tsig: IRAPIResultEntityTypeDecl): object {
        return {
            ttype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.ttype)
        }
    }

    static jsonParseMeta_IRAPIResultEntityTypeDecl(obj: any): [IRTypeSignature] {
        return [
            IRTypeSignature.jsonParse_IRTypeSignature(obj.ttype)
        ];
    }
}

class IRAPIErrorTypeDecl extends IRAPIResultEntityTypeDecl {
    constructor(tkey: string, saturatedProvides: IRTypeSignature[], file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature) {
        super(tkey, saturatedProvides, file, sinfo, ttype);
    }

    static jsonEmit_IRAPIErrorTypeDecl(tsig: IRAPIErrorTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        const iirv = IRAPIResultEntityTypeDecl.jsonEmitMeta_IRAPIResultEntityTypeDecl(tsig);
        
        return {
            ...ntv,
            ...iirv
        }
    }

    static jsonParse_IRAPIErrorTypeDecl(obj: any): IRAPIErrorTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);
        const iirv = IRAPIResultEntityTypeDecl.jsonParseMeta_IRAPIResultEntityTypeDecl(obj);

        return new IRAPIErrorTypeDecl(ntv[0], ntv[5], ntv[11], ntv[12], ...iirv);
    }
}

class IRAPIRejectedTypeDecl extends IRAPIResultEntityTypeDecl {
    constructor(tkey: string, saturatedProvides: IRTypeSignature[], file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature) {
        super(tkey, saturatedProvides, file, sinfo, ttype);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype];
    }

    static jsonEmit_IRAPIRejectedTypeDecl(tsig: IRAPIRejectedTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        const iirv = IRAPIResultEntityTypeDecl.jsonEmitMeta_IRAPIResultEntityTypeDecl(tsig);
        
        return {
            ...ntv,
            ...iirv
        }
    
    }

    static jsonParse_IRAPIRejectedTypeDecl(obj: any): IRAPIRejectedTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);
        const iirv = IRAPIResultEntityTypeDecl.jsonParseMeta_IRAPIResultEntityTypeDecl(obj);

        return new IRAPIRejectedTypeDecl(ntv[0], ntv[5], ntv[11], ntv[12], ...iirv);
    }
}

class IRAPIDeniedTypeDecl extends IRAPIResultEntityTypeDecl {
    constructor(tkey: string, saturatedProvides: IRTypeSignature[], file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature) {
        super(tkey, saturatedProvides, file, sinfo, ttype);
    }

    static jsonEmit_IRAPIDeniedTypeDecl(tsig: IRAPIDeniedTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        const iirv = IRAPIResultEntityTypeDecl.jsonEmitMeta_IRAPIResultEntityTypeDecl(tsig);
        
        return {
            ...ntv,
            ...iirv
        }
    }

    static jsonParse_IRAPIDeniedTypeDecl(obj: any): IRAPIDeniedTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);
        const iirv = IRAPIResultEntityTypeDecl.jsonParseMeta_IRAPIResultEntityTypeDecl(obj);

        return new IRAPIDeniedTypeDecl(ntv[0], ntv[5], ntv[11], ntv[12], ...iirv);
    }
}

class IRAPIDroppedTypeDecl extends IRAPIResultEntityTypeDecl {
    constructor(tkey: string, saturatedProvides: IRTypeSignature[], file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature) {
        super(tkey, saturatedProvides, file, sinfo, ttype);
    }

    static jsonEmit_IRAPIDroppedTypeDecl(tsig: IRAPIDroppedTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        const iirv = IRAPIResultEntityTypeDecl.jsonEmitMeta_IRAPIResultEntityTypeDecl(tsig);
        
        return {
            ...ntv,
            ...iirv
        }
    }

    static jsonParse_IRAPIDroppedTypeDecl(obj: any): IRAPIDroppedTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);
        const iirv = IRAPIResultEntityTypeDecl.jsonParseMeta_IRAPIResultEntityTypeDecl(obj);

        return new IRAPIDroppedTypeDecl(ntv[0], ntv[5], ntv[11], ntv[12], ...iirv);
    }
}

class IRAPISuccessTypeDecl extends IRAPIResultEntityTypeDecl {
    constructor(tkey: string, saturatedProvides: IRTypeSignature[], file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature) {
        super(tkey, saturatedProvides, file, sinfo, ttype);
    }

    static jsonEmit_IRAPISuccessTypeDecl(tsig: IRAPISuccessTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        const iirv = IRAPIResultEntityTypeDecl.jsonEmitMeta_IRAPIResultEntityTypeDecl(tsig);
        
        return {
            ...ntv,
            ...iirv
        }
    }

    static jsonParse_IRAPISuccessTypeDecl(obj: any): IRAPISuccessTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);
        const iirv = IRAPIResultEntityTypeDecl.jsonParseMeta_IRAPIResultEntityTypeDecl(obj);

        return new IRAPISuccessTypeDecl(ntv[0], ntv[5], ntv[11], ntv[12], ...iirv);
    }
}

class IRSomeTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature) {
        super(tkey, saturatedProvides, file, sinfo);
        this.ttype = ttype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype];
    }

    static jsonEmit_IRSomeTypeDecl(tsig: IRSomeTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        
        return {
            ...ntv,
            ttype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.ttype)
        }
    }

    static jsonParse_IRSomeTypeDecl(obj: any): IRSomeTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);

        return new IRSomeTypeDecl(ntv[0], ntv[5], ntv[11], ntv[12], IRTypeSignature.jsonParse_IRTypeSignature(obj["ttype"]));
    }
}

class IRMapEntryTypeDecl extends IRConstructableTypeDecl {
    readonly ktype: IRTypeSignature;
    readonly vtype: IRTypeSignature;

    constructor(tkey: string, file: string, sinfo: IRSourceInfo, ktype: IRTypeSignature, vtype: IRTypeSignature) {
        super(tkey, [], file, sinfo);
        this.ktype = ktype;
        this.vtype = vtype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ktype, this.vtype];
    }

    static jsonEmit_IRMapEntryTypeDecl(tsig: IRMapEntryTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        
        return {
            ...ntv,
            ktype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.ktype),
            vtype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.vtype)
        }
    }

    static jsonParse_IRMapEntryTypeDecl(obj: any): IRMapEntryTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);

        return new IRMapEntryTypeDecl(ntv[0], ntv[11], ntv[12], IRTypeSignature.jsonParse_IRTypeSignature(obj["ktype"]), IRTypeSignature.jsonParse_IRTypeSignature(obj["vtype"]));
    }
}

abstract class IRAbstractCollectionTypeDecl extends IRInternalEntityTypeDecl {
    readonly oftype: IRTypeSignature;

    constructor(tkey: string, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature) {
        super(tkey, [], [], file, sinfo);
        this.oftype = oftype;
    }

    static jsonEmit_IRAbstractCollectionTypeDecl(tsig: IRAbstractCollectionTypeDecl): object {
        return IRAbstractNominalTypeDecl.jsonEmit_IRAbstractNominalTypeDecl(tsig);
    }

    static jsonParse_IRAbstractCollectionTypeDecl(obj: any): IRAbstractCollectionTypeDecl {
        return IRAbstractNominalTypeDecl.jsonParse_IRAbstractNominalTypeDecl(obj) as IRAbstractCollectionTypeDecl;
    }

    static jsonEmitMeta_IRAbstractCollectionTypeDecl(tsig: IRAbstractCollectionTypeDecl): object {
        return {
            oftype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.oftype)
        }
    }

    static jsonParseMeta_IRAbstractCollectionTypeDecl(obj: any): [IRTypeSignature] {
        return [IRTypeSignature.jsonParse_IRTypeSignature(obj["oftype"])];
    }
}

class IRListTypeDecl extends IRAbstractCollectionTypeDecl {
    constructor(tkey: string, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature) {
        super(tkey, file, sinfo, oftype);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.oftype];
    }

    static jsonEmit_IRListTypeDecl(tsig: IRListTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        const ctv = IRAbstractCollectionTypeDecl.jsonEmitMeta_IRAbstractCollectionTypeDecl(tsig);
        
        return {
            ...ntv,
            ...ctv
        };
    }

    static jsonParse_IRListTypeDecl(obj: any): IRListTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);
        const ctv = IRAbstractCollectionTypeDecl.jsonParseMeta_IRAbstractCollectionTypeDecl(obj);

        return new IRListTypeDecl(ntv[0], ntv[11], ntv[12], ...ctv);
    }
}

class IRStackTypeDecl extends IRAbstractCollectionTypeDecl {
    constructor(tkey: string, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature) {
        super(tkey, file, sinfo, oftype);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.oftype];
    }

    static jsonEmit_IRStackTypeDecl(tsig: IRStackTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        const ctv = IRAbstractCollectionTypeDecl.jsonEmitMeta_IRAbstractCollectionTypeDecl(tsig);
        
        return {
            ...ntv,
            ...ctv
        };
    }

    static jsonParse_IRStackTypeDecl(obj: any): IRStackTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);
        const ctv = IRAbstractCollectionTypeDecl.jsonParseMeta_IRAbstractCollectionTypeDecl(obj);

        return new IRStackTypeDecl(ntv[0], ntv[11], ntv[12], ...ctv);
    }
}

class IRQueueTypeDecl extends IRAbstractCollectionTypeDecl {
    constructor(tkey: string, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature) {
        super(tkey, file, sinfo, oftype);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.oftype];
    }
    
    static jsonEmit_IRQueueTypeDecl(tsig: IRQueueTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        const ctv = IRAbstractCollectionTypeDecl.jsonEmitMeta_IRAbstractCollectionTypeDecl(tsig);
        
        return {
            ...ntv,
            ...ctv
        };
    }

    static jsonParse_IRQueueTypeDecl(obj: any): IRQueueTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);
        const ctv = IRAbstractCollectionTypeDecl.jsonParseMeta_IRAbstractCollectionTypeDecl(obj);

        return new IRQueueTypeDecl(ntv[0], ntv[11], ntv[12], ...ctv);
    }
}

class IRSetTypeDecl extends IRAbstractCollectionTypeDecl {
    constructor(tkey: string, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature) {
        super(tkey, file, sinfo, oftype);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.oftype];
    }

    static jsonEmit_IRSetTypeDecl(tsig: IRSetTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        const ctv = IRAbstractCollectionTypeDecl.jsonEmitMeta_IRAbstractCollectionTypeDecl(tsig);

        return {
            ...ntv,
            ...ctv
        };
    }

    static jsonParse_IRSetTypeDecl(obj: any): IRSetTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);
        const ctv = IRAbstractCollectionTypeDecl.jsonParseMeta_IRAbstractCollectionTypeDecl(obj);

        return new IRSetTypeDecl(ntv[0], ntv[11], ntv[12], ...ctv);
    }
}

class IRMapTypeDecl extends IRAbstractCollectionTypeDecl {
    readonly ktype: IRTypeSignature;
    readonly vtype: IRTypeSignature;

    constructor(tkey: string, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature, ktype: IRTypeSignature, vtype: IRTypeSignature) {
        super(tkey, file, sinfo, oftype);
        this.ktype = ktype;
        this.vtype = vtype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
       return [this.oftype, this.ktype, this.vtype];
    }

    static jsonEmit_IRMapTypeDecl(tsig: IRMapTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        const ctv = IRAbstractCollectionTypeDecl.jsonEmitMeta_IRAbstractCollectionTypeDecl(tsig);

        return {
            ...ntv,
            ...ctv,
            ktype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.ktype),
            vtype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.vtype)
        };
    }

    static jsonParse_IRMapTypeDecl(obj: any): IRMapTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);
        const ctv = IRAbstractCollectionTypeDecl.jsonParseMeta_IRAbstractCollectionTypeDecl(obj);

        return new IRMapTypeDecl(ntv[0], ntv[11], ntv[12], ...ctv, IRTypeSignature.jsonParse_IRTypeSignature(obj.ktype), IRTypeSignature.jsonParse_IRTypeSignature(obj.vtype));
    }
}

class IREventListTypeDecl extends IRInternalEntityTypeDecl {
    readonly etype: IRTypeSignature;

    constructor(tkey: string, file: string, sinfo: IRSourceInfo, etype: IRTypeSignature) {
        super(tkey, [], [], file, sinfo);
        this.etype = etype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.etype];
    }

    static jsonEmit_IREventListTypeDecl(tsig: IREventListTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);

        return {
            ...ntv,
            etype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.etype)
        };
    }

    static jsonParse_IREventListTypeDecl(obj: any): IREventListTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);

        return new IREventListTypeDecl(ntv[0], ntv[11], ntv[12], IRTypeSignature.jsonParse_IRTypeSignature(obj.etype));
    }
}

class IREntityTypeDecl extends IRAbstractEntityTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, invariants, validates, fields, etag, saturatedProvides, saturatedBFieldInfo, allInvariants, allValidates, docstr, metatags, file, sinfo);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        const ffdecls = this.saturatedBFieldInfo.map((bf) => {
            const ctt = alltypes.get(bf.containingtype.tkeystr) as IRAbstractNominalTypeDecl;
            const bfdecl = ctt.fields.find(f => f.fkey === bf.fkey) as IRMemberFieldDecl;
            return bfdecl.declaredType;
        });

        return ffdecls;
    }

    static jsonEmit_IREntityTypeDecl(tsig: IREntityTypeDecl): any {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        
        return ntv;
    }

    static jsonParse_IREntityTypeDecl(obj: any): IREntityTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);

        return new IREntityTypeDecl(...ntv);
    }
}

abstract class IRAbstractConceptTypeDecl extends IRAbstractNominalTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, invariants, validates, fields, "std", saturatedProvides, saturatedBFieldInfo, [], [], docstr, metatags, file, sinfo);
    }

    static jsonEmit_IRAbstractConceptTypeDecl(tsig: IRAbstractConceptTypeDecl): object {
        return IRAbstractNominalTypeDecl.jsonEmit_IRAbstractNominalTypeDecl(tsig);
    }

    static jsonParse_IRAbstractConceptTypeDecl(obj: any): IRAbstractConceptTypeDecl {
        return IRAbstractNominalTypeDecl.jsonParse_IRAbstractNominalTypeDecl(obj) as IRAbstractConceptTypeDecl;
    }
}

abstract class IRInternalConceptTypeDecl extends IRAbstractConceptTypeDecl {
    constructor(tkey: string, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, [], [], [], [], [], undefined, metatags, file, sinfo);
    }

    static jsonEmit_IRInternalConceptTypeDecl(tsig: IRInternalConceptTypeDecl): object {
        return IRAbstractNominalTypeDecl.jsonEmit_IRAbstractNominalTypeDecl(tsig);
    }

    static jsonParse_IRInternalConceptTypeDecl(obj: any): IRInternalConceptTypeDecl {
        return IRAbstractNominalTypeDecl.jsonParse_IRAbstractNominalTypeDecl(obj) as IRInternalConceptTypeDecl;
    }
}

class IROptionTypeDecl extends IRInternalConceptTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly sometype: IRTypeSignature;

    constructor(tkey: string, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, sometype: IRTypeSignature) {
        super(tkey, [], file, sinfo);
        this.ttype = ttype;
        this.sometype = sometype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype, this.sometype];
    }

    static jsonEmit_IROptionTypeDecl(tsig: IROptionTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        return {
            ...ntv,
            ttype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.ttype),
            sometype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.sometype)
        };
    }

    static jsonParse_IROptionTypeDecl(obj: any): IROptionTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);

        return new IROptionTypeDecl(ntv[0], ntv[11], ntv[12], IRTypeSignature.jsonParse_IRTypeSignature(obj.ttype), IRTypeSignature.jsonParse_IRTypeSignature(obj.sometype));
    }
}

class IRResultTypeDecl extends IRInternalConceptTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    readonly oktype: IRTypeSignature;
    readonly failtype: IRTypeSignature;

    constructor(tkey: string, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature, oktype: IRTypeSignature, failtype: IRTypeSignature) {
        super(tkey, [], file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
        this.oktype = oktype;
        this.failtype = failtype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype, this.etype, this.oktype, this.failtype];
    }

    static jsonEmit_IRResultTypeDecl(tsig: IRResultTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);

        return {
            ...ntv,
            ttype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.ttype),
            etype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.etype),
            oktype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.oktype),
            failtype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.failtype)
        };
    }

    static jsonParse_IRResultTypeDecl(obj: any): IRResultTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);

        return new IRResultTypeDecl(ntv[0], ntv[11], ntv[12], IRTypeSignature.jsonParse_IRTypeSignature(obj.ttype), IRTypeSignature.jsonParse_IRTypeSignature(obj.etype), IRTypeSignature.jsonParse_IRTypeSignature(obj.oktype), IRTypeSignature.jsonParse_IRTypeSignature(obj.failtype));
    }
}

class IRAPIResultTypeDecl extends IRInternalConceptTypeDecl {
    readonly ttype: IRTypeSignature;

    readonly errortype: IRTypeSignature;
    readonly rejectedtype: IRTypeSignature;
    readonly deniedtype: IRTypeSignature;
    readonly droppedtype: IRTypeSignature;
    readonly successtype: IRTypeSignature;

    constructor(tkey: string, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, errortype: IRTypeSignature, rejectedtype: IRTypeSignature, deniedtype: IRTypeSignature, droppedtype: IRTypeSignature, successtype: IRTypeSignature) {
        super(tkey, [], file, sinfo);
        this.ttype = ttype;
        this.errortype = errortype;
        this.rejectedtype = rejectedtype;
        this.deniedtype = deniedtype;
        this.droppedtype = droppedtype;
        this.successtype = successtype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype, this.errortype, this.rejectedtype, this.deniedtype, this.droppedtype, this.successtype];
    }

    static jsonEmit_IRAPIResultTypeDecl(tsig: IRAPIResultTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);

        return {
            ...ntv,
            ttype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.ttype),
            errortype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.errortype),
            rejectedtype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.rejectedtype),
            deniedtype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.deniedtype),
            droppedtype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.droppedtype),
            successtype: IRTypeSignature.jsonEmit_IRTypeSignature(tsig.successtype)
        };
    }

    static jsonParse_IRAPIResultTypeDecl(obj: any): IRAPIResultTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);

        return new IRAPIResultTypeDecl(ntv[0], ntv[11], ntv[12], IRTypeSignature.jsonParse_IRTypeSignature(obj.ttype), IRTypeSignature.jsonParse_IRTypeSignature(obj.errortype), IRTypeSignature.jsonParse_IRTypeSignature(obj.rejectedtype), IRTypeSignature.jsonParse_IRTypeSignature(obj.deniedtype), IRTypeSignature.jsonParse_IRTypeSignature(obj.droppedtype), IRTypeSignature.jsonParse_IRTypeSignature(obj.successtype));
    }
}

class IRConceptTypeDecl extends IRAbstractConceptTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, invariants, validates, fields, saturatedProvides, saturatedBFieldInfo, docstr, metatags, file, sinfo);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        const ffdecls = this.saturatedBFieldInfo.map(bf => {
            const ctt = alltypes.get(bf.containingtype.tkeystr) as IRAbstractNominalTypeDecl;
            const bfdecl = ctt.fields.find(f => f.fkey === bf.fkey) as IRMemberFieldDecl;
            return bfdecl.declaredType;
        });

        return [new IRNominalTypeSignature(this.tkey), ...ffdecls];
    }

    static jsonEmit_IRConceptTypeDecl(tsig: IRConceptTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        
        return ntv;
    }

    static jsonParse_IRConceptTypeDecl(obj: any): IRConceptTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);

        return new IRConceptTypeDecl(ntv[0], ntv[1], ntv[2], ntv[3], ntv[5], ntv[6], ntv[9], ntv[10], ntv[11], ntv[12]);
    }
}

class IRDatatypeMemberEntityTypeDecl extends IRAbstractEntityTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, invariants, validates, fields, etag, saturatedProvides, saturatedBFieldInfo, allInvariants, allValidates, docstr, metatags, file, sinfo);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        const ffdecls = this.saturatedBFieldInfo.map(bf => {
            const ctt = alltypes.get(bf.containingtype.tkeystr) as IRAbstractNominalTypeDecl;
            const bfdecl = ctt.fields.find(f => f.fkey === bf.fkey) as IRMemberFieldDecl;
            return bfdecl.declaredType;
        });

        return ffdecls;
    }

    static jsonEmit_IRDatatypeMemberEntityTypeDecl(tsig: IRDatatypeMemberEntityTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        
        return ntv;
    }

    static jsonParse_IRDatatypeMemberEntityTypeDecl(obj: any): IRDatatypeMemberEntityTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);

        return new IRDatatypeMemberEntityTypeDecl(...ntv);
    }
}

class IRDatatypeTypeDecl extends IRAbstractConceptTypeDecl {
    readonly dataelems: IRTypeSignature[];

    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, dataelems: IRTypeSignature[]) {
        super(tkey, invariants, validates, fields, saturatedProvides, saturatedBFieldInfo, docstr, metatags, file, sinfo);
        this.dataelems = dataelems;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        const ffdecls = this.saturatedBFieldInfo.map(bf => {
            const ctt = alltypes.get(bf.containingtype.tkeystr) as IRAbstractNominalTypeDecl;
            const bfdecl = ctt.fields.find(f => f.fkey === bf.fkey) as IRMemberFieldDecl;
            return bfdecl.declaredType;
        });
        
        return [new IRNominalTypeSignature(this.tkey), ...ffdecls];
    }

    static jsonEmit_IRDatatypeTypeDecl(tsig: IRDatatypeTypeDecl): object {
        const ntv = IRAbstractNominalTypeDecl.jsonEmitMeta_IRAbstractNominalTypeDecl(tsig);
        const dataelems = tsig.dataelems.map(de => IRTypeSignature.jsonEmit_IRTypeSignature(de));

        return {
            ...ntv,
            dataelems: dataelems
        };
    }

    static jsonParse_IRDatatypeTypeDecl(obj: any): IRDatatypeTypeDecl {
        const ntv = IRAbstractNominalTypeDecl.jsonParseMeta_IRAbstractNominalTypeDecl(obj);

        return new IRDatatypeTypeDecl(ntv[0], ntv[1], ntv[2], ntv[3], ntv[5], ntv[6], ntv[9], ntv[10], ntv[11], ntv[12], obj.dataelems.map((de: any) => IRTypeSignature.jsonParse_IRTypeSignature(de)));
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
    readonly biterms: [string, IRTypeSignature][];

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

    constructor(ikey: string, biterms: [string, IRTypeSignature][], params: IRInvokeParameterDecl[], resultType: IRTypeSignature, eventType: IRTypeSignature | undefined, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], configs: IRTaskConfiguration, statusinfo: IRTypeSignature[], envreqs: IREnvironmentVariableInformation[], resourcereqs: IRResourceInformation, body: IRBody, docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        this.ikey = ikey;
        this.biterms = biterms;
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
    readonly biterms: [string, IRTypeSignature][];

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

    constructor(ikey: string, biterms: [string, IRTypeSignature][], params: IRInvokeParameterDecl[], resultType: IRTypeSignature, eventType: IRTypeSignature | undefined, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], configs: IRTaskConfiguration, statusinfo: IRTypeSignature[], envreqs: IREnvironmentVariableInformation[], resourcereqs: IRResourceInformation, body: IRBody, docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        this.ikey = ikey;
        this.biterms = biterms;
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

class IRTaskDecl extends IRAbstractNominalTypeDecl {
    readonly configs: IRTaskConfiguration;

    readonly statusinfo: IRTypeSignature[];
    readonly envreqs: IREnvironmentVariableInformation[];
    readonly resourcereqs: IRResourceInformation;
    readonly eventinfo: IRTypeSignature[];

    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, configs: IRTaskConfiguration, statusinfo: IRTypeSignature[], envreqs: IREnvironmentVariableInformation[], resourcereqs: IRResourceInformation, eventinfo: IRTypeSignature[]) {
        super(tkey, invariants, validates, fields, "std", [], [], [], [], docstr, metatags, file, sinfo);
        
        this.configs = configs;
        this.statusinfo = statusinfo;
        this.envreqs = envreqs;
        this.resourcereqs = resourcereqs;
        this.eventinfo = eventinfo;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return []; //We should put all of these last and can't depend on each other
    }

    static jsonEmit_IRTaskDecl(tsig: IRTaskDecl) {
        assert(false, "IRTaskDecl.jsonEmit_IRTaskDecl() is not implemented yet");
    }

    static jsonParse_IRTaskDecl(obj: any): IRTaskDecl {
        assert(false, "IRTaskDecl.jsonParse_IRTaskDecl() is not implemented yet");
    }
}

class IRLambdaParameterPackDecl {
    readonly tkeystr: string;
    readonly invtrgt: string;
    readonly stdvalues: {vname: string, vtype: IRTypeSignature}[];
    readonly lambdavalues: {lname: string, ltypekey: string}[];

    constructor(tkeystr: string, invtrgt: string, stdvalues: {vname: string, vtype: IRTypeSignature}[], lambdavalues: {lname: string, ltypekey: string}[]) {
        this.tkeystr = tkeystr;
        this.invtrgt = invtrgt;
        this.stdvalues = stdvalues;
        this.lambdavalues = lambdavalues;
    }
}

class IRAssembly {
    readonly code: IRCodeFileInfo[];
    readonly macrodefs: string[];

    readonly cregexps: IRCRegex[] = [];
    readonly uregexps: IRURegex[] = [];

    readonly constants: IRConstantDecl[] = [];

    readonly tests: IRTestDecl[] = [];
    readonly examples: IRExampleDecl[] = [];

    readonly invokes: IRInvokeDecl[] = [];
    readonly taskactions: IRTaskActionDecl[] = [];

    readonly primitives: IRPrimitiveEntityTypeDecl[] = [];
    readonly constructables: IRConstructableTypeDecl[] = [];
    readonly collections: IRAbstractCollectionTypeDecl[] = [];
    readonly eventlists: IREventListTypeDecl[] = [];

    readonly enums: IREnumTypeDecl[] = [];
    readonly simpletypedecls: IRTypedeclSimpleTypeDecl[] = [];
    readonly boundedtypedecls: IRTypedeclBoundedTypeDecl[] = [];
    readonly cstringoftypedecls: IRTypedeclCStringTypeDecl[] = [];
    readonly stringoftypedecls: IRTypedeclStringTypeDecl[] = [];

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
    readonly alllambdas: Map<string, IRLambdaParameterPackDecl> = new Map<string, IRLambdaParameterPackDecl>();

    readonly elists: IREListTypeSignature[] = [];
    readonly dashtypes: IRDashResultTypeSignature[] = [];
    readonly formats: IRFormatTypeSignature[] = [];
    readonly lpacksigs: IRLambdaParameterPackTypeSignature[] = [];

    readonly formatcstrings: IRLiteralFormatCStringExpression[] = [];
    readonly formatstrings: IRLiteralFormatStringExpression[] = [];

    readonly concretesubtypes: Map<string, IRTypeSignature[]> = new Map<string, IRTypeSignature[]>();
    readonly concretesupertypes: Map<string, IRTypeSignature[]> = new Map<string, IRTypeSignature[]>();

    readonly typedeporder: IRTypeSignature[] = [];
    readonly typedepcycles: IRTypeSignature[][] = [];

    constructor(code: IRCodeFileInfo[], macrodefs: string[]) {
        this.code = code;
        this.macrodefs = macrodefs;
    }

    computeSubtypeInfo() {
        const alltl = [...this.alltypes.values()];

        for(let i = 0; i < alltl.length; i++) {
            const ctt = alltl[i];

            if(ctt instanceof IRAbstractConceptTypeDecl) {
                if(!this.concretesubtypes.has(ctt.tkey)) {
                    this.concretesubtypes.set(ctt.tkey, []);
                }
            }
            else {
                if(!this.concretesupertypes.has(ctt.tkey)) {
                    this.concretesupertypes.set(ctt.tkey, []);
                }
                let superl = this.concretesupertypes.get(ctt.tkey) as IRTypeSignature[];

                const cctsig = new IRNominalTypeSignature(ctt.tkey);
                for(let j = 0; j < ctt.saturatedProvides.length; j++) {
                    const ssuper = ctt.saturatedProvides[j];

                    if(!this.concretesubtypes.has(ssuper.tkeystr)) {
                        this.concretesubtypes.set(ssuper.tkeystr, []);
                    }
                    (this.concretesubtypes.get(ssuper.tkeystr) as IRTypeSignature[]).push(cctsig);
                    superl.push(ssuper);
                }
            }
        }

        for(const csubts of this.concretesubtypes.values()) {
            csubts.sort((a, b) => a.tkeystr.localeCompare(b.tkeystr));   
        }

        for(const csupts of this.concretesupertypes.values()) {
            csupts.sort((a, b) => a.tkeystr.localeCompare(b.tkeystr));   
        }
    }

    getTypeDependencyInfo(tsig: IRTypeSignature): IRTypeSignature[] {
        let ttl: IRTypeSignature[] = [];
        if(tsig instanceof IRLambdaParameterPackTypeSignature) {
            const lsdecl = this.alllambdas.get(tsig.tkeystr) as IRLambdaParameterPackDecl;
            ttl = [
                ...lsdecl.stdvalues.map((sv) => sv.vtype),
                ...lsdecl.lambdavalues.map((lv) => new IRLambdaParameterPackTypeSignature(lv.ltypekey))
            ];
        }
        else if(tsig instanceof IRNominalTypeSignature) {
            const ttdecl = this.alltypes.get(tsig.tkeystr) as IRAbstractNominalTypeDecl;
            ttl = ttdecl.getDeclDependencyTypes(this.alltypes);
        }
        else {
            ttl = tsig.getDirectDependencyTypes();            
        }

        //now make all the concrete subtypes explicit
        let allttl: IRTypeSignature[] = [];
        for(let i = 0; i < ttl.length; i++) {
            allttl.push(ttl[i]);

            const csubts = this.concretesubtypes.get(ttl[i].tkeystr);
            if(csubts !== undefined) {
                for(let j = 0; j < csubts.length; j++) {
                    allttl.push(csubts[j]);
                }
            }
        }

        //now make the result unique
        let resl: IRTypeSignature[] = [];
        for(let i = 0; i < allttl.length; i++) {
            if(resl.findIndex((t) => t.tkeystr === allttl[i].tkeystr) === -1) {
                resl.push(allttl[i]);
            }
        }

        return resl;
    }

    private visitType(tsig: IRTypeSignature, visited: Set<string>) {
        if(visited.has(tsig.tkeystr)) {
            return;
        }

        //If this is a SCC then we don't revisit this and we need to handle the cycle elsewhere
        visited.add(tsig.tkeystr);

        const deps = this.getTypeDependencyInfo(tsig);
        for(let i = 0; i < deps.length; i++) {
            this.visitType(deps[i], visited);
        }

        this.typedeporder.push(tsig);
    }

    private computeAllTypes(): IRTypeSignature[] {
        const allndecls = [...this.alltypes.values()].map(td => new IRNominalTypeSignature(td.tkey));
        const allsdtypes = [...this.elists, ...this.dashtypes, ...this.formats, ...this.lpacksigs];

        return [...allndecls, ...allsdtypes];
    }

    private getTypesCount(visited: Set<string>): [IRTypeSignature, number][] {
        const allpending = this.computeAllTypes().filter((t) => !visited.has(t.tkeystr));
        const ttcount = new Map<string, number>();

        for(let i = 0; i < allpending.length; i++) {
            ttcount.set(allpending[i].tkeystr, 0);
        }

        for(let i = 0; i < allpending.length; i++) {
            const deps = this.getTypeDependencyInfo(allpending[i]);
            for(let j = 0; j < deps.length; j++) {
                if(allpending[i].tkeystr !== deps[j].tkeystr) {
                    const ccount = ttcount.get(deps[j].tkeystr) as number;
                    ttcount.set(deps[j].tkeystr, ccount + 1);
                }
            }
        }

        return allpending.map<[IRTypeSignature, number]>((t) => [t, ttcount.get(t.tkeystr) as number]).sort((a, b) => a[1] - b[1]);
    }

    computeTypeDependencyInfo() {
        const visited = new Set<string>();
        let toproc = this.getTypesCount(visited);

        while(toproc.length !== 0) {
            const nrval = toproc.shift() as [IRTypeSignature, number];
            this.visitType(nrval[0], visited);

            if(nrval[1] !== 0) {
                toproc = this.getTypesCount(visited);
            }
        }

        let orderedtypes = [...this.typedeporder];
        while(orderedtypes.length !== 0) {
            const ctt = orderedtypes[0];
            const deps = this.getTypeDependencyInfo(ctt);

            let scc: IRTypeSignature[] = [];
            let cycdeps = deps.filter((d) => orderedtypes.findIndex((t) => t.tkeystr === d.tkeystr) !== -1);
            if(cycdeps.length !== 0) {
                let foundmore = true;
                while(foundmore) {
                    foundmore = false;
                    const olen = cycdeps.length;
                    for(let i = 0; i < olen; ++i) {
                        const ndeps = this.getTypeDependencyInfo(cycdeps[i]);
                        for(let j = 0; j < ndeps.length; ++j) {
                            let orr = orderedtypes.findIndex((t) => t.tkeystr === ndeps[j].tkeystr) !== -1;
                            let nadd = cycdeps.findIndex((t) => t.tkeystr === ndeps[j].tkeystr) === -1;
                            if(orr && nadd) {
                                cycdeps.push(ndeps[j])
                                foundmore = true;
                            }
                        }
                    }
                }

                scc.sort((a, b) => {
                    const apos = orderedtypes.findIndex((t) => t.tkeystr === a.tkeystr);
                    const bpos = orderedtypes.findIndex((t) => t.tkeystr === b.tkeystr);

                    return apos - bpos;
                });

                scc.push(...cycdeps);
            }

            if(scc.length === 0) {
                orderedtypes.shift();
            }
            else {
                orderedtypes = orderedtypes.filter((t) => !scc.find((st) => st.tkeystr === t.tkeystr));
                this.typedepcycles.push(scc);
            }
        }
    }

    jsonEmit(): object {
        return {
            cregexps: this.cregexps.map((cr) => cr.jsonEmit()),
            uregexps: this.uregexps.map((ur) => ur.jsonEmit()),

            //this.constants.map((c) => c.toBAPI()).join(","),
            
            //this.tests.map((t) => t.toBAPI()).join(","),
            //this.examples.map((e) => e.toBAPI()).join(","),
            
            //this.invokes.map((i) => i.toBAPI()).join(","),
            //this.taskactions.map((ta) => ta.toBAPI()).join(","),

            primitives: this.primitives.map((p) => IRPrimitiveEntityTypeDecl.jsonEmit_IRPrimitiveEntityTypeDecl(p)),

            //this.constructables.map((c) => c.toBAPI()).join(","),
            //this.collections.map((c) => c.toBAPI()).join(","),
            //this.eventlists.map((el) => el.toBAPI()).join(","),

            enums: this.enums.map((e) => IREnumTypeDecl.jsonEmit_IREnumTypeDecl(e)),
            simpletypedecls: this.simpletypedecls.map((td) => IRTypedeclSimpleTypeDecl.jsonEmit_IRTypedeclSimpleTypeDecl(td)),
            boundedtypedecls: this.boundedtypedecls.map((td) => IRTypedeclBoundedTypeDecl.jsonEmit_IRTypedeclBoundedTypeDecl(td)),
            cstringtypedecls: this.cstringoftypedecls.map((td) => IRTypedeclCStringTypeDecl.jsonEmit_IRTypedeclCStringTypeDecl(td)),
            stringtypedecls: this.stringoftypedecls.map((td) => IRTypedeclStringTypeDecl.jsonEmit_IRTypedeclStringTypeDecl(td)),

            //this.entities.map((e) => e.toBAPI()).join(","),
            //this.datamembers.map((dm) => dm.toBAPI()).join(","),
            //this.pconcepts.map((pc) => pc.toBAPI()).join(","),
            //this.concepts.map((c) => c.toBAPI()).join(","),
            //this.datatypes.map((dt) => dt.toBAPI()).join(","),
            
            //this.apis.map((api) => api.toBAPI()).join(","),
            //this.agents.map((ag) => ag.toBAPI()).join(","),
            //this.tasks.map((t) => t.toBAPI()).join(",")

            alltypesigs: this.typedeporder.map((tt) => [tt.tkeystr, IRTypeSignature.jsonEmit_IRTypeSignature(tt)]),
            alltypes: Array.from(this.alltypes.entries()).map(([k, v]) => [k, IRAbstractNominalTypeDecl.jsonEmit_IRAbstractNominalTypeDecl(v)]),
            //readonly allinvokes: Map<string, IRInvokeMetaDecl> = new Map<string, IRInvokeMetaDecl>();
            //readonly alllambdas: Map<string, IRLambdaParameterPackDecl> = new Map<string, IRLambdaParameterPackDecl>();

            elists: this.elists.map((el) => IREListTypeSignature.jsonEmit(el)),
            //this.dashtypes.map((dt) => dt.toBAPI()).join(","),
            //this.formats.map((f) => f.toBAPI()).join(","),
            //this.lpacksigs.map((lp) => lp.toBAPI()).join(","),
            
            //this.formatcstrings.map((fc) => fc.toBAPI()).join(","),
            //this.formatstrings.map((fs) => fs.toBAPI()).join(","),

            //this.concretesubtypes.entries().map(([k, v]) => `Assembly::ConcreteSubtypes{${k}, [${v.map((t) => t.toBAPI()).join(",")}]}`).join(","),
            //this.concretesupertypes.entries().map(([k, v]) => `Assembly::ConcreteSupertypes{${k}, [${v.map((t) => t.toBAPI()).join(",")}]}`).join(","),

            //this.typedeporder.map((t) => `Assembly::TypeDependencyOrder{${t.toBAPI()}}`).join(","),
            //this.typedepcycles.map((c) => `Assembly::TypeDependencyCycle{[${c.map((t) => t.toBAPI()).join(",")}]} `).join(","),

            code: this.code.map((c) => c.jsonEmit()),
            macrodefs: this.macrodefs
        };
    }

    static parseJSON(obj: any): IRAssembly {
        const code = obj.code.map((c: any) => IRCodeFileInfo.jsonParse(c));
        const macrodefs = obj.macrodefs;

        let irasm = new IRAssembly(code, macrodefs);
        
        irasm.cregexps.push(...obj.cregexps.map((c: any) => IRCRegex.jsonParse(c)));
        irasm.uregexps.push(...obj.uregexps.map((u: any) => IRURegex.jsonParse(u)));
        
        irasm.primitives.push(...obj.primitives.map((p: any) => IRPrimitiveEntityTypeDecl.jsonParse_IRPrimitiveEntityTypeDecl(p)));
        
        irasm.enums.push(...obj.enums.map((e: any) => IREnumTypeDecl.jsonParse_IREnumTypeDecl(e)));

        irasm.simpletypedecls.push(...obj.simpletypedecls.map((s: any) => IRTypedeclSimpleTypeDecl.jsonParse_IRTypedeclSimpleTypeDecl(s)));
        irasm.boundedtypedecls.push(...obj.boundedtypedecls.map((b: any) => IRTypedeclBoundedTypeDecl.jsonParse_IRTypedeclBoundedTypeDecl(b)));
        irasm.cstringoftypedecls.push(...obj.cstringoftypedecls.map((c: any) => IRTypedeclCStringTypeDecl.jsonParse_IRTypedeclCStringTypeDecl(c)));
        irasm.stringoftypedecls.push(...obj.stringoftypedecls.map((s: any) => IRTypedeclStringTypeDecl.jsonParse_IRTypedeclStringTypeDecl(s)));

        obj.alltypes.forEach(([k, v]: [string, IRAbstractNominalTypeDecl]) => irasm.alltypes.set(k, IRAbstractNominalTypeDecl.jsonParse_IRAbstractNominalTypeDecl(v)));
        
        irasm.elists.push(...obj.elists.map((e: any) => IREListTypeSignature.jsonParse(e)));

        irasm.computeTypeDependencyInfo();

        return irasm;
    }
}

export {
    IRPreConditionDecl, IRPostConditionDecl, IRInvariantDecl, IRValidateDecl,
    IRDeclarationDocString, IRDeclarationMetaTag,
    IRConstantDecl,
    IRInvokeParameterDecl, IRInvokeMetaDecl, IRTestAssociation,
    IRTestDecl, IRExampleDecl, IRInvokeDecl, IRTaskActionDecl,
    IRMemberFieldDecl,
    IRAbstractNominalTypeDecl, IRAbstractEntityTypeDecl, 
    IREnumTypeDecl, 
    IRTypedeclRngCheck, IRTypedeclAbstractTypeDecl, IRTypedeclSimpleTypeDecl, IRTypedeclBoundedTypeDecl, IRTypedeclCStringTypeDecl, IRTypedeclStringTypeDecl,
    IRInternalEntityTypeDecl, IRPrimitiveEntityTypeDecl, IRConstructableTypeDecl, 
    IROkTypeDecl, IRFailTypeDecl,
    IRAPIResultEntityTypeDecl, IRAPIDeniedTypeDecl, IRAPIErrorTypeDecl, IRAPIRejectedTypeDecl, IRAPIDroppedTypeDecl, IRAPISuccessTypeDecl,
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
    IRLambdaParameterPackDecl,
    IRAssembly
};
