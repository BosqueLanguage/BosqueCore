
import { TIRExpression, TIRLiteralValue, TIRStatement } from "./tir_body";

import { SourceInfo } from "../build_decls";
import { BSQRegex } from "../bsqregex";
import { PathValidator } from "../path_validator";

function assert(cond: boolean, msg: string) {
    if(!cond) {
        throw new Error(msg + " -- tir_assembly.ts");
    }
} 

type TIRTypeKey = string;
type TIRInvokeKey = string;
type TIRFieldKey = string;
type TIRPCodeKey = string;

class TIRTypeName {
    readonly ns: string;
    readonly name: string;
    readonly templates: TIRTypeKey[] | undefined;

    constructor(ns: string, name: string, templates?: TIRTypeKey[] | undefined) {
        this.ns = ns;
        this.name = name;
        this.templates = templates || [];
    }

    bsqemit(): any {
        return {ns: this.ns, name: this.name, templates: this.templates};
    }
    static bsqparse(jv: any): TIRTypeName {
        return new TIRTypeName(jv.ns, jv.name, jv.templates);
    }
}

class TIRFunctionParameter {
    readonly name: string;
    readonly type: TIRTypeKey;
    readonly ddlit: TIRLiteralValue | undefined;

    constructor(name: string, type: TIRTypeKey, ddlit?: TIRLiteralValue | undefined) {
        this.name = name;
        this.type = type;
        this.ddlit = ddlit;
    }

    bsqemit(): any {
        return {name: this.name, type: this.type, ddlit: this.ddlit !== undefined ? this.ddlit.bsqemit() : null};
    }
    static bsqparse(jv: any): TIRFunctionParameter {
        return new TIRFunctionParameter(jv.name, jv.type, jv.ddlit !== null ? TIRLiteralValue.bsqparse(jv.ddlit) : undefined);
    }
}

class TIRPreConditionDecl {
    readonly exp: TIRExpression;
    readonly args: TIRFunctionParameter[];

    constructor(exp: TIRExpression, args: TIRFunctionParameter[]) {
        this.exp = exp;
        this.args = args;
    }

    bsqemit(): any {
        return {exp: this.exp.bsqemit(), args: this.args.map((arg) => arg.bsqemit())};
    }
    static bsqparse(jv: any): TIRPreConditionDecl {
        return new TIRPreConditionDecl(TIRExpression.bsqparse(jv.exp), jv.args.map((arg: any) => TIRFunctionParameter.bsqparse(arg)));
    }
}

class TIRPostConditionDecl {
    readonly exp: TIRExpression;
    readonly args: TIRFunctionParameter[];

    constructor(exp: TIRExpression, args: TIRFunctionParameter[]) {
        this.exp = exp;
        this.args = args;
    }

    bsqemit(): any {
        return {exp: this.exp.bsqemit(), args: this.args.map((arg) => arg.bsqemit())};
    }
    static bsqparse(jv: any): TIRPostConditionDecl {
        return new TIRPostConditionDecl(TIRExpression.bsqparse(jv.exp), jv.args.map((arg: any) => TIRFunctionParameter.bsqparse(arg)));
    }
}

class TIRObjectInvariantDecl {
    readonly exp: TIRExpression;
    readonly args: TIRFunctionParameter[];

    constructor(exp: TIRExpression, args: TIRFunctionParameter[]) {
        this.exp = exp;
        this.args = args;
    }

    bsqemit(): any {
        return {exp: this.exp.bsqemit(), args: this.args.map((arg) => arg.bsqemit())};
    }
    static bsqparse(jv: any): TIRObjectInvariantDecl {
        return new TIRObjectInvariantDecl(TIRExpression.bsqparse(jv.exp), jv.args.map((arg: any) => TIRFunctionParameter.bsqparse(arg)));
    }
}

class TIRObjectValidateDecl {
    readonly exp: TIRExpression;
    readonly args: TIRFunctionParameter[];

    constructor(exp: TIRExpression, args: TIRFunctionParameter[]) {
        this.exp = exp;
        this.args = args;
    }

    bsqemit(): any {
        return {exp: this.exp.bsqemit(), args: this.args.map((arg) => arg.bsqemit())};
    }
    static bsqparse(jv: any): TIRObjectValidateDecl {
        return new TIRObjectValidateDecl(TIRExpression.bsqparse(jv.exp), jv.args.map((arg: any) => TIRFunctionParameter.bsqparse(arg)));
    }
}

class TIRTypedeclInvariantDecl {
    readonly exp: TIRExpression;
    readonly vtype: TIRTypeKey;

    constructor(exp: TIRExpression, vtype: TIRTypeKey) {
        this.exp = exp;
        this.vtype = vtype;
    }

    bsqemit(): any {
        return {exp: this.exp.bsqemit(), vtype: this.vtype};
    }
    static bsqparse(jv: any): TIRTypedeclInvariantDecl {
        return new TIRTypedeclInvariantDecl(TIRExpression.bsqparse(jv.exp), jv.vtype);
    }
}

class TIRTypedeclValidateDecl {
    readonly exp: TIRExpression;
    readonly vtype: TIRTypeKey;

    constructor(exp: TIRExpression, vtype: TIRTypeKey) {
        this.exp = exp;
        this.vtype = vtype;
    }

    bsqemit(): any {
        return {exp: this.exp.bsqemit(), vtype: this.vtype};
    }
    static bsqparse(jv: any): TIRTypedeclValidateDecl {
        return new TIRTypedeclValidateDecl(TIRExpression.bsqparse(jv.exp), jv.vtype);
    }
}

class TIRTaskStatusEffect {
    readonly statusinfo: TIRTypeKey[];

    constructor(statusinfo: TIRTypeKey[]) {
        this.statusinfo = statusinfo;
    }

    bsqemit(): any {
        return {statusinfo: this.statusinfo};
    }
    static bsqparse(jv: any): TIRTaskStatusEffect {
        return new TIRTaskStatusEffect(jv.statusinfo);
    }
}

class TIRTaskEventEffect {
    readonly eventinfo: TIRTypeKey[];

    constructor(eventinfo: TIRTypeKey[]) {
        this.eventinfo = eventinfo;
    }

    bsqemit(): any {
        return {eventinfo: this.eventinfo};
    }
    static bsqparse(jv: any): TIRTaskEventEffect {
        return new TIRTaskEventEffect(jv.eventinfo);
    }
}

class TIRTaskEnvironmentEffect {
    readonly readvars: string[]; //string "*" is wildcard
    readonly writevars: string[]; //string "*" is wildcard

    constructor(readvars: string[], writevars: string[]) {
        this.readvars = readvars;
        this.writevars = writevars;
    }

    bsqemit(): any {
        return {readvars: this.readvars, writevars: this.writevars};
    }
    static bsqparse(jv: any): TIRTaskEnvironmentEffect {
        return new TIRTaskEnvironmentEffect(jv.readvars, jv.writevars);
    }
}

class TIRTaskResourceEffect {
    readonly pathdescriptor: TIRTypeKey; //the resource validator
    readonly isread: boolean;
    readonly iswrite: boolean;

    readonly pathglob: TIRExpression | undefined; //returns a glob string of type PathGlob<pathdescriptor>
    readonly args: TIRFunctionParameter[];

    constructor(pathdescriptor: TIRTypeKey,  isread: boolean, iswrite: boolean, pathglob: TIRExpression | undefined, args: TIRFunctionParameter[]) {
        this.pathdescriptor = pathdescriptor;
        this.isread = isread;
        this.iswrite = iswrite;

        this.pathglob = pathglob;
        this.args = args;
    }

    bsqemit(): any {
        return {pathdescriptor: this.pathdescriptor, isread: this.isread, iswrite: this.iswrite, pathglob: this.pathglob !== undefined ? this.pathglob.bsqemit() : null, args: this.args.map((arg) => arg.bsqemit())};
    }
    static bsqparse(jv: any): TIRTaskResourceEffect {
        return new TIRTaskResourceEffect(jv.pathdescriptor, jv.isread, jv.iswrite, jv.pathglob !== null ? TIRExpression.bsqparse(jv.pathglob) : undefined, jv.args.map((arg: any) => TIRFunctionParameter.bsqparse(arg)));
    }
}

class TIRTaskEnsures {
    readonly sinfo: SourceInfo;
    readonly exp: TIRExpression;
    readonly args: TIRFunctionParameter[];

    constructor(sinfo: SourceInfo, exp: TIRExpression, args: TIRFunctionParameter[]) {
        this.sinfo = sinfo;
        this.exp = exp;
        this.args = args;
    }

    bsqemit(): any {
        return {sinfo: this.sinfo.bsqemit(), exp: this.exp.bsqemit(), args: this.args.map((arg) => arg.bsqemit())};
    }
    static bsqparse(jv: any): TIRTaskEnsures {
        return new TIRTaskEnsures(SourceInfo.bsqparse(jv.sinfo), TIRExpression.bsqparse(jv.exp), jv.args.map((arg: any) => TIRFunctionParameter.bsqparse(arg)));
    }
}

abstract class TIRInvoke {
    readonly invkey: TIRInvokeKey;
    readonly name: string;

    readonly startSourceLocation: SourceInfo;
    readonly endSourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly isrecursive: boolean;

    readonly tbinds: Map<string, TIRTypeKey>;
    readonly pcodes: Map<string, TIRPCodeKey>;

    readonly isMemberMethod: boolean;
    readonly isVirtual: boolean;
    readonly isDynamicOperator: boolean;
    readonly isLambda: boolean;

    readonly isThisRef: boolean;
    readonly params: TIRFunctionParameter[];
    
    readonly resultType: TIRTypeKey;

    readonly preconditions: TIRPreConditionDecl[];
    readonly postconditions: TIRPostConditionDecl[];

    constructor(invkey: TIRInvokeKey, name: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: string[], recursive: boolean, tbinds: Map<string, TIRTypeKey>, pcodes: Map<string, TIRPCodeKey>, isMemberMethod: boolean, isVirtual: boolean, isDynamicOperator: boolean, isLambda: boolean, params: TIRFunctionParameter[], isThisRef: boolean, resultType: TIRTypeKey, preconds: TIRPreConditionDecl[], postconds: TIRPostConditionDecl[]) {
        this.invkey = invkey;
        this.name = name;

        this.startSourceLocation = sinfoStart;
        this.endSourceLocation = sinfoEnd;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.isrecursive = recursive;

        this.tbinds = tbinds;
        this.pcodes = pcodes;

        this.isMemberMethod = isMemberMethod;
        this.isVirtual = isVirtual;
        this.isDynamicOperator = isDynamicOperator;
        this.isLambda = isLambda;

        this.isThisRef = isThisRef;
        this.params = params;

        this.resultType = resultType;

        this.preconditions = preconds;
        this.postconditions = postconds;
    }

    bsqemit_inv(): any {
        return {invkey: this.invkey, name: this.name, sinfoStart: this.startSourceLocation.bsqemit(), sinfoEnd: this.endSourceLocation.bsqemit(), srcFile: this.srcFile, attributes: this.attributes, isrecursive: this.isrecursive, tbinds: Array.from(this.tbinds.entries()), pcodes: Array.from(this.pcodes.entries()), isMemberMethod: this.isMemberMethod, isVirtual: this.isVirtual, isDynamicOperator: this.isDynamicOperator, isLambda: this.isLambda, params: this.params.map((param) => param.bsqemit()), isThisRef: this.isThisRef, resultType: this.resultType, preconds: this.preconditions.map((precond) => precond.bsqemit()), postconds: this.postconditions.map((postcond) => postcond.bsqemit())};
    }

    abstract bsqemit(): any;

    static bsqparse(jv: any): TIRInvoke {
        if(jv[0] === "InvokeAbstractDeclaration") {
            return TIRInvokeAbstractDeclaration.bsqparse(jv);
        }
        else if(jv[0] === "InvokeImplementation") {
            return TIRInvokeImplementation.bsqparse(jv);
        }
        else {
            return TIRInvokePrimitive.bsqparse(jv);
        }
    }
}

class TIRInvokeAbstractDeclaration extends TIRInvoke {
    constructor(invkey: TIRInvokeKey, name: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: string[], recursive: boolean, tbinds: Map<string, TIRTypeKey>, pcodes: Map<string, TIRPCodeKey>, isMemberMethod: boolean, isDynamicOperator: boolean, params: TIRFunctionParameter[], isThisRef: boolean, resultType: TIRTypeKey, preconds: TIRPreConditionDecl[], postconds: TIRPostConditionDecl[]) {
        super(invkey, name, sinfoStart, sinfoEnd, srcFile, attributes, recursive, tbinds, pcodes, isMemberMethod, true, isDynamicOperator, false, params, isThisRef, resultType, preconds, postconds);
    }

    bsqemit(): any {
        return ["InvokeAbstractDeclaration", this.bsqemit_inv()];
    }
    static bsqparse(jv: any): TIRInvokeAbstractDeclaration {
        assert(Array.isArray(jv) && jv[0] === "InvokeAbstractDeclaration", "InvokeAbstractDeclaration");
        
        jv = jv[1];
        return new TIRInvokeAbstractDeclaration(jv.invkey, jv.name, SourceInfo.bsqparse(jv.sinfoStart), SourceInfo.bsqparse(jv.sinfoEnd), jv.srcFile, jv.attributes, jv.isrecursive, new Map<string, TIRTypeKey>(jv.tbinds), new Map<string, TIRPCodeKey>(jv.pcodes), jv.isMemberMethod, jv.isDynamicOperator, jv.params.map((param: any) => TIRFunctionParameter.bsqparse(param)), jv.isThisRef, jv.resultType, jv.preconds.map((precond: any) => TIRPreConditionDecl.bsqparse(precond)), jv.postconds.map((postcond: any) => TIRPostConditionDecl.bsqparse(postcond)));
    }
}

class TIRInvokeImplementation extends TIRInvoke {
    readonly body: TIRStatement[];

    constructor(invkey: TIRInvokeKey, name: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: string[], recursive: boolean, tbinds: Map<string, TIRTypeKey>, pcodes: Map<string, TIRPCodeKey>, isMemberMethod: boolean, isVirtual: boolean, isDynamicOperator: boolean, isLambda: boolean, params: TIRFunctionParameter[], isThisRef: boolean, resultType: TIRTypeKey, preconds: TIRPreConditionDecl[], postconds: TIRPostConditionDecl[], body: TIRStatement[]) {
        super(invkey, name, sinfoStart, sinfoEnd, srcFile, attributes, recursive, tbinds, pcodes, isMemberMethod, isVirtual, isDynamicOperator, isLambda, params, isThisRef, resultType, preconds, postconds);

        this.body = body;
    }

    bsqemit(): any {
        return ["InvokeImplementation", {...this.bsqemit_inv(), body: this.body.map((stmt) => stmt.bsqemit())}];
    }
    static bsqparse(jv: any): TIRInvokeImplementation {
        assert(Array.isArray(jv) && jv[0] === "InvokeImplementation", "InvokeImplementation");
        
        jv = jv[1];
        const body = jv.body.map((stmt: any) => TIRStatement.bsqparse(stmt));
        return new TIRInvokeImplementation(jv.invkey, jv.name, SourceInfo.bsqparse(jv.sinfoStart), SourceInfo.bsqparse(jv.sinfoEnd), jv.srcFile, jv.attributes, jv.isrecursive, new Map<string, TIRTypeKey>(jv.tbinds), new Map<string, TIRPCodeKey>(jv.pcodes), jv.isMemberMethod, jv.isVirtual, jv.isDynamicOperator, jv.isLambda, jv.params.map((param: any) => TIRFunctionParameter.bsqparse(param)), jv.isThisRef, jv.resultType, jv.preconds.map((precond: any) => TIRPreConditionDecl.bsqparse(precond)), jv.postconds.map((postcond: any) => TIRPostConditionDecl.bsqparse(postcond)), body);
    }
}

class TIRInvokePrimitive extends TIRInvoke {
    readonly body: string;

    constructor(invkey: TIRInvokeKey, name: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: string[], recursive: boolean, tbinds: Map<string, TIRTypeKey>, pcodes: Map<string, TIRPCodeKey>, params: TIRFunctionParameter[], resultType: TIRTypeKey, body: string) {
        super(invkey, name, sinfoStart, sinfoEnd, srcFile, attributes, recursive, tbinds, pcodes, false, false, false, false, params, false, resultType, [], []);

        this.body = body;
    }

    bsqemit(): any {
        return ["InvokePrimitive", {...this.bsqemit_inv(), body: this.body}];
    }
    static bsqparse(jv: any): TIRInvokePrimitive {
        assert(Array.isArray(jv) && jv[0] === "InvokePrimitive", "InvokePrimitive");
        
        jv = jv[1];
        const body = jv.body;
        return new TIRInvokePrimitive(jv.invkey, jv.name, SourceInfo.bsqparse(jv.sinfoStart), SourceInfo.bsqparse(jv.sinfoEnd), jv.srcFile, jv.attributes, jv.isrecursive, new Map<string, TIRTypeKey>(jv.tbinds), new Map<string, TIRPCodeKey>(jv.pcodes), jv.params.map((param: any) => TIRFunctionParameter.bsqparse(param)), jv.resultType, body);
    }
}

abstract class TIRMemberDecl {
    readonly tkey: TIRTypeKey;
    readonly name: string;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];

    constructor(tkey: TIRTypeKey, name: string, srcInfo: SourceInfo, srcFile: string, attributes: string[]) {
        this.tkey = tkey;
        this.name = name;
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
    }

    bsqemit_decl(): any {
        return {tkey: this.tkey, name: this.name, sinfo: this.sourceLocation.bsqemit(), srcFile: this.srcFile, attributes: this.attributes};
    }

    abstract bsqemit(): any;

    static bsqparse(jv: any): TIRMemberDecl {
        if(jv[0] === "ConstMemberDecl") {
            return TIRConstMemberDecl.bsqparse(jv);
        }
        else if (jv[0] === "StaticFunctionDecl") {
            return TIRStaticFunctionDecl.bsqparse(jv);
        }
        else if(jv[0] === "MemberFieldDecl") {
            return TIRMemberFieldDecl.bsqparse(jv);
        }
        else {
            assert(jv[0] === "MemberMethodDecl", "MemberMethodDecl");

            return TIRMemberMethodDecl.bsqparse(jv);
        }
    }
}

class TIRConstMemberDecl extends TIRMemberDecl {
    readonly declaredType: TIRTypeKey;
    readonly value: TIRExpression;

    constructor(tkey: TIRTypeKey, name: string, srcInfo: SourceInfo, srcFile: string, attributes: string[], declaredtype: TIRTypeKey, value: TIRExpression) {
        super(tkey, name, srcInfo, srcFile, attributes);
        this.declaredType = declaredtype;
        this.value = value;
    }

    bsqemit(): any {
        return ["ConstMemberDecl", {...this.bsqemit_decl(), declaredType: this.declaredType, value: this.value.bsqemit()}];
    }
    static bsqparse(jv: any): TIRConstMemberDecl {
        assert(Array.isArray(jv) && jv[0] === "ConstMemberDecl", "ConstMemberDecl");
        
        jv = jv[1];
        const declaredType = jv.declaredType;
        const value = TIRExpression.bsqparse(jv.value);
        return new TIRConstMemberDecl(jv.tkey, jv.name, SourceInfo.bsqparse(jv.sinfo), jv.srcFile, jv.attributes, declaredType, value);
    }
}

class TIRStaticFunctionDecl extends TIRMemberDecl {
    readonly ikey: TIRInvokeKey;
    readonly invoke: TIRInvoke;

    constructor(tkey: TIRTypeKey, sinfo: SourceInfo, srcFile: string, invoke: TIRInvoke) {
        super(tkey, invoke.name, sinfo, srcFile, invoke.attributes);
        this.ikey = invoke.invkey;
        this.invoke = invoke;
    }

    bsqemit(): any {
        return ["StaticFunctionDecl", {...this.bsqemit_decl(), invoke: this.invoke.bsqemit()}];
    }
    static bsqparse(jv: any): TIRStaticFunctionDecl {
        assert(Array.isArray(jv) && jv[0] === "StaticFunctionDecl", "StaticFunctionDecl");
        
        jv = jv[1];
        return new TIRStaticFunctionDecl(jv.tkey, SourceInfo.bsqparse(jv.sinfo), jv.srcFile, TIRInvoke.bsqparse(jv.invoke));
    }
}

class TIRMemberFieldDecl extends TIRMemberDecl {
    readonly fkey: TIRFieldKey;
    readonly declaredType: TIRTypeKey;

    constructor(fkey: TIRFieldKey, tkey: TIRTypeKey, name: string, srcInfo: SourceInfo, srcFile: string, attributes: string[], declaredtype: TIRTypeKey) {
        super(tkey, name, srcInfo, srcFile, attributes);
        this.fkey = fkey;
        this.declaredType = declaredtype;
    }

    bsqemit() {
        return ["MemberFieldDecl", {...this.bsqemit_decl(), fkey: this.fkey, declaredType: this.declaredType}];
    }
    static bsqparse(jv: any): TIRMemberFieldDecl {
        assert(Array.isArray(jv) && jv[0] === "MemberFieldDecl", "MemberFieldDecl");
        
        jv = jv[1];
        return new TIRMemberFieldDecl(jv.fkey, jv.tkey, jv.name, SourceInfo.bsqparse(jv.sinfo), jv.srcFile, jv.attributes, jv.declaredType);
    }
}

class TIRMemberMethodDecl extends TIRMemberDecl {
    readonly ikey: TIRInvokeKey;
    readonly invoke: TIRInvoke;

    constructor(tkey: TIRTypeKey, sinfo: SourceInfo, srcFile: string, invoke: TIRInvoke) {
        super(tkey, invoke.name, sinfo, srcFile, invoke.attributes);
        this.ikey = invoke.invkey;
        this.invoke = invoke;
    }

    bsqemit() {
        return ["MemberMethodDecl", {...this.bsqemit_decl(), invoke: this.invoke.bsqemit()}];
    }
    static bsqparse(jv: any): TIRMemberMethodDecl {
        assert(Array.isArray(jv) && jv[0] === "MemberMethodDecl", "MemberMethodDecl");
        
        jv = jv[1];
        return new TIRMemberMethodDecl(jv.tkey, SourceInfo.bsqparse(jv.sinfo), jv.srcFile, TIRInvoke.bsqparse(jv.invoke));
    }
}

abstract class TIRType {
    readonly tkey: TIRTypeKey;

    //direct suprertypes -- not saturated set
    readonly supertypes: Set<TIRTypeKey> | undefined;
    readonly isexportable: boolean;

    constructor(tkey: TIRTypeKey, supertypes: TIRTypeKey[] | undefined, isexportable: boolean) {
        this.tkey = tkey;
        this.supertypes = supertypes !== undefined ? new Set<TIRTypeKey>(supertypes) : undefined;
        this.isexportable = isexportable;
    }

    bsqemit_type(): any {
        return {tkey: this.tkey, supertypes: this.supertypes !== undefined ? [...this.supertypes] : null, isexportable: this.isexportable};
    }

    abstract bsqemit(): any;

    static bsqparse(jv: any): TIRType {
        if(jv[0] === "ObjectEntityType") {
            return TIRObjectEntityType.bsqparse(jv);
        }
        else if(jv[0] === "EnumEntityType") {
            return TIREnumEntityType.bsqparse(jv);
        }
        else if(jv[0] === "TypedeclEntityType") {
            return TIRTypedeclEntityType.bsqparse(jv);
        }
        else if(jv[0] === "PrimitiveInternalEntityType") {
            return TIRPrimitiveInternalEntityType.bsqparse(jv);
        }
        else if(jv[0] === "ValidatorEntityType") {
            return TIRValidatorEntityType.bsqparse(jv);
        }
        else if(jv[0] === "StringOfEntityType") {
            return TIRStringOfEntityType.bsqparse(jv);
        }
        else if(jv[0] === "ASCIIStringOfEntityType") {
            return TIRASCIIStringOfEntityType.bsqparse(jv);
        }
        else if(jv[0] === "PathValidatorEntityType") {
            return TIRPathValidatorEntityType.bsqparse(jv);
        }
        else if(jv[0] === "PathEntityType") {
            return TIRPathEntityType.bsqparse(jv);
        }
        else if(jv[0] === "PathFragmentEntityType") {
            return TIRPathFragmentEntityType.bsqparse(jv);
        }
        else if(jv[0] === "PathGlobEntityType") {
            return TIRPathGlobEntityType.bsqparse(jv);
        }
        else if(jv[0] === "OkEntityType") {
            return TIROkEntityType.bsqparse(jv);
        }
        else if(jv[0] === "ErrEntityType") {
            return TIRErrEntityType.bsqparse(jv);
        }
        else if(jv[0] === "SomethingEntityType") {
            return TIRSomethingEntityType.bsqparse(jv);
        }
        else if(jv[0] === "MapEntryEntityType") {
            return TIRMapEntryEntityType.bsqparse(jv);
        }
        else if(jv[0] === "HavocEntityType") {
            return TIRHavocEntityType.bsqparse(jv);
        }
        else if(jv[0] === "ListEntityType") {
            return TIRListEntityType.bsqparse(jv);
        }
        else if(jv[0] === "StackEntityType") {
            return TIRStackEntityType.bsqparse(jv);
        }
        else if(jv[0] === "QueueEntityType") {
            return TIRQueueEntityType.bsqparse(jv);
        }
        else if(jv[0] === "SetEntityType") {
            return TIRSetEntityType.bsqparse(jv);
        }
        else if(jv[0] === "MapEntityType") {
            return TIRMapEntityType.bsqparse(jv);
        }
        else if(jv[0] === "TaskType") {
            return TIRTaskType.bsqparse(jv);
        }
        else if(jv[0] === "ConceptType") {
            return TIRConceptType.bsqparse(jv);
        }
        else if(jv[0] === "ConceptSetType") {
            return TIRConceptSetType.bsqparse(jv);
        }
        else if(jv[0] === "TupleType") {
            return TIRTupleType.bsqparse(jv);
        }
        else if(jv[0] === "RecordType") {
            return TIRRecordType.bsqparse(jv);
        }
        else if(jv[0] === "UnionType") {
            return TIRUnionType.bsqparse(jv);
        }
        else if(jv[0] === "EListType") {
            return TIREListType.bsqparse(jv);
        }
        else {
            assert(false, "TIRType: " + jv[0]);
            return (undefined as any) as TIRType;
        }
    }
}

abstract class TIROOType extends TIRType {
    readonly tname: TIRTypeName;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];

    readonly constMembers: TIRConstMemberDecl[] = [];
    readonly staticFunctions: TIRStaticFunctionDecl[] = [];
    readonly memberFields: TIRMemberFieldDecl[] = [];
    readonly memberMethods: TIRMemberMethodDecl[] = [];

    readonly iskeytype: boolean;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], iskeytype: boolean, isexportable: boolean) {
        super(tkey, supertypes, isexportable);
        this.tname = tname;
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.iskeytype = iskeytype;
    }

    bsqemit_ootype(): any {
        return {...this.bsqemit_type(), tname: this.tname, sinfo: this.sourceLocation.bsqemit(), srcFile: this.srcFile, attributes: this.attributes, constMembers: this.constMembers.map((x) => x.bsqemit()), staticFunctions: this.staticFunctions.map((x) => x.bsqemit()), memberFields: this.memberFields.map((x) => x.bsqemit()), memberMethods: this.memberMethods.map((x) => x.bsqemit()), iskeytype: this.iskeytype};
    }
    static bsqparse_ooinfo(jv: any, tt: TIROOType) {
        tt.constMembers.push(...jv.constMembers.map((x: any) => TIRConstMemberDecl.bsqparse(x)));
        tt.staticFunctions.push(...jv.staticFunctions.map((x: any) => TIRStaticFunctionDecl.bsqparse(x)));
        tt.memberFields.push(...jv.memberFields.map((x: any) => TIRMemberFieldDecl.bsqparse(x)));
        tt.memberMethods.push(...jv.memberMethods.map((x: any) => TIRMemberMethodDecl.bsqparse(x)));
    }
}

abstract class TIREntityType extends TIROOType {
    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], iskeytype: boolean, isexportable: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, iskeytype, isexportable);
    }

    bsqemit_entitytype(): any {
        return {...this.bsqemit_ootype()};
    }
}

//Represents types declared as entities in the code
class TIRObjectEntityType extends TIREntityType {
    readonly allfields: {fkey: TIRFieldKey, ftype: TIRTypeKey}[] = [];

    readonly consinvariants: TIRObjectInvariantDecl[] = []; 
    readonly apivalidates: TIRObjectValidateDecl[] = [];

    readonly vtable: Map<string, TIRInvokeKey> = new Map<string, TIRInvokeKey>(); 
    readonly binds: Map<string, TIRTypeKey>;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], binds: Map<string, TIRTypeKey>, isexportable: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false, isexportable);
        this.binds = binds;
    }

    bsqemit(): any {
        return ["ObjectEntityType", {...this.bsqemit_entitytype(), allfields: this.allfields, consinvariants: this.consinvariants.map((x) => x.bsqemit()), apivalidates: this.apivalidates.map((x) => x.bsqemit()), vtable: [...this.vtable], binds: [...this.binds]}];
    }
    static bsqparse(jv: any): TIRObjectEntityType {
        assert(Array.isArray(jv) && jv[0] === "ObjectEntityType", "ObjectEntityType");
        
        jv = jv[1];
        const rr = new TIRObjectEntityType(jv.tkey, jv.tname, SourceInfo.bsqparse(jv.sinfo), jv.srcFile, jv.attributes, jv.supertypes, new Map<string, TIRTypeKey>(jv.binds), jv.isexportable);
        TIROOType.bsqparse_ooinfo(jv, rr);

        rr.allfields.push(...jv.allfields);
        rr.consinvariants.push(...jv.consinvariants.map((x: any) => TIRObjectInvariantDecl.bsqparse(x)));
        rr.apivalidates.push(...jv.apivalidates.map((x: any) => TIRObjectValidateDecl.bsqparse(x)));
        jv.vtable.forEach((x: any) => rr.vtable.set(x[0], x[1]));

        return rr;
    }
}

//Represents enum types declared as entities in the code
class TIREnumEntityType extends TIREntityType {
    readonly enums: string[];
    readonly litvals: Map<string, TIRLiteralValue> = new Map<string, TIRLiteralValue>();

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], enums: string[]) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, true, true);
        this.enums = enums;
    }

    bsqemit(): any {
        return ["EnumEntityType", {...this.bsqemit_entitytype(), enums: this.enums, litvals: [...this.litvals].map((x) => [x[0], x[1].bsqemit()])}];
    }
    static bsqparse(jv: any): TIREnumEntityType {
        assert(Array.isArray(jv) && jv[0] === "EnumEntityType", "EnumEntityType");
        
        jv = jv[1];
        const rr = new TIREnumEntityType(jv.tkey, jv.tname, SourceInfo.bsqparse(jv.sinfo), jv.srcFile, jv.attributes, jv.supertypes, jv.enums);
        TIROOType.bsqparse_ooinfo(jv, rr);

        jv.litvals.forEach((x: any) => rr.litvals.set(x[0], TIRLiteralValue.bsqparse(x[1])));

        return rr;
    }
}

//Represents typedecl T = X ... types where the representation is a single primitve typed value
class TIRTypedeclEntityType extends TIREntityType {
    readonly valuetype: TIRTypeKey; //result of .value()
    readonly representation: TIRTypeKey; //result of getUnderlyingRepresentation opcode -- a TIRResolvedPrimitiveInternalEntityAtomType

    readonly consinvariantsall: TIRTypedeclInvariantDecl[] = []; 
    readonly consinvariantsexplicit: TIRTypedeclInvariantDecl[] = []; 
    readonly apivalidates: TIRTypedeclValidateDecl[] = [];

    readonly strvalidator: {vtype: TIRTypeKey, vre: BSQRegex} | undefined; //TIRValidatorEntityType;
    readonly pthvalidator: {vtype: TIRTypeKey, vpth: PathValidator, kind: "path" | "pathfragment" | "pathglob"} | undefined; //TIRPathValidatorEntityType;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], valuetype: TIRTypeKey, representation: TIRTypeKey, strvalidator: {vtype: TIRTypeKey, vre: BSQRegex} | undefined, pthvalidator: {vtype: TIRTypeKey, vpth: PathValidator, kind: "path" | "pathfragment" | "pathglob"} | undefined, iskeytype: boolean, isexportable: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, iskeytype, isexportable);
        this.valuetype = valuetype;
        this.representation = representation;
        this.strvalidator = strvalidator;
        this.pthvalidator = pthvalidator;
    }

    bsqemit(): any {
        return ["TypedeclEntityType", {...this.bsqemit_entitytype(), valuetype: this.valuetype, representation: this.representation, consinvariantsall: this.consinvariantsall.map((x) => x.bsqemit()), consinvariantsexplicit: this.consinvariantsexplicit.map((x) => x.bsqemit()), apivalidates: this.apivalidates.map((x) => x.bsqemit()), 
            strvalidator: this.strvalidator !== undefined ? {vtype: this.strvalidator.vtype, vre: this.strvalidator.vre.jemit() } : null,
            pthvalidator: this.pthvalidator !== undefined ? {vtype: this.pthvalidator, vpth: this.pthvalidator.vpth.jemit(), kind: this.pthvalidator.kind} : null}];
    }
    static bsqparse(jv: any): TIRTypedeclEntityType {
        assert(Array.isArray(jv) && jv[0] === "TypedeclEntityType", "TypedeclEntityType");
        
        jv = jv[1];
        const rr = new TIRTypedeclEntityType(jv.tkey, jv.tname, SourceInfo.bsqparse(jv.sinfo), jv.srcFile, jv.attributes, jv.supertypes, jv.valuetype, jv.representation, jv.strvalidator !== null ? {vtype: jv.strvalidator.vtype, vre: BSQRegex.jparse(jv.strvalidator.vre)} : undefined, jv.pthvalidator !== null ? {vtype: jv.pthvalidator.vtype, vpth: PathValidator.jparse(jv.pthvalidator.vpth), kind: jv.pthvalidator.kind} : undefined, jv.iskeytype, jv.isexportable);
        TIROOType.bsqparse_ooinfo(jv, rr);
        
        rr.consinvariantsall.push(...jv.consinvariantsall.map((x: any) => TIRTypedeclInvariantDecl.bsqparse(x)));
        rr.consinvariantsexplicit.push(...jv.consinvariantsexplicit.map((x: any) => TIRTypedeclInvariantDecl.bsqparse(x)));
        rr.apivalidates.push(...jv.apivalidates.map((x: any) => TIRTypedeclValidateDecl.bsqparse(x)));

        return rr;
    }
}

//base class for all the primitive types that are defined
abstract class TIRInternalEntityType extends TIREntityType {
    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], iskeytype: boolean, isexportable: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, iskeytype, isexportable);
    }

    bsqemit_internalentity(): any {
        return {...this.bsqemit_entitytype()};
    }
} 

//class representing all the primitive values (Int, Bool, String, ...). All of these are special implemented values
class TIRPrimitiveInternalEntityType extends TIRInternalEntityType {
    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], iskeytype: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, iskeytype, true);
    }

    bsqemit(): any {
        return ["PrimitiveInternalEntityType", this.bsqemit_internalentity()];
    }
    static bsqparse(jv: any): TIRPrimitiveInternalEntityType {
        assert(Array.isArray(jv) && jv[0] === "PrimitiveInternalEntityType", "PrimitiveInternalEntityType");
        const rr = new TIRPrimitiveInternalEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].iskeytype);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
} 

//class representing Validator regex types
class TIRValidatorEntityType extends TIRInternalEntityType {
    readonly revalidator: BSQRegex;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], revalidator: BSQRegex) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false, false);
        this.revalidator = revalidator;
    }

    bsqemit(): any {
        return ["ValidatorEntityType", {...this.bsqemit_internalentity(), revalidator: this.revalidator.jemit()}];
    }
    static bsqparse(jv: any): TIRValidatorEntityType {
        assert(Array.isArray(jv) && jv[0] === "ValidatorEntityType", "ValidatorEntityType");
        const rr = new TIRValidatorEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, BSQRegex.jparse(jv[1].revalidator));
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing StringOf<T> types
class TIRStringOfEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey; //TIRValidatorEntityType;
    readonly revalidator: BSQRegex;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], validatortype: TIRTypeKey, revalidator: BSQRegex) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, true, true);
        this.validatortype = validatortype;
        this.revalidator = revalidator;
    }

    bsqemit(): any {
        return ["StringOfEntityType", {...this.bsqemit_internalentity(), validatortype: this.validatortype, revalidator: this.revalidator.jemit()}];
    }
    static bsqparse(jv: any): TIRStringOfEntityType {
        assert(Array.isArray(jv) && jv[0] === "StringOfEntityType", "StringOfEntityType");
        const rr = new TIRStringOfEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].validatortype, BSQRegex.jparse(jv[1].revalidator));
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing ASCIIStringOf<T> types
class TIRASCIIStringOfEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey; //TIRValidatorEntityType;
    readonly revalidator: BSQRegex;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], validatortype: TIRTypeKey, revalidator: BSQRegex) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, true, true);
        this.validatortype = validatortype;
        this.revalidator = revalidator;
    }

    bsqemit(): any {
        return ["ASCIIStringOfEntityType", {...this.bsqemit_internalentity(), validatortype: this.validatortype, revalidator: this.revalidator.jemit()}];
    }
    static bsqparse(jv: any): TIRASCIIStringOfEntityType {
        assert(Array.isArray(jv) && jv[0] === "ASCIIStringOfEntityType", "ASCIIStringOfEntityType");
        const rr = new TIRASCIIStringOfEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].validatortype, BSQRegex.jparse(jv[1].revalidator));
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing PathValidator types
class TIRPathValidatorEntityType extends TIRInternalEntityType {
    readonly pthvalidator: PathValidator;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], pthvalidator: PathValidator) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false, false);
        this.pthvalidator = pthvalidator;
    }

    bsqemit(): any {
        return ["PathValidatorEntityType", {...this.bsqemit_internalentity(), pthvalidator: this.pthvalidator.jemit()}];
    }
    static bsqparse(jv: any): TIRPathValidatorEntityType {
        assert(Array.isArray(jv) && jv[0] === "PathValidatorEntityType", "PathValidatorEntityType");
        const rr = new TIRPathValidatorEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, PathValidator.jparse(jv[1].pthvalidator));
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing a Path<T> type
class TIRPathEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey //TIRPathValidatorEntityType;
    readonly pthvalidator: PathValidator;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], validatortype: TIRTypeKey, pthvalidator: PathValidator) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, true, true);
        this.validatortype = validatortype;
        this.pthvalidator = pthvalidator;
    }

    bsqemit(): any {
        return ["PathEntityType", {...this.bsqemit_internalentity(), validatortype: this.validatortype, pthvalidator: this.pthvalidator.jemit()}];
    }
    static bsqparse(jv: any): TIRPathEntityType {
        assert(Array.isArray(jv) && jv[0] === "PathEntityType", "PathEntityType");
        const rr = new TIRPathEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].validatortype, PathValidator.jparse(jv[1].pthvalidator));
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing a PathFragment<T> type
class TIRPathFragmentEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey //TIRPathValidatorEntityType;
    readonly pthvalidator: PathValidator;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], validatortype: TIRTypeKey, pthvalidator: PathValidator) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, true, true);
        this.validatortype = validatortype;
        this.pthvalidator = pthvalidator;
    }

    bsqemit(): any {
        return ["PathFragmentEntityType", {...this.bsqemit_internalentity(), validatortype: this.validatortype, pthvalidator: this.pthvalidator.jemit()}];
    }
    static bsqparse(jv: any): TIRPathFragmentEntityType {
        assert(Array.isArray(jv) && jv[0] === "PathFragmentEntityType", "PathFragmentEntityType");
        const rr = new TIRPathFragmentEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].validatortype, PathValidator.jparse(jv[1].pthvalidator));
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

class TIRPathGlobEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey //TIRPathValidatorEntityType;
    readonly pthvalidator: PathValidator;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], validatortype: TIRTypeKey, pthvalidator: PathValidator) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, true, true);
        this.validatortype = validatortype;
        this.pthvalidator = pthvalidator;
    }

    bsqemit(): any {
        return ["PathGlobEntityType", {...this.bsqemit_internalentity(), validatortype: this.validatortype, pthvalidator: this.pthvalidator.jemit()}];
    }
    static bsqparse(jv: any): TIRPathGlobEntityType {
        assert(Array.isArray(jv) && jv[0] === "PathGlobEntityType", "PathGlobEntityType");
        const rr = new TIRPathGlobEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].validatortype, PathValidator.jparse(jv[1].pthvalidator));
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing Ok, Err, Something types
abstract class TIRConstructableEntityType extends TIRInternalEntityType {
    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], isexportable: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false, isexportable);
    }

    bsqemit_constructable(): any {
        return this.bsqemit_internalentity();
    }
}

class TIROkEntityType extends TIRConstructableEntityType {
    readonly typeT: TIRTypeKey;
    readonly typeE: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey, typeE: TIRTypeKey, isexportable: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, isexportable);
        this.typeT = typeT;
        this.typeE = typeE;
    }

    bsqemit(): any {
        return ["OkEntityType", {...this.bsqemit_constructable(), typeT: this.typeT, typeE: this.typeE}];
    }
    static bsqparse(jv: any): TIROkEntityType {
        assert(Array.isArray(jv) && jv[0] === "OkEntityType", "OkEntityType");
        const rr = new TIROkEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeT, jv[1].typeE, jv[1].isexportable);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

class TIRErrEntityType extends TIRConstructableEntityType {
    readonly typeT: TIRTypeKey;
    readonly typeE: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey, typeE: TIRTypeKey, isexportable: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, isexportable);
        this.typeT = typeT;
        this.typeE = typeE;
    }

    bsqemit(): any {
        return ["ErrEntityType", {...this.bsqemit_constructable(), typeT: this.typeT, typeE: this.typeE}];
    }
    static bsqparse(jv: any): TIRErrEntityType {
        assert(Array.isArray(jv) && jv[0] === "ErrEntityType", "ErrEntityType");
        const rr = new TIRErrEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeT, jv[1].typeE, jv[1].isexportable);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

class TIRSomethingEntityType extends TIRConstructableEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey, isexportable: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, isexportable);
        this.typeT = typeT;
    }

    bsqemit(): any {
        return ["SomethingEntityType", {...this.bsqemit_constructable(), typeT: this.typeT}];
    }
    static bsqparse(jv: any): TIRSomethingEntityType {
        assert(Array.isArray(jv) && jv[0] === "SomethingEntityType", "SomethingEntityType");
        const rr = new TIRSomethingEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeT, jv[1].isexportable);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

class TIRMapEntryEntityType extends TIRConstructableEntityType {
    readonly typeK: TIRTypeKey;
    readonly typeV: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeK: TIRTypeKey, typeV: TIRTypeKey, isexportable: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, isexportable);
        this.typeK = typeK;
        this.typeV = typeV;
    }

    bsqemit(): any {
        return ["MapEntryEntityType", {...this.bsqemit_constructable(), typeK: this.typeK, typeV: this.typeV}];
    }
    static bsqparse(jv: any): TIRMapEntryEntityType {
        assert(Array.isArray(jv) && jv[0] === "MapEntryEntityType", "MapEntryEntityType");
        const rr = new TIRMapEntryEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeK, jv[1].typeV, jv[1].isexportable);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing special havoc type
class TIRHavocEntityType extends TIRInternalEntityType {
    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[]) {
        super(tkey, tname, srcInfo, srcFile, attributes, [], false, false);
    }

    bsqemit(): any {
        return ["HavocEntityType", this.bsqemit_internalentity()];
    }
    static bsqparse(jv: any): TIRHavocEntityType {
        assert(Array.isArray(jv) && jv[0] === "HavocEntityType", "HavocEntityType");
        return new TIRHavocEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes);
    }
}

//abstract class for all the builtin collection types
abstract class TIRPrimitiveCollectionEntityType extends TIRInternalEntityType {
    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], isexportable: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false, isexportable);
    }

    bsqemit_collection(): any {
        return this.bsqemit_internalentity();
    }
}

//class representing List<T>
class TIRListEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey, isexportable: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, isexportable);
        this.typeT = typeT;
    }

    bsqemit(): any {
        return ["ListEntityType", {...this.bsqemit_collection(), typeT: this.typeT}];
    }
    static bsqparse(jv: any): TIRListEntityType {
        assert(Array.isArray(jv) && jv[0] === "ListEntityType", "ListEntityType");
        const rr = new TIRListEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeT, jv[1].isexportable);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing Stack<T>
class TIRStackEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey, isexportable: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, isexportable);
        this.typeT = typeT;
    }

    bsqemit(): any {
        return ["StackEntityType", {...this.bsqemit_collection(), typeT: this.typeT}];
    }
    static bsqparse(jv: any): TIRStackEntityType {
        assert(Array.isArray(jv) && jv[0] === "StackEntityType", "StackEntityType");
        const rr = new TIRStackEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeT, jv[1].isexportable);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing Queue<T>
class TIRQueueEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey, isexportable: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, isexportable);
        this.typeT = typeT;
    }

    bsqemit(): any {
        return ["QueueEntityType", {...this.bsqemit_collection(), typeT: this.typeT}];
    }
    static bsqparse(jv: any): TIRQueueEntityType {
        assert(Array.isArray(jv) && jv[0] === "QueueEntityType", "QueueEntityType");
        const rr = new TIRQueueEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeT, jv[1].isexportable);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing Set<T>
class TIRSetEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey, isexportable: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, isexportable);
        this.typeT = typeT;
    }

    bsqemit(): any {
        return ["SetEntityType", {...this.bsqemit_collection(), typeT: this.typeT}];
    }
    static bsqparse(jv: any): TIRSetEntityType {
        assert(Array.isArray(jv) && jv[0] === "SetEntityType", "SetEntityType");
        const rr = new TIRSetEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeT, jv[1].isexportable);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing Map<K, V>
class TIRMapEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeK: TIRTypeKey;
    readonly typeV: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeK: TIRTypeKey, typeV: TIRTypeKey, isexportable: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, isexportable);
        this.typeK = typeK;
        this.typeV = typeV;
    }

    bsqemit(): any {
        return ["MapEntityType", {...this.bsqemit_collection(), typeK: this.typeK, typeV: this.typeV}];
    }
    static bsqparse(jv: any): TIRMapEntityType {
        assert(Array.isArray(jv) && jv[0] === "MapEntityType", "MapEntityType");
        const rr = new TIRMapEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeK, jv[1].typeV, jv[1].isexportable);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

class TIRTaskType extends TIROOType {
    readonly binds: Map<string, TIRTypeKey>;

    readonly controls: {val: TIRLiteralValue | undefined, cname: string}[] = []; //control members
    readonly actions: {akey: TIRInvokeKey, aname: string}[] = []; //methods
    readonly mainfunc: {mkey: TIRInvokeKey, mname: string}; //a static function
    readonly onfuncs: { onCanel: TIRInvokeKey | undefined, onFailure: TIRInvokeKey | undefined, onTimeout: TIRInvokeKey | undefined };
    readonly lfuncs: { logStart: TIRInvokeKey | undefined, logEnd: TIRInvokeKey | undefined, taskEnsures: TIRInvokeKey | undefined, taskWarns: TIRInvokeKey | undefined };


    readonly statuseffect: TIRTaskStatusEffect = new TIRTaskStatusEffect([]);
    readonly eventeffect: TIRTaskEventEffect = new TIRTaskEventEffect([]);
    readonly enveffect: TIRTaskEnvironmentEffect = new TIRTaskEnvironmentEffect([], []);
    readonly resourceeffect: TIRTaskResourceEffect[] = [];

    readonly ensures: TIRTaskEnsures[] = [];

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], 
        binds: Map<string, TIRTypeKey>, mainfunc: {mkey: TIRInvokeKey, mname: string}, 
        onfuncs: { onCanel: TIRInvokeKey | undefined, onFailure: TIRInvokeKey | undefined, onTimeout: TIRInvokeKey | undefined },
        lfuncs: { logStart: TIRInvokeKey | undefined, logEnd: TIRInvokeKey | undefined, taskEnsures: TIRInvokeKey | undefined, taskWarns: TIRInvokeKey | undefined }
    ) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false, false);
        this.binds = binds;
        this.mainfunc = mainfunc;
        this.onfuncs = onfuncs;
        this.lfuncs = lfuncs;
    }

    bsqemit(): any {
        return ["TaskType", {...this.bsqemit_ootype(), binds: [...this.binds], controls: this.controls.map((cc) => ({val: cc.val ? cc.val.bsqemit() : null, cname: cc.cname})), actions: this.actions, mainfunc: this.mainfunc, onfuncs: {onCancel: this.onfuncs.onCanel || null, onFailure: this.onfuncs.onFailure || null, onTimeout: this.onfuncs.onTimeout || null}, lfuncs: {logStart: this.lfuncs.logStart || null, logEnd: this.lfuncs.logEnd || null, taskEnsures: this.lfuncs.taskEnsures || null, taskWarns: this.lfuncs.taskWarns || null }, statuseffect: this.statuseffect.bsqemit(), eventeffect: this.eventeffect.bsqemit(), enveffect: this.enveffect.bsqemit(), resourceeffect: this.resourceeffect.map((eff) => eff.bsqemit()), tskensures: this.ensures.map((ee) => ee.bsqemit())}];
    }
    static bsqparse(jv: any): TIRTaskType {
        assert(Array.isArray(jv) && jv[0] === "TaskType", "TaskType");
        const rr = new TIRTaskType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, new Map(jv[1].binds), {mkey: jv[1].mainfunc.mkey, mname: jv[1].mainfunc.mname}, {onCanel: jv[1].onfuncs.onCancel || undefined, onFailure: jv[1].onfuncs.onFailure || undefined, onTimeout: jv[1].onfuncs.onTimeout || undefined}, {logStart: jv[1].lfuncs.logStart || undefined, logEnd: jv[1].lfuncs.logEnd || undefined, taskEnsures: jv[1].lfuncs.taskEnsures || undefined, taskWarns: jv[1].lfuncs.taskWarns || undefined});
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        rr.controls.push(...jv[1].controls.map((cc: any) => ({val: cc.val ? TIRLiteralValue.bsqparse(cc.val) : undefined, cname: cc.cname})));
        rr.actions.push(...jv[1].actions);
        rr.statuseffect.statusinfo.push(...TIRTaskStatusEffect.bsqparse(jv[1].statuseffect).statusinfo);
        rr.eventeffect.eventinfo.push(...TIRTaskEventEffect.bsqparse(jv[1].eventeffect).eventinfo);
        rr.enveffect.readvars.push(...TIRTaskEnvironmentEffect.bsqparse(jv[1].enveffect).readvars);
        rr.enveffect.writevars.push(...TIRTaskEnvironmentEffect.bsqparse(jv[1].enveffect).writevars);
        rr.resourceeffect.push(...jv[1].resourceeffect.map((x: any) => TIRTaskResourceEffect.bsqparse(x)));
        rr.ensures.push(...jv[1].tskensures.map((x: any) => TIRTaskEnsures.bsqparse(x)));

        return rr;
    }
}

class TIRConceptType extends TIROOType {
    readonly binds: Map<string, TIRTypeKey>;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], binds: Map<string, TIRTypeKey>, isexportable: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false, isexportable);
        this.binds = binds;
    }

    bsqemit(): any {
        return ["ConceptType", {...this.bsqemit_ootype(), binds: [...this.binds]}];
    }
    static bsqparse(jv: any): TIRConceptType {
        assert(Array.isArray(jv) && jv[0] === "ConceptType", "ConceptType");
        const rr = new TIRConceptType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, new Map(jv[1].binds), jv[1].isexportable);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }

    isAnyConcept(): boolean {
        return this.tkey === "Any";
    }

    isSomeConcept(): boolean {
        return this.tkey === "Some";
    }

    isOptionConcept(): boolean {
        return this.attributes.includes("__option_type");
    }

    isResultConcept(): boolean {
        return this.attributes.includes("__result_type");
    }
}

class TIRConceptSetType extends TIRType {
    readonly conceptTypes: TIRTypeKey[]; //each is a TIRConceptType

    constructor(tkey: TIRTypeKey, concepts: TIRTypeKey[], isexportable: boolean) {
        super(tkey, concepts, isexportable);
        this.conceptTypes = concepts;
    }

    bsqemit(): any {
        return ["ConceptSetType", {...this.bsqemit_type(), conceptTypes: this.conceptTypes}];
    }
    static bsqparse(jv: any): TIRConceptSetType {
        assert(Array.isArray(jv) && jv[0] === "ConceptSetType", "ConceptSetType");
        return new TIRConceptSetType(jv[1].tkey, jv[1].conceptTypes, jv[1].isexportable);
    }
}

class TIRTupleType extends TIRType {
    readonly types: TIRTypeKey[];

    constructor(tkey: TIRTypeKey, types: TIRTypeKey[], supertypes: TIRTypeKey[], isexportable: boolean) {
        super(tkey, supertypes, isexportable);
        this.types = types;
    }

    bsqemit(): any {
        return ["TupleType", {...this.bsqemit_type(), types: this.types}];
    }
    static bsqparse(jv: any): TIRTupleType {
        assert(Array.isArray(jv) && jv[0] === "TupleType", "TupleType");
        return new TIRTupleType(jv[1].tkey, jv[1].types, jv[1].supertypes, jv[1].isexportable);
    }
}

class TIRRecordType extends TIRType {
    readonly entries: {pname: string, ptype: TIRTypeKey}[];

    constructor(tkey: TIRTypeKey, entries: {pname: string, ptype: TIRTypeKey}[], supertypes: TIRTypeKey[], isexportable: boolean) {
        super(tkey, supertypes, isexportable);
        this.entries = entries;
    }

    bsqemit(): any {
        return ["RecordType", {...this.bsqemit_type(), entries: this.entries}];
    }
    static bsqparse(jv: any): TIRRecordType {
        assert(Array.isArray(jv) && jv[0] === "RecordType", "RecordType");
        return new TIRRecordType(jv[1].tkey, jv[1].entries, jv[1].supertypes, jv[1].isexportable);
    }
}

class TIRUnionType extends TIRType {
    readonly options: TIRTypeKey[];

    constructor(tkey: TIRTypeKey, options: TIRTypeKey[], isexportable: boolean) {
        super(tkey, undefined, isexportable);
        this.options = options;
    }

    bsqemit(): any {
        return ["UnionType", {...this.bsqemit_type(), options: this.options}];
    }
    static bsqparse(jv: any): TIRUnionType {
        assert(Array.isArray(jv) && jv[0] === "UnionType", "UnionType");
        return new TIRUnionType(jv[1].tkey, jv[1].options, jv[1].isexportable);
    }
}

class TIREListType extends TIRType {
    readonly types: TIRTypeKey[];

    constructor(tkey: TIRTypeKey, types: TIRTypeKey[]) {
        super(tkey, undefined, false);
        this.types = types;
    }

    bsqemit(): any {
        return ["EListType", {...this.bsqemit_type(), types: this.types}];
    }
    static bsqparse(jv: any): TIREListType {
        assert(Array.isArray(jv) && jv[0] === "EListType", "EListType");
        return new TIREListType(jv[1].tkey, jv[1].types);
    }
}

abstract class TIRNamespaceDecl {
    readonly ns: string;
    readonly name: string;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];

    constructor(ns: string, name: string, srcInfo: SourceInfo, srcFile: string, attributes: string[]) {
        this.ns = ns;
        this.name = name;
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
    }

    bsqemit_nsdecl(): any {
        return {ns: this.ns, name: this.name, sourceLocation: this.sourceLocation, srcFile: this.srcFile, attributes: this.attributes};
    }
}

class TIRNamespaceConstDecl extends TIRNamespaceDecl {
    readonly declaredType: TIRTypeKey;
    readonly value: TIRExpression;

    constructor(ns: string, name: string, srcInfo: SourceInfo, srcFile: string, attributes: string[], declaredtype: TIRTypeKey, value: TIRExpression) {
        super(ns, name, srcInfo, srcFile, attributes);
        this.declaredType = declaredtype;
        this.value = value;
    }

    bsqemit(): any {
        return ["NamespaceConstDecl", {...this.bsqemit_nsdecl(), declaredType: this.declaredType, value: this.value.bsqemit()}];
    }
    static bsqparse(jv: any): TIRNamespaceConstDecl {
        assert(Array.isArray(jv) && jv[0] === "NamespaceConstDecl", "NamespaceConstDecl");
        return new TIRNamespaceConstDecl(jv[1].ns, jv[1].name, jv[1].sourceLocation, jv[1].srcFile, jv[1].attributes, jv[1].declaredType, TIRExpression.bsqparse(jv[1].value));
    }
}

class TIRNamespaceFunctionDecl extends TIRNamespaceDecl {
    readonly ikey: TIRInvokeKey;
    readonly invoke: TIRInvoke;

    constructor(ns: string, sinfo: SourceInfo, srcFile: string, invoke: TIRInvoke) {
        super(ns, invoke.name, sinfo, srcFile, invoke.attributes);
        this.ikey = invoke.invkey;
        this.invoke = invoke;
    }

    bsqemit(): any {
        return ["NamespaceFunctionDecl", {...this.bsqemit_nsdecl(), ikey: this.ikey, invoke: this.invoke.bsqemit()}];
    }

    static bsqparse(jv: any): TIRNamespaceFunctionDecl {
        assert(Array.isArray(jv) && jv[0] === "NamespaceFunctionDecl", "NamespaceFunctionDecl");
        return new TIRNamespaceFunctionDecl(jv[1].ns, jv[1].sourceLocation, jv[1].srcFile, TIRInvoke.bsqparse(jv[1].invoke));
    }
}

class TIRNamespaceOperatorDecl extends TIRNamespaceDecl {
    readonly ikey: TIRInvokeKey;
    readonly invoke: TIRInvoke;

    constructor(ns: string, sinfo: SourceInfo, srcFile: string, invoke: TIRInvoke) {
        super(ns, invoke.name, sinfo, srcFile, invoke.attributes);
        this.ikey = invoke.invkey;
        this.invoke = invoke;
    }

    bsqemit(): any {
        return ["NamespaceOperatorDecl", {...this.bsqemit_nsdecl(), ikey: this.ikey, invoke: this.invoke.bsqemit()}];
    }
    static bsqparse(jv: any): TIRNamespaceOperatorDecl {
        assert(Array.isArray(jv) && jv[0] === "NamespaceOperatorDecl", "NamespaceOperatorDecl");
        return new TIRNamespaceOperatorDecl(jv[1].ns, jv[1].sourceLocation, jv[1].srcFile, TIRInvoke.bsqparse(jv[1].invoke));
    }
}

class TIRNamespaceLambdaDecl {
    readonly ikey: TIRInvokeKey;
    readonly pcid: TIRPCodeKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly invoke: TIRInvoke;

    constructor(pcid: TIRPCodeKey, sinfo: SourceInfo, srcFile: string, invoke: TIRInvoke) {
        this.ikey = invoke.invkey;
        this.pcid = pcid;
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.attributes = invoke.attributes;
        this.invoke = invoke;
    }

    bsqemit(): any {
        return ["NamespaceLambdaDecl", {ikey: this.ikey, pcid: this.pcid, sourceLocation: this.sourceLocation, srcFile: this.srcFile, attributes: this.attributes, invoke: this.invoke.bsqemit()}];
    }
    static bsqparse(jv: any): TIRNamespaceLambdaDecl {
        assert(Array.isArray(jv) && jv[0] === "NamespaceLambdaDecl", "NamespaceLambdaDecl");
        return new TIRNamespaceLambdaDecl(jv[1].pcid, jv[1].sourceLocation, jv[1].srcFile, TIRInvoke.bsqparse(jv[1].invoke));
    }
}

class TIRCodePack {
    readonly ns: string;
    readonly codekey: TIRPCodeKey;
    readonly invk: TIRInvokeKey;
    readonly recursive: boolean;

    readonly terms: TIRTypeKey[]; //Implicit template terms that this is bound with (e.g. if it uses type T from outer scope bound to Int then we need to specialize on whatever T is specialized to)
    readonly pcodes: TIRPCodeKey[]; //Implicit "template" pcode that is bound with this (e.g. if it uses afun from argument to enclosing method we need to specialize on whatever afun is specialized to) 
    
    //Maps from captured variables to their captured values
    readonly capturedValues: {cname: string, ctype: TIRTypeKey}[];
    readonly capturedCodePacks: {cpname: string, cpval: TIRPCodeKey}[];

    constructor(ns: string, codekey: TIRPCodeKey, invk: TIRInvokeKey, recursive: boolean, terms: TIRTypeKey[], pcodes: TIRTypeKey[], capturedValues: {cname: string, ctype: TIRTypeKey}[], capturedCodePacks: {cpname: string, cpval: TIRPCodeKey}[]) {
        this.ns = ns;
        this.codekey = codekey;
        this.invk = invk;
        this.recursive = recursive;
        this.terms = terms;
        this.pcodes = pcodes;
        this.capturedValues = capturedValues;
        this.capturedCodePacks = capturedCodePacks;
    }

    bsqemit(): any {
        return ["CodePack", {ns: this.ns, codekey: this.codekey, invk: this.invk, isrecursive: this.recursive, terms: this.terms, pcodes: this.pcodes, capturedValues: this.capturedValues, capturedCodePacks: this.capturedCodePacks}];
    }
    static bsqparse(jv: any): TIRCodePack {
        assert(Array.isArray(jv) && jv[0] === "CodePack", "CodePack");
        return new TIRCodePack(jv[1].ns, jv[1].codekey, jv[1].invk, jv[1].isrecursive, jv[1].terms, jv[1].pcodes, jv[1].capturedValues, jv[1].capturedCodePacks);
    }
}

abstract class TIRInfoTemplate {
    abstract bsqemit(): any;

    static bsqparse(jv: any): TIRInfoTemplate {
        if(jv[0] === "InfoTemplateRecord") {
            return TIRInfoTemplateRecord.bsqparse(jv);
        }
        else if(jv[0] === "InfoTemplateTuple") {
            return TIRInfoTemplateTuple.bsqparse(jv);
        }
        else if(jv[0] === "InfoTemplateConst") {
            return TIRInfoTemplateConst.bsqparse(jv);
        }
        else if(jv[0] === "InfoTemplateMacro") {
            return TIRInfoTemplateMacro.bsqparse(jv);
        }
        else if(jv[0] === "InfoTemplateValue") {
            return TIRInfoTemplateValue.bsqparse(jv);
        }
        else {
            assert(false, "Unknown info template type: " + jv[0]);
            return (undefined as any) as TIRInfoTemplate;
        }
    }
}

class TIRInfoTemplateRecord extends TIRInfoTemplate {
    readonly entries: { name: string, value: TIRInfoTemplate }[];

    constructor(entries: { name: string, value: TIRInfoTemplate }[]) {
        super();
        this.entries = entries;
    }

    bsqemit(): any {
        return ["InfoTemplateRecord", {entries: this.entries.map((e) => ({name: e.name, value: e.value.bsqemit()}))}];
    }
    static bsqparse(jv: any): TIRInfoTemplateRecord {
        assert(Array.isArray(jv) && jv[0] === "InfoTemplateRecord", "InfoTemplateRecord");
        return new TIRInfoTemplateRecord(jv[1].entries.map((e: any) => ({name: e.name, value: TIRInfoTemplate.bsqparse(e.value)})));
    }
}

class TIRInfoTemplateTuple extends TIRInfoTemplate {
    readonly entries: TIRInfoTemplate[];

    constructor(entries: TIRInfoTemplate[]) {
        super();
        this.entries = entries;
    }

    bsqemit(): any {
        return ["InfoTemplateTuple", {entries: this.entries.map((e) => e.bsqemit())}];
    }
    static bsqparse(jv: any): TIRInfoTemplateTuple {
        assert(Array.isArray(jv) && jv[0] === "InfoTemplateTuple", "InfoTemplateTuple");
        return new TIRInfoTemplateTuple(jv[1].entries.map((e: any) => TIRInfoTemplate.bsqparse(e)));
    }
}

class TIRInfoTemplateConst extends TIRInfoTemplate {
    readonly litexp: TIRLiteralValue;

    constructor(litexp: TIRLiteralValue) {
        super();
        this.litexp = litexp;
    }

    bsqemit(): any {
        return ["InfoTemplateConst", {litexp: this.litexp.bsqemit()}];
    }
    static bsqparse(jv: any): TIRInfoTemplateConst {
        assert(Array.isArray(jv) && jv[0] === "InfoTemplateConst", "InfoTemplateConst");
        return new TIRInfoTemplateConst(TIRLiteralValue.bsqparse(jv[1].litexp));
    }
}

class TIRInfoTemplateMacro extends TIRInfoTemplate {
    readonly macro: string;

    constructor(macro: string) {
        super();
        this.macro = macro;
    }

    bsqemit(): any {
        return ["InfoTemplateMacro", {macro: this.macro}];
    }
    static bsqparse(jv: any): TIRInfoTemplateMacro {
        assert(Array.isArray(jv) && jv[0] === "InfoTemplateMacro", "InfoTemplateMacro");
        return new TIRInfoTemplateMacro(jv[1].macro);
    }
}

class TIRInfoTemplateValue extends TIRInfoTemplate {
    readonly argpos: number;
    readonly argtype: TIRTypeKey;

    constructor(argpos: number, argtype: TIRTypeKey) {
        super();
        this.argpos = argpos;
        this.argtype = argtype;
    }

    bsqemit(): any {
        return ["InfoTemplateValue", {argpos: this.argpos, argtype: this.argtype}];
    }
    static bsqparse(jv: any): TIRInfoTemplateValue {
        assert(Array.isArray(jv) && jv[0] === "InfoTemplateValue", "InfoTemplateValue");
        return new TIRInfoTemplateValue(jv[1].argpos, jv[1].argtype);
    }
}

class TIRStringTemplate {
    readonly str: string;

    //
    //TODO: want to pre-process this for formats and such
    //

    constructor(str: string) {
        this.str = str;
    }

    bsqemit(): any {
        return ["StringTemplate", {str: this.str}];
    }
    static bsqparse(jv: any): TIRStringTemplate {
        assert(Array.isArray(jv) && jv[0] === "StringTemplate", "StringTemplate");
        return new TIRStringTemplate(jv[1].str);
    }
}

class TIRNamespaceDeclaration {
    readonly ns: string;

    consts: Map<string, TIRNamespaceConstDecl>;
    functions: Map<string, TIRNamespaceFunctionDecl[]>;
    operators: Map<string, TIRNamespaceOperatorDecl[]>;
    concepts: Map<string, TIRTypeKey[]>;
    objects: Map<string, TIRTypeKey[]>;
    
    tasks: Map<string, TIRTypeKey>;

    lambdas: Map<TIRInvokeKey, TIRNamespaceLambdaDecl>;
    codepacks: Map<TIRPCodeKey, TIRCodePack>;

    msgformats: Map<string, TIRInfoTemplate>;
    stringformats: Map<string, TIRStringTemplate>;

    constructor(ns: string) {
        this.ns = ns;
        this.consts = new Map<string, TIRNamespaceConstDecl>();
        this.functions = new Map<string, TIRNamespaceFunctionDecl[]>();
        this.operators = new Map<string, TIRNamespaceOperatorDecl[]>();
        this.concepts = new Map<string, TIRTypeKey[]>();
        this.objects = new Map<string, TIRTypeKey[]>();

        this.tasks = new Map<string, TIRTypeKey>();

        this.lambdas = new Map<TIRInvokeKey, TIRNamespaceLambdaDecl>();
        this.codepacks = new Map<TIRPCodeKey, TIRCodePack>();

        this.msgformats = new Map<string, TIRInfoTemplate>();
        this.stringformats = new Map<string, TIRStringTemplate>();
    }

    bsqemit(): any {
        return ["NamespaceDeclaration", {
            ns: this.ns,
            consts: [...this.consts.entries()].map((e) => ({name: e[0], value: e[1].bsqemit()})),
            functions: [...this.functions.entries()].map((e) => ({name: e[0], value: e[1].map((f) => f.bsqemit())})),
            operators: [...this.operators.entries()].map((e) => ({name: e[0], value: e[1].map((f) => f.bsqemit())})),
            concepts: [...this.concepts.entries()].map((e) => ({name: e[0], value: e[1]})),
            objects: [...this.objects.entries()].map((e) => ({name: e[0], value: e[1]})),
            tasks: [...this.tasks.entries()].map((e) => ({name: e[0], value: e[1]})),
            lambdas: [...this.lambdas.entries()].map((e) => ({name: e[0], value: e[1].bsqemit()})),
            codepacks: [...this.codepacks.entries()].map((e) => ({name: e[0], value: e[1].bsqemit()})),
            msgformats: [...this.msgformats.entries()].map((e) => ({name: e[0], value: e[1].bsqemit()})),
            stringformats: [...this.stringformats.entries()].map((e) => ({name: e[0], value: e[1].bsqemit()}))
        }];
    }
    static bsqparse(jv: any): TIRNamespaceDeclaration {
        assert(Array.isArray(jv) && jv[0] === "NamespaceDeclaration", "NamespaceDeclaration");
        const ns = new TIRNamespaceDeclaration(jv[1].ns);
        jv[1].consts.forEach((e: any) => ns.consts.set(e.name, TIRNamespaceConstDecl.bsqparse(e.value)));
        jv[1].functions.forEach((e: any) => ns.functions.set(e.name, e.value.map((f: any) => TIRNamespaceFunctionDecl.bsqparse(f))));
        jv[1].operators.forEach((e: any) => ns.operators.set(e.name, e.value.map((f: any) => TIRNamespaceOperatorDecl.bsqparse(f))));
        jv[1].concepts.forEach((e: any) => ns.concepts.set(e.name, e.value));
        jv[1].objects.forEach((e: any) => ns.objects.set(e.name, e.value));
        jv[1].tasks.forEach((e: any) => ns.tasks.set(e.name, e.value));
        jv[1].lambdas.forEach((e: any) => ns.lambdas.set(e.name, TIRNamespaceLambdaDecl.bsqparse(e.value)));
        jv[1].codepacks.forEach((e: any) => ns.codepacks.set(e.name, TIRCodePack.bsqparse(e.value)));
        jv[1].msgformats.forEach((e: any) => ns.msgformats.set(e.name, TIRInfoTemplate.bsqparse(e.value)));
        jv[1].stringformats.forEach((e: any) => ns.stringformats.set(e.name, TIRStringTemplate.bsqparse(e.value)));
        return ns;
    }
}

class TIRAssembly {
    readonly namespaceMap: Map<string, TIRNamespaceDeclaration>;
    readonly typeMap: Map<TIRTypeKey, TIRType>;
    readonly fieldMap: Map<TIRTypeKey, TIRMemberFieldDecl>;
    readonly invokeMap: Map<TIRTypeKey, TIRInvoke>;
    readonly pcodemap: Map<TIRPCodeKey, TIRCodePack>;

    readonly literalRegexs: BSQRegex[];
    readonly validatorRegexs: Map<string, BSQRegex>;
    readonly validatorPaths: Map<string, PathValidator>;

    getNamespace(ns: string): TIRNamespaceDeclaration {
        assert(this.namespaceMap.has(ns), "Missing namespace?");
        return this.namespaceMap.get(ns) as TIRNamespaceDeclaration;
    }

    getTypeAs<T extends TIRType>(tkey: TIRTypeKey): T {
        assert(this.typeMap.has(tkey), "Missing type");
        return this.typeMap.get(tkey) as T;
    }

    constructor(namespaceMap: Map<string, TIRNamespaceDeclaration>, typeMap: Map<TIRTypeKey, TIRType>, fieldMap: Map<TIRTypeKey, TIRMemberFieldDecl>, invokeMap: Map<TIRTypeKey, TIRInvoke>, pcodemap: Map<TIRPCodeKey, TIRCodePack>, literalRegexs: BSQRegex[], validatorRegexs: Map<string, BSQRegex>, validatorPaths: Map<string, PathValidator>) {
        this.namespaceMap = namespaceMap;
        this.typeMap = typeMap;
        this.fieldMap = fieldMap;
        this.invokeMap = invokeMap;
        this.pcodemap = pcodemap;
        this.literalRegexs = literalRegexs;
        this.validatorRegexs = validatorRegexs;
        this.validatorPaths = validatorPaths;
    }

    bsqemit(): any {
        return ["Assembly", {
            namespaceMap: [...this.namespaceMap.entries()].map((e) => ({name: e[0], value: e[1].bsqemit()})),
            typeMap: [...this.typeMap.entries()].map((e) => ({name: e[0], value: e[1].bsqemit()})),
            fieldMap: [...this.fieldMap.entries()].map((e) => ({name: e[0], value: e[1].bsqemit()})),
            invokeMap: [...this.invokeMap.entries()].map((e) => ({name: e[0], value: e[1].bsqemit()})),
            pcodemap: [...this.pcodemap.entries()].map((e) => ({name: e[0], value: e[1].bsqemit()})),
            literalRegexs: this.literalRegexs.map((r) => r.jemit()),
            validatorRegexs: [...this.validatorRegexs.entries()].map((e) => ({name: e[0], value: e[1].jemit()})),
            validatorPaths: [...this.validatorPaths.entries()].map((e) => ({name: e[0], value: e[1].jemit()}))
        }];
    }
    static bsqparse(jv: any): TIRAssembly {
        assert(Array.isArray(jv) && jv[0] === "Assembly", "Assembly");
        const nsmap = new Map<string, TIRNamespaceDeclaration>();
        jv[1].namespaceMap.forEach((e: any) => nsmap.set(e.name, TIRNamespaceDeclaration.bsqparse(e.value)));

        const typemap = new Map<TIRTypeKey, TIRType>();
        jv[1].typeMap.forEach((e: any) => typemap.set(e.name, TIRType.bsqparse(e.value)));

        const fieldmap = new Map<TIRTypeKey, TIRMemberFieldDecl>();
        jv[1].fieldMap.forEach((e: any) => fieldmap.set(e.name, TIRMemberFieldDecl.bsqparse(e.value)));

        const invokemap = new Map<TIRTypeKey, TIRInvoke>();
        jv[1].invokeMap.forEach((e: any) => invokemap.set(e.name, TIRInvoke.bsqparse(e.value)));

        const pcodemap = new Map<TIRPCodeKey, TIRCodePack>();
        jv[1].pcodemap.forEach((e: any) => pcodemap.set(e.name, TIRCodePack.bsqparse(e.value)));

        const literalRegexs = jv[1].literalRegexs.map((r: any) => BSQRegex.jparse(r));

        const validatorRegexs = new Map<string, BSQRegex>();
        jv[1].validatorRegexs.forEach((e: any) => validatorRegexs.set(e.name, BSQRegex.jparse(e.value)));
        
        const validatorPaths = new Map<string, PathValidator>();
        jv[1].validatorPaths.forEach((e: any) => validatorPaths.set(e.name, PathValidator.jparse(e.value)));
        
        return new TIRAssembly(nsmap, typemap, fieldmap, invokemap, pcodemap, literalRegexs, validatorRegexs, validatorPaths);
    }
}

export {
    TIRTypeName,
    TIRTypeKey, TIRInvokeKey, TIRFieldKey, TIRPCodeKey,
    TIRFunctionParameter,
    TIRObjectInvariantDecl, TIRObjectValidateDecl, TIRTypedeclInvariantDecl, TIRTypedeclValidateDecl,
    TIRTaskStatusEffect, TIRTaskEventEffect, TIRTaskEnvironmentEffect, TIRTaskResourceEffect, TIRTaskEnsures,
    TIRInvoke, TIRPreConditionDecl, TIRPostConditionDecl, TIRInvokeAbstractDeclaration, TIRInvokeImplementation, TIRInvokePrimitive,
    TIRConstMemberDecl, TIRStaticFunctionDecl, TIRMemberFieldDecl, TIRMemberMethodDecl,
    TIRType,
    TIROOType, TIREntityType, TIRObjectEntityType, TIREnumEntityType, TIRTypedeclEntityType, TIRInternalEntityType, TIRPrimitiveInternalEntityType,
    TIRValidatorEntityType, TIRStringOfEntityType, TIRASCIIStringOfEntityType,
    TIRPathValidatorEntityType, TIRPathEntityType, TIRPathFragmentEntityType, TIRPathGlobEntityType,
    TIRConstructableEntityType, TIROkEntityType, TIRErrEntityType, TIRSomethingEntityType, TIRMapEntryEntityType,
    TIRHavocEntityType,
    TIRPrimitiveCollectionEntityType, TIRListEntityType, TIRStackEntityType, TIRQueueEntityType, TIRSetEntityType, TIRMapEntityType,
    TIRTaskType,
    TIRConceptType, TIRConceptSetType,
    TIRTupleType, TIRRecordType,
    TIREListType,
    TIRUnionType,
    TIRInfoTemplate, TIRInfoTemplateRecord, TIRInfoTemplateTuple, TIRInfoTemplateConst, TIRInfoTemplateMacro, TIRInfoTemplateValue,
    TIRStringTemplate,
    TIRNamespaceConstDecl, TIRNamespaceFunctionDecl, TIRNamespaceOperatorDecl, TIRNamespaceLambdaDecl,
    TIRNamespaceDeclaration,
    TIRCodePack,
    TIRAssembly
};
