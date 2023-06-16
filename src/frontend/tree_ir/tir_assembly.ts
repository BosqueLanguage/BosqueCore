
import { TIRExpression, TIRLiteralValue, TIRStatement } from "./tir_body";

import { SourceInfo } from "../build_decls";
import { BSQRegex } from "../bsqregex";
import { BSQPathValidator } from "../path_validator";
import * as TypeInfo from "./typeinfo";

function assert(cond: boolean, msg: string) {
    if (!cond) {
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
        return { ns: this.ns, name: this.name, templates: this.templates };
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
        return { name: this.name, type: this.type, ddlit: this.ddlit !== undefined ? this.ddlit.bsqemit() : null };
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
        return { exp: this.exp.bsqemit(), args: this.args.map((arg) => arg.bsqemit()) };
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
        return { exp: this.exp.bsqemit(), args: this.args.map((arg) => arg.bsqemit()) };
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
        return { exp: this.exp.bsqemit(), args: this.args.map((arg) => arg.bsqemit()) };
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
        return { exp: this.exp.bsqemit(), args: this.args.map((arg) => arg.bsqemit()) };
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
        return { exp: this.exp.bsqemit(), vtype: this.vtype };
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
        return { exp: this.exp.bsqemit(), vtype: this.vtype };
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
        return { statusinfo: this.statusinfo };
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
        return { eventinfo: this.eventinfo };
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
        return { readvars: this.readvars, writevars: this.writevars };
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

    constructor(pathdescriptor: TIRTypeKey, isread: boolean, iswrite: boolean, pathglob: TIRExpression | undefined, args: TIRFunctionParameter[]) {
        this.pathdescriptor = pathdescriptor;
        this.isread = isread;
        this.iswrite = iswrite;

        this.pathglob = pathglob;
        this.args = args;
    }

    bsqemit(): any {
        return { pathdescriptor: this.pathdescriptor, isread: this.isread, iswrite: this.iswrite, pathglob: this.pathglob !== undefined ? this.pathglob.bsqemit() : null, args: this.args.map((arg) => arg.bsqemit()) };
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
        return { sinfo: this.sinfo.bsqemit(), exp: this.exp.bsqemit(), args: this.args.map((arg) => arg.bsqemit()) };
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
        return { invkey: this.invkey, name: this.name, sinfoStart: this.startSourceLocation.bsqemit(), sinfoEnd: this.endSourceLocation.bsqemit(), srcFile: this.srcFile, attributes: this.attributes, isrecursive: this.isrecursive, tbinds: Array.from(this.tbinds.entries()), pcodes: Array.from(this.pcodes.entries()), isMemberMethod: this.isMemberMethod, isVirtual: this.isVirtual, isDynamicOperator: this.isDynamicOperator, isLambda: this.isLambda, params: this.params.map((param) => param.bsqemit()), isThisRef: this.isThisRef, resultType: this.resultType, preconditions: this.preconditions.map((precond) => precond.bsqemit()), postconditions: this.postconditions.map((postcond) => postcond.bsqemit()) };
    }

    abstract bsqemit(): any;

    static bsqparse(jv: any): TIRInvoke {
        if (jv[0] === "TreeIR::InvokeAbstractDeclaration") {
            return TIRInvokeAbstractDeclaration.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::InvokeImplementation") {
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
        return ["TreeIR::InvokeAbstractDeclaration", this.bsqemit_inv()];
    }
    static bsqparse(jv: any): TIRInvokeAbstractDeclaration {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::InvokeAbstractDeclaration", "InvokeAbstractDeclaration");

        jv = jv[1];
        return new TIRInvokeAbstractDeclaration(jv.invkey, jv.name, SourceInfo.bsqparse(jv.sinfoStart), SourceInfo.bsqparse(jv.sinfoEnd), jv.srcFile, jv.attributes, jv.isrecursive, new Map<string, TIRTypeKey>(jv.tbinds), new Map<string, TIRPCodeKey>(jv.pcodes), jv.isMemberMethod, jv.isDynamicOperator, jv.params.map((param: any) => TIRFunctionParameter.bsqparse(param)), jv.isThisRef, jv.resultType, jv.preconditions.map((precond: any) => TIRPreConditionDecl.bsqparse(precond)), jv.postconditions.map((postcond: any) => TIRPostConditionDecl.bsqparse(postcond)));
    }
}

class TIRInvokeImplementation extends TIRInvoke {
    readonly body: TIRStatement[];

    constructor(invkey: TIRInvokeKey, name: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: string[], recursive: boolean, tbinds: Map<string, TIRTypeKey>, pcodes: Map<string, TIRPCodeKey>, isMemberMethod: boolean, isVirtual: boolean, isDynamicOperator: boolean, isLambda: boolean, params: TIRFunctionParameter[], isThisRef: boolean, resultType: TIRTypeKey, preconds: TIRPreConditionDecl[], postconds: TIRPostConditionDecl[], body: TIRStatement[]) {
        super(invkey, name, sinfoStart, sinfoEnd, srcFile, attributes, recursive, tbinds, pcodes, isMemberMethod, isVirtual, isDynamicOperator, isLambda, params, isThisRef, resultType, preconds, postconds);

        this.body = body;
    }

    bsqemit(): any {
        return ["TreeIR::InvokeImplementation", { ...this.bsqemit_inv(), body: this.body.map((stmt) => stmt.bsqemit()) }];
    }
    static bsqparse(jv: any): TIRInvokeImplementation {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::InvokeImplementation", "InvokeImplementation");

        jv = jv[1];
        const body = jv.body.map((stmt: any) => TIRStatement.bsqparse(stmt));
        return new TIRInvokeImplementation(jv.invkey, jv.name, SourceInfo.bsqparse(jv.sinfoStart), SourceInfo.bsqparse(jv.sinfoEnd), jv.srcFile, jv.attributes, jv.isrecursive, new Map<string, TIRTypeKey>(jv.tbinds), new Map<string, TIRPCodeKey>(jv.pcodes), jv.isMemberMethod, jv.isVirtual, jv.isDynamicOperator, jv.isLambda, jv.params.map((param: any) => TIRFunctionParameter.bsqparse(param)), jv.isThisRef, jv.resultType, jv.preconditions.map((precond: any) => TIRPreConditionDecl.bsqparse(precond)), jv.postconditions.map((postcond: any) => TIRPostConditionDecl.bsqparse(postcond)), body);
    }
}

class TIRInvokePrimitive extends TIRInvoke {
    readonly body: string;

    constructor(invkey: TIRInvokeKey, name: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: string[], recursive: boolean, tbinds: Map<string, TIRTypeKey>, pcodes: Map<string, TIRPCodeKey>, params: TIRFunctionParameter[], resultType: TIRTypeKey, body: string) {
        super(invkey, name, sinfoStart, sinfoEnd, srcFile, attributes, recursive, tbinds, pcodes, false, false, false, false, params, false, resultType, [], []);

        this.body = body;
    }

    bsqemit(): any {
        return ["TreeIR::InvokePrimitive", { ...this.bsqemit_inv(), body: this.body }];
    }
    static bsqparse(jv: any): TIRInvokePrimitive {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::InvokePrimitive", "InvokePrimitive");

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
        return { tkey: this.tkey, name: this.name, sinfo: this.sourceLocation.bsqemit(), srcFile: this.srcFile, attributes: this.attributes };
    }

    abstract bsqemit(): any;

    static bsqparse(jv: any): TIRMemberDecl {
        if (jv[0] === "TreeIR::ConstMemberDecl") {
            return TIRConstMemberDecl.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::StaticFunctionDecl") {
            return TIRStaticFunctionDecl.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::MemberFieldDecl") {
            return TIRMemberFieldDecl.bsqparse(jv);
        }
        else {
            assert(jv[0] === "TreeIR::MemberMethodDecl", "MemberMethodDecl");

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
        return ["TreeIR::ConstMemberDecl", { ...this.bsqemit_decl(), declaredType: this.declaredType, value: this.value.bsqemit() }];
    }
    static bsqparse(jv: any): TIRConstMemberDecl {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::ConstMemberDecl", "ConstMemberDecl");

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
        return ["TreeIR::StaticFunctionDecl", { ...this.bsqemit_decl(), ikey: this.ikey, invoke: this.invoke.bsqemit() }];
    }
    static bsqparse(jv: any): TIRStaticFunctionDecl {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::StaticFunctionDecl", "StaticFunctionDecl");

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
        return ["TreeIR::MemberFieldDecl", { ...this.bsqemit_decl(), fkey: this.fkey, declaredType: this.declaredType }];
    }
    static bsqparse(jv: any): TIRMemberFieldDecl {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::MemberFieldDecl", "MemberFieldDecl");

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
        return ["TreeIR::MemberMethodDecl", { ...this.bsqemit_decl(), ikey: this.ikey, invoke: this.invoke.bsqemit() }];
    }
    static bsqparse(jv: any): TIRMemberMethodDecl {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::MemberMethodDecl", "MemberMethodDecl");

        jv = jv[1];
        return new TIRMemberMethodDecl(jv.tkey, SourceInfo.bsqparse(jv.sinfo), jv.srcFile, TIRInvoke.bsqparse(jv.invoke));
    }
}

abstract class TIRType {
    readonly tkey: TIRTypeKey;

    //direct suprertypes -- not saturated set
    readonly supertypes: Set<TIRTypeKey> | undefined;

    constructor(tkey: TIRTypeKey, supertypes: TIRTypeKey[] | undefined) {
        this.tkey = tkey;
        this.supertypes = supertypes !== undefined ? new Set<TIRTypeKey>(supertypes) : undefined;
    }

    bsqemit_type(): any {
        return { tkey: this.tkey, supertypes: this.supertypes !== undefined ? [...this.supertypes] : null };
    }

    abstract bsqemit(): any;

    static bsqparse(jv: any): TIRType {
        if (jv[0] === "TreeIR::ObjectEntityType") {
            return TIRObjectEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::EnumEntityType") {
            return TIREnumEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::TypedeclEntityType") {
            return TIRTypedeclEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::PrimitiveInternalEntityType") {
            return TIRPrimitiveInternalEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::ValidatorEntityType") {
            return TIRValidatorEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::StringOfEntityType") {
            return TIRStringOfEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::ASCIIStringOfEntityType") {
            return TIRASCIIStringOfEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::PathValidatorEntityType") {
            return TIRPathValidatorEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::PathEntityType") {
            return TIRPathEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::PathFragmentEntityType") {
            return TIRPathFragmentEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::PathGlobEntityType") {
            return TIRPathGlobEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::OkEntityType") {
            return TIROkEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::ErrEntityType") {
            return TIRErrEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::SomethingEntityType") {
            return TIRSomethingEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::MapEntryEntityType") {
            return TIRMapEntryEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::HavocEntityType") {
            return TIRHavocEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::ListEntityType") {
            return TIRListEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::StackEntityType") {
            return TIRStackEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::QueueEntityType") {
            return TIRQueueEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::SetEntityType") {
            return TIRSetEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::MapEntityType") {
            return TIRMapEntityType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::TaskType") {
            return TIRTaskType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::ConceptType") {
            return TIRConceptType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::ConceptSetType") {
            return TIRConceptSetType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::TupleType") {
            return TIRTupleType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::RecordType") {
            return TIRRecordType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::UnionType") {
            return TIRUnionType.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::EListType") {
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

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], iskeytype: boolean) {
        super(tkey, supertypes);
        this.tname = tname;
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.iskeytype = iskeytype;
    }

    bsqemit_ootype(): any {
        return { ...this.bsqemit_type(), tname: this.tname, sinfo: this.sourceLocation.bsqemit(), srcFile: this.srcFile, attributes: this.attributes, constMembers: this.constMembers.map((x) => x.bsqemit()), staticFunctions: this.staticFunctions.map((x) => x.bsqemit()), memberFields: this.memberFields.map((x) => x.bsqemit()), memberMethods: this.memberMethods.map((x) => x.bsqemit()), iskeytype: this.iskeytype };
    }
    static bsqparse_ooinfo(jv: any, tt: TIROOType) {
        tt.constMembers.push(...jv.constMembers.map((x: any) => TIRConstMemberDecl.bsqparse(x)));
        tt.staticFunctions.push(...jv.staticFunctions.map((x: any) => TIRStaticFunctionDecl.bsqparse(x)));
        tt.memberFields.push(...jv.memberFields.map((x: any) => TIRMemberFieldDecl.bsqparse(x)));
        tt.memberMethods.push(...jv.memberMethods.map((x: any) => TIRMemberMethodDecl.bsqparse(x)));
    }
}

abstract class TIREntityType extends TIROOType {
    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], iskeytype: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, iskeytype);
    }

    bsqemit_entitytype(): any {
        return { ...this.bsqemit_ootype() };
    }
}

//Represents types declared as entities in the code
class TIRObjectEntityType extends TIREntityType {
    readonly allfields: { fkey: TIRFieldKey, ftype: TIRTypeKey }[] = [];

    readonly consinvariants: TIRObjectInvariantDecl[] = [];
    readonly apivalidates: TIRObjectValidateDecl[] = [];

    readonly vtable: Map<string, TIRInvokeKey> = new Map<string, TIRInvokeKey>();
    readonly binds: Map<string, TIRTypeKey>;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], binds: Map<string, TIRTypeKey>) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false);
        this.binds = binds;
    }

    bsqemit(): any {
        return ["TreeIR::ObjectEntityType", { ...this.bsqemit_entitytype(), allfields: this.allfields, consinvariants: this.consinvariants.map((x) => x.bsqemit()), apivalidates: this.apivalidates.map((x) => x.bsqemit()), vtable: [...this.vtable], binds: [...this.binds] }];
    }
    static bsqparse(jv: any): TIRObjectEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::ObjectEntityType", "ObjectEntityType");

        jv = jv[1];
        const rr = new TIRObjectEntityType(jv.tkey, jv.tname, SourceInfo.bsqparse(jv.sinfo), jv.srcFile, jv.attributes, jv.supertypes, new Map<string, TIRTypeKey>(jv.binds));
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
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, true);
        this.enums = enums;
    }

    bsqemit(): any {
        return ["TreeIR::EnumEntityType", { ...this.bsqemit_entitytype(), enums: this.enums, litvals: [...this.litvals].map((x) => [x[0], x[1].bsqemit()]) }];
    }
    static bsqparse(jv: any): TIREnumEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::EnumEntityType", "EnumEntityType");

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

    readonly strvalidator: { vtype: TIRTypeKey, vre: BSQRegex } | undefined; //TIRValidatorEntityType;
    readonly pthvalidator: { vtype: TIRTypeKey, vpth: BSQPathValidator, kind: "path" | "pathfragment" | "pathglob" } | undefined; //TIRPathValidatorEntityType;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], valuetype: TIRTypeKey, representation: TIRTypeKey, strvalidator: { vtype: TIRTypeKey, vre: BSQRegex } | undefined, pthvalidator: { vtype: TIRTypeKey, vpth: BSQPathValidator, kind: "path" | "pathfragment" | "pathglob" } | undefined, iskeytype: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, iskeytype);
        this.valuetype = valuetype;
        this.representation = representation;
        this.strvalidator = strvalidator;
        this.pthvalidator = pthvalidator;
    }

    bsqemit(): any {
        return ["TreeIR::TypedeclEntityType", {
            ...this.bsqemit_entitytype(), valuetype: this.valuetype, representation: this.representation, consinvariantsall: this.consinvariantsall.map((x) => x.bsqemit()), consinvariantsexplicit: this.consinvariantsexplicit.map((x) => x.bsqemit()), apivalidates: this.apivalidates.map((x) => x.bsqemit()),
            strvalidator: this.strvalidator !== undefined ? { vtype: this.strvalidator.vtype, vre: this.strvalidator.vre.jemit() } : null,
            pthvalidator: this.pthvalidator !== undefined ? { vtype: this.pthvalidator, vpth: this.pthvalidator.vpth.jemit(), kind: this.pthvalidator.kind } : null
        }];
    }
    static bsqparse(jv: any): TIRTypedeclEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::TypedeclEntityType", "TypedeclEntityType");

        jv = jv[1];
        const rr = new TIRTypedeclEntityType(jv.tkey, jv.tname, SourceInfo.bsqparse(jv.sinfo), jv.srcFile, jv.attributes, jv.supertypes, jv.valuetype, jv.representation, jv.strvalidator !== null ? { vtype: jv.strvalidator.vtype, vre: BSQRegex.jparse(jv.strvalidator.vre) } : undefined, jv.pthvalidator !== null ? { vtype: jv.pthvalidator.vtype, vpth: BSQPathValidator.jparse(jv.pthvalidator.vpth), kind: jv.pthvalidator.kind } : undefined, jv.iskeytype);
        TIROOType.bsqparse_ooinfo(jv, rr);

        rr.consinvariantsall.push(...jv.consinvariantsall.map((x: any) => TIRTypedeclInvariantDecl.bsqparse(x)));
        rr.consinvariantsexplicit.push(...jv.consinvariantsexplicit.map((x: any) => TIRTypedeclInvariantDecl.bsqparse(x)));
        rr.apivalidates.push(...jv.apivalidates.map((x: any) => TIRTypedeclValidateDecl.bsqparse(x)));

        return rr;
    }
}

//base class for all the primitive types that are defined
abstract class TIRInternalEntityType extends TIREntityType {
    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], iskeytype: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, iskeytype);
    }

    bsqemit_internalentity(): any {
        return { ...this.bsqemit_entitytype() };
    }
}

//class representing all the primitive values (Int, Bool, String, ...). All of these are special implemented values
class TIRPrimitiveInternalEntityType extends TIRInternalEntityType {
    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], iskeytype: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, iskeytype);
    }

    bsqemit(): any {
        return ["TreeIR::PrimitiveInternalEntityType", this.bsqemit_internalentity()];
    }
    static bsqparse(jv: any): TIRPrimitiveInternalEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::PrimitiveInternalEntityType", "PrimitiveInternalEntityType");
        const rr = new TIRPrimitiveInternalEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].iskeytype);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing Validator regex types
class TIRValidatorEntityType extends TIRInternalEntityType {
    readonly revalidator: BSQRegex;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], revalidator: BSQRegex) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false);
        this.revalidator = revalidator;
    }

    bsqemit(): any {
        return ["TreeIR::ValidatorEntityType", { ...this.bsqemit_internalentity(), revalidator: this.revalidator.jemit() }];
    }
    static bsqparse(jv: any): TIRValidatorEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::ValidatorEntityType", "ValidatorEntityType");
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
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, true);
        this.validatortype = validatortype;
        this.revalidator = revalidator;
    }

    bsqemit(): any {
        return ["TreeIR::StringOfEntityType", { ...this.bsqemit_internalentity(), validatortype: this.validatortype, revalidator: this.revalidator.jemit() }];
    }
    static bsqparse(jv: any): TIRStringOfEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::StringOfEntityType", "StringOfEntityType");
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
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, true);
        this.validatortype = validatortype;
        this.revalidator = revalidator;
    }

    bsqemit(): any {
        return ["TreeIR::ASCIIStringOfEntityType", { ...this.bsqemit_internalentity(), validatortype: this.validatortype, revalidator: this.revalidator.jemit() }];
    }
    static bsqparse(jv: any): TIRASCIIStringOfEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::ASCIIStringOfEntityType", "ASCIIStringOfEntityType");
        const rr = new TIRASCIIStringOfEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].validatortype, BSQRegex.jparse(jv[1].revalidator));
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing PathValidator types
class TIRPathValidatorEntityType extends TIRInternalEntityType {
    readonly pthvalidator: BSQPathValidator;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], pthvalidator: BSQPathValidator) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false);
        this.pthvalidator = pthvalidator;
    }

    bsqemit(): any {
        return ["TreeIR::PathValidatorEntityType", { ...this.bsqemit_internalentity(), pthvalidator: this.pthvalidator.jemit() }];
    }
    static bsqparse(jv: any): TIRPathValidatorEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::PathValidatorEntityType", "PathValidatorEntityType");
        const rr = new TIRPathValidatorEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, BSQPathValidator.jparse(jv[1].pthvalidator));
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing a Path<T> type
class TIRPathEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey //TIRPathValidatorEntityType;
    readonly pthvalidator: BSQPathValidator;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], validatortype: TIRTypeKey, pthvalidator: BSQPathValidator) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, true);
        this.validatortype = validatortype;
        this.pthvalidator = pthvalidator;
    }

    bsqemit(): any {
        return ["TreeIR::PathEntityType", { ...this.bsqemit_internalentity(), validatortype: this.validatortype, pthvalidator: this.pthvalidator.jemit() }];
    }
    static bsqparse(jv: any): TIRPathEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::PathEntityType", "PathEntityType");
        const rr = new TIRPathEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].validatortype, BSQPathValidator.jparse(jv[1].pthvalidator));
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing a PathFragment<T> type
class TIRPathFragmentEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey //TIRPathValidatorEntityType;
    readonly pthvalidator: BSQPathValidator;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], validatortype: TIRTypeKey, pthvalidator: BSQPathValidator) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, true);
        this.validatortype = validatortype;
        this.pthvalidator = pthvalidator;
    }

    bsqemit(): any {
        return ["TreeIR::PathFragmentEntityType", { ...this.bsqemit_internalentity(), validatortype: this.validatortype, pthvalidator: this.pthvalidator.jemit() }];
    }
    static bsqparse(jv: any): TIRPathFragmentEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::PathFragmentEntityType", "PathFragmentEntityType");
        const rr = new TIRPathFragmentEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].validatortype, BSQPathValidator.jparse(jv[1].pthvalidator));
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

class TIRPathGlobEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey //TIRPathValidatorEntityType;
    readonly pthvalidator: BSQPathValidator;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], validatortype: TIRTypeKey, pthvalidator: BSQPathValidator) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, true);
        this.validatortype = validatortype;
        this.pthvalidator = pthvalidator;
    }

    bsqemit(): any {
        return ["TreeIR::PathGlobEntityType", { ...this.bsqemit_internalentity(), validatortype: this.validatortype, pthvalidator: this.pthvalidator.jemit() }];
    }
    static bsqparse(jv: any): TIRPathGlobEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::PathGlobEntityType", "PathGlobEntityType");
        const rr = new TIRPathGlobEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].validatortype, BSQPathValidator.jparse(jv[1].pthvalidator));
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing Ok, Err, Something types
abstract class TIRConstructableEntityType extends TIRInternalEntityType {
    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[]) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false);
    }

    bsqemit_constructable(): any {
        return this.bsqemit_internalentity();
    }
}

class TIROkEntityType extends TIRConstructableEntityType {
    readonly typeT: TIRTypeKey;
    readonly typeE: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey, typeE: TIRTypeKey) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes);
        this.typeT = typeT;
        this.typeE = typeE;
    }

    bsqemit(): any {
        return ["TreeIR::OkEntityType", { ...this.bsqemit_constructable(), typeT: this.typeT, typeE: this.typeE }];
    }
    static bsqparse(jv: any): TIROkEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::OkEntityType", "OkEntityType");
        const rr = new TIROkEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeT, jv[1].typeE);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

class TIRErrEntityType extends TIRConstructableEntityType {
    readonly typeT: TIRTypeKey;
    readonly typeE: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey, typeE: TIRTypeKey) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes);
        this.typeT = typeT;
        this.typeE = typeE;
    }

    bsqemit(): any {
        return ["TreeIR::ErrEntityType", { ...this.bsqemit_constructable(), typeT: this.typeT, typeE: this.typeE }];
    }
    static bsqparse(jv: any): TIRErrEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::ErrEntityType", "ErrEntityType");
        const rr = new TIRErrEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeT, jv[1].typeE);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

class TIRSomethingEntityType extends TIRConstructableEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes);
        this.typeT = typeT;
    }

    bsqemit(): any {
        return ["TreeIR::SomethingEntityType", { ...this.bsqemit_constructable(), typeT: this.typeT }];
    }
    static bsqparse(jv: any): TIRSomethingEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::SomethingEntityType", "SomethingEntityType");
        const rr = new TIRSomethingEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeT);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

class TIRMapEntryEntityType extends TIRConstructableEntityType {
    readonly typeK: TIRTypeKey;
    readonly typeV: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeK: TIRTypeKey, typeV: TIRTypeKey) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes);
        this.typeK = typeK;
        this.typeV = typeV;
    }

    bsqemit(): any {
        return ["TreeIR::MapEntryEntityType", { ...this.bsqemit_constructable(), typeK: this.typeK, typeV: this.typeV }];
    }
    static bsqparse(jv: any): TIRMapEntryEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::MapEntryEntityType", "MapEntryEntityType");
        const rr = new TIRMapEntryEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeK, jv[1].typeV);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing special havoc type
class TIRHavocEntityType extends TIRInternalEntityType {
    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[]) {
        super(tkey, tname, srcInfo, srcFile, attributes, [], false);
    }

    bsqemit(): any {
        return ["TreeIR::HavocEntityType", this.bsqemit_internalentity()];
    }
    static bsqparse(jv: any): TIRHavocEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::HavocEntityType", "HavocEntityType");
        return new TIRHavocEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes);
    }
}

//abstract class for all the builtin collection types
abstract class TIRPrimitiveCollectionEntityType extends TIRInternalEntityType {
    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[]) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false);
    }

    bsqemit_collection(): any {
        return this.bsqemit_internalentity();
    }
}

//class representing List<T>
class TIRListEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes);
        this.typeT = typeT;
    }

    bsqemit(): any {
        return ["TreeIR::ListEntityType", { ...this.bsqemit_collection(), typeT: this.typeT }];
    }
    static bsqparse(jv: any): TIRListEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::ListEntityType", "ListEntityType");
        const rr = new TIRListEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeT);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing Stack<T>
class TIRStackEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes);
        this.typeT = typeT;
    }

    bsqemit(): any {
        return ["TreeIR::StackEntityType", { ...this.bsqemit_collection(), typeT: this.typeT }];
    }
    static bsqparse(jv: any): TIRStackEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::StackEntityType", "StackEntityType");
        const rr = new TIRStackEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeT);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing Queue<T>
class TIRQueueEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes);
        this.typeT = typeT;
    }

    bsqemit(): any {
        return ["TreeIR::QueueEntityType", { ...this.bsqemit_collection(), typeT: this.typeT }];
    }
    static bsqparse(jv: any): TIRQueueEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::QueueEntityType", "QueueEntityType");
        const rr = new TIRQueueEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeT);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing Set<T>
class TIRSetEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes);
        this.typeT = typeT;
    }

    bsqemit(): any {
        return ["TreeIR::SetEntityType", { ...this.bsqemit_collection(), typeT: this.typeT }];
    }
    static bsqparse(jv: any): TIRSetEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::SetEntityType", "SetEntityType");
        const rr = new TIRSetEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeT);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

//class representing Map<K, V>
class TIRMapEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeK: TIRTypeKey;
    readonly typeV: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeK: TIRTypeKey, typeV: TIRTypeKey) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes);
        this.typeK = typeK;
        this.typeV = typeV;
    }

    bsqemit(): any {
        return ["TreeIR::MapEntityType", { ...this.bsqemit_collection(), typeK: this.typeK, typeV: this.typeV }];
    }
    static bsqparse(jv: any): TIRMapEntityType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::MapEntityType", "MapEntityType");
        const rr = new TIRMapEntityType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, jv[1].typeK, jv[1].typeV);
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }
}

class TIRTaskType extends TIROOType {
    readonly binds: Map<string, TIRTypeKey>;

    readonly controls: { val: TIRLiteralValue | undefined, cname: string }[] = []; //control members
    readonly actions: { akey: TIRInvokeKey, aname: string }[] = []; //methods
    readonly mainfunc: { mkey: TIRInvokeKey, mname: string }; //a static function
    readonly onfuncs: { onCanel: TIRInvokeKey | undefined, onFailure: TIRInvokeKey | undefined, onTimeout: TIRInvokeKey | undefined };
    readonly lfuncs: { logStart: TIRInvokeKey | undefined, logEnd: TIRInvokeKey | undefined, taskEnsures: TIRInvokeKey | undefined, taskWarns: TIRInvokeKey | undefined };


    readonly statuseffect: TIRTaskStatusEffect = new TIRTaskStatusEffect([]);
    readonly eventeffect: TIRTaskEventEffect = new TIRTaskEventEffect([]);
    readonly enveffect: TIRTaskEnvironmentEffect = new TIRTaskEnvironmentEffect([], []);
    readonly resourceeffect: TIRTaskResourceEffect[] = [];

    readonly ensures: TIRTaskEnsures[] = [];

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[],
        binds: Map<string, TIRTypeKey>, mainfunc: { mkey: TIRInvokeKey, mname: string },
        onfuncs: { onCanel: TIRInvokeKey | undefined, onFailure: TIRInvokeKey | undefined, onTimeout: TIRInvokeKey | undefined },
        lfuncs: { logStart: TIRInvokeKey | undefined, logEnd: TIRInvokeKey | undefined, taskEnsures: TIRInvokeKey | undefined, taskWarns: TIRInvokeKey | undefined }
    ) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false);
        this.binds = binds;
        this.mainfunc = mainfunc;
        this.onfuncs = onfuncs;
        this.lfuncs = lfuncs;
    }

    bsqemit(): any {
        return ["TreeIR::TaskType", { ...this.bsqemit_ootype(), binds: [...this.binds], controls: this.controls.map((cc) => ({ val: cc.val ? cc.val.bsqemit() : null, cname: cc.cname })), actions: this.actions, mainfunc: this.mainfunc, onfuncs: { onCancel: this.onfuncs.onCanel || null, onFailure: this.onfuncs.onFailure || null, onTimeout: this.onfuncs.onTimeout || null }, lfuncs: { logStart: this.lfuncs.logStart || null, logEnd: this.lfuncs.logEnd || null, taskEnsures: this.lfuncs.taskEnsures || null, taskWarns: this.lfuncs.taskWarns || null }, statuseffect: this.statuseffect.bsqemit(), eventeffect: this.eventeffect.bsqemit(), enveffect: this.enveffect.bsqemit(), resourceeffect: this.resourceeffect.map((eff) => eff.bsqemit()), tskensures: this.ensures.map((ee) => ee.bsqemit()) }];
    }
    static bsqparse(jv: any): TIRTaskType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::TaskType", "TaskType");
        const rr = new TIRTaskType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, new Map(jv[1].binds), { mkey: jv[1].mainfunc.mkey, mname: jv[1].mainfunc.mname }, { onCanel: jv[1].onfuncs.onCancel || undefined, onFailure: jv[1].onfuncs.onFailure || undefined, onTimeout: jv[1].onfuncs.onTimeout || undefined }, { logStart: jv[1].lfuncs.logStart || undefined, logEnd: jv[1].lfuncs.logEnd || undefined, taskEnsures: jv[1].lfuncs.taskEnsures || undefined, taskWarns: jv[1].lfuncs.taskWarns || undefined });
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        rr.controls.push(...jv[1].controls.map((cc: any) => ({ val: cc.val ? TIRLiteralValue.bsqparse(cc.val) : undefined, cname: cc.cname })));
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

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], binds: Map<string, TIRTypeKey>) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false);
        this.binds = binds;
    }

    bsqemit(): any {
        return ["TreeIR::ConceptType", { ...this.bsqemit_ootype(), binds: [...this.binds] }];
    }
    static bsqparse(jv: any): TIRConceptType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::ConceptType", "ConceptType");
        const rr = new TIRConceptType(jv[1].tkey, jv[1].tname, SourceInfo.bsqparse(jv[1].sinfo), jv[1].srcFile, jv[1].attributes, jv[1].supertypes, new Map(jv[1].binds));
        TIROOType.bsqparse_ooinfo(jv[1], rr);

        return rr;
    }

    isAnyConcept(): boolean {
        return this.tkey === "Any";
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

    constructor(tkey: TIRTypeKey, concepts: TIRTypeKey[]) {
        super(tkey, concepts);
        this.conceptTypes = concepts;
    }

    bsqemit(): any {
        return ["TreeIR::ConceptSetType", { ...this.bsqemit_type(), conceptTypes: this.conceptTypes }];
    }
    static bsqparse(jv: any): TIRConceptSetType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::ConceptSetType", "ConceptSetType");
        return new TIRConceptSetType(jv[1].tkey, jv[1].conceptTypes);
    }
}

class TIRTupleType extends TIRType {
    readonly types: TIRTypeKey[];

    constructor(tkey: TIRTypeKey, types: TIRTypeKey[], supertypes: TIRTypeKey[]) {
        super(tkey, supertypes);
        this.types = types;
    }

    bsqemit(): any {
        return ["TreeIR::TupleType", { ...this.bsqemit_type(), types: this.types }];
    }
    static bsqparse(jv: any): TIRTupleType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::TupleType", "TupleType");
        return new TIRTupleType(jv[1].tkey, jv[1].types, jv[1].supertypes);
    }
}

class TIRRecordType extends TIRType {
    readonly entries: { pname: string, ptype: TIRTypeKey }[];

    constructor(tkey: TIRTypeKey, entries: { pname: string, ptype: TIRTypeKey }[], supertypes: TIRTypeKey[]) {
        super(tkey, supertypes);
        this.entries = entries;
    }

    bsqemit(): any {
        return ["TreeIR::RecordType", { ...this.bsqemit_type(), entries: this.entries }];
    }
    static bsqparse(jv: any): TIRRecordType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::RecordType", "RecordType");
        return new TIRRecordType(jv[1].tkey, jv[1].entries, jv[1].supertypes);
    }
}

class TIRUnionType extends TIRType {
    readonly options: TIRTypeKey[];

    constructor(tkey: TIRTypeKey, options: TIRTypeKey[]) {
        super(tkey, undefined);
        this.options = options;
    }

    bsqemit(): any {
        return ["TreeIR::UnionType", { ...this.bsqemit_type(), options: this.options }];
    }
    static bsqparse(jv: any): TIRUnionType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::UnionType", "UnionType");
        return new TIRUnionType(jv[1].tkey, jv[1].options);
    }
}

class TIREListType extends TIRType {
    readonly types: TIRTypeKey[];

    constructor(tkey: TIRTypeKey, types: TIRTypeKey[]) {
        super(tkey, undefined);
        this.types = types;
    }

    bsqemit(): any {
        return ["TreeIR::EListType", { ...this.bsqemit_type(), types: this.types }];
    }
    static bsqparse(jv: any): TIREListType {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::EListType", "EListType");
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
        return { ns: this.ns, name: this.name, sinfo: this.sourceLocation, srcFile: this.srcFile, attributes: this.attributes };
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
        return ["TreeIR::NamespaceConstDecl", { ...this.bsqemit_nsdecl(), declaredType: this.declaredType, value: this.value.bsqemit() }];
    }
    static bsqparse(jv: any): TIRNamespaceConstDecl {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::NamespaceConstDecl", "NamespaceConstDecl");
        return new TIRNamespaceConstDecl(jv[1].ns, jv[1].name, jv[1].sinfo, jv[1].srcFile, jv[1].attributes, jv[1].declaredType, TIRExpression.bsqparse(jv[1].value));
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
        return ["TreeIR::NamespaceFunctionDecl", { ...this.bsqemit_nsdecl(), ikey: this.ikey, invoke: this.invoke.bsqemit() }];
    }

    static bsqparse(jv: any): TIRNamespaceFunctionDecl {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::NamespaceFunctionDecl", "NamespaceFunctionDecl");
        return new TIRNamespaceFunctionDecl(jv[1].ns, jv[1].sinfo, jv[1].srcFile, TIRInvoke.bsqparse(jv[1].invoke));
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
        return ["TreeIR::NamespaceOperatorDecl", { ...this.bsqemit_nsdecl(), ikey: this.ikey, invoke: this.invoke.bsqemit() }];
    }
    static bsqparse(jv: any): TIRNamespaceOperatorDecl {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::NamespaceOperatorDecl", "NamespaceOperatorDecl");
        return new TIRNamespaceOperatorDecl(jv[1].ns, jv[1].sinfo, jv[1].srcFile, TIRInvoke.bsqparse(jv[1].invoke));
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
        return ["TreeIR::NamespaceLambdaDecl", { ikey: this.ikey, pcid: this.pcid, sinfo: this.sourceLocation, srcFile: this.srcFile, attributes: this.attributes, invoke: this.invoke.bsqemit() }];
    }
    static bsqparse(jv: any): TIRNamespaceLambdaDecl {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::NamespaceLambdaDecl", "NamespaceLambdaDecl");
        return new TIRNamespaceLambdaDecl(jv[1].pcid, jv[1].sinfo, jv[1].srcFile, TIRInvoke.bsqparse(jv[1].invoke));
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
    readonly capturedValues: { cname: string, ctype: TIRTypeKey }[];
    readonly capturedCodePacks: { cpname: string, cpval: TIRPCodeKey }[];

    constructor(ns: string, codekey: TIRPCodeKey, invk: TIRInvokeKey, recursive: boolean, terms: TIRTypeKey[], pcodes: TIRTypeKey[], capturedValues: { cname: string, ctype: TIRTypeKey }[], capturedCodePacks: { cpname: string, cpval: TIRPCodeKey }[]) {
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
        return ["TreeIR::CodePack", { ns: this.ns, codekey: this.codekey, invk: this.invk, isrecursive: this.recursive, terms: this.terms, pcodes: this.pcodes, capturedValues: this.capturedValues, capturedCodePacks: this.capturedCodePacks }];
    }
    static bsqparse(jv: any): TIRCodePack {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::CodePack", "CodePack");
        return new TIRCodePack(jv[1].ns, jv[1].codekey, jv[1].invk, jv[1].isrecursive, jv[1].terms, jv[1].pcodes, jv[1].capturedValues, jv[1].capturedCodePacks);
    }
}

abstract class TIRInfoTemplate {
    abstract bsqemit(): any;

    static bsqparse(jv: any): TIRInfoTemplate {
        if (jv[0] === "TreeIR::InfoTemplateRecord") {
            return TIRInfoTemplateRecord.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::InfoTemplateTuple") {
            return TIRInfoTemplateTuple.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::InfoTemplateConst") {
            return TIRInfoTemplateConst.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::InfoTemplateMacro") {
            return TIRInfoTemplateMacro.bsqparse(jv);
        }
        else if (jv[0] === "TreeIR::InfoTemplateValue") {
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
        return ["TreeIR::InfoTemplateRecord", { entries: this.entries.map((e) => ({ name: e.name, value: e.value.bsqemit() })) }];
    }
    static bsqparse(jv: any): TIRInfoTemplateRecord {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::InfoTemplateRecord", "InfoTemplateRecord");
        return new TIRInfoTemplateRecord(jv[1].entries.map((e: any) => ({ name: e.name, value: TIRInfoTemplate.bsqparse(e.value) })));
    }
}

class TIRInfoTemplateTuple extends TIRInfoTemplate {
    readonly entries: TIRInfoTemplate[];

    constructor(entries: TIRInfoTemplate[]) {
        super();
        this.entries = entries;
    }

    bsqemit(): any {
        return ["TreeIR::InfoTemplateTuple", { entries: this.entries.map((e) => e.bsqemit()) }];
    }
    static bsqparse(jv: any): TIRInfoTemplateTuple {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::InfoTemplateTuple", "InfoTemplateTuple");
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
        return ["TreeIR::InfoTemplateConst", { litexp: this.litexp.bsqemit() }];
    }
    static bsqparse(jv: any): TIRInfoTemplateConst {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::InfoTemplateConst", "InfoTemplateConst");
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
        return ["TreeIR::InfoTemplateMacro", { macro: this.macro }];
    }
    static bsqparse(jv: any): TIRInfoTemplateMacro {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::InfoTemplateMacro", "InfoTemplateMacro");
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
        return ["TreeIR::InfoTemplateValue", { argpos: this.argpos, argtype: this.argtype }];
    }
    static bsqparse(jv: any): TIRInfoTemplateValue {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::InfoTemplateValue", "InfoTemplateValue");
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
        return ["TreeIR::StringTemplate", { str: this.str }];
    }
    static bsqparse(jv: any): TIRStringTemplate {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::StringTemplate", "StringTemplate");
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
        return {
            ns: this.ns,
            consts: [...this.consts.entries()].map((e) => [e[0], e[1].bsqemit()]),
            functions: [...this.functions.entries()].map((e) => [e[0], e[1].map((f) => f.bsqemit())]),
            operators: [...this.operators.entries()].map((e) => [e[0], e[1].map((f) => f.bsqemit())]),
            concepts: [...this.concepts.entries()].map((e) => [e[0], e[1]]),
            objects: [...this.objects.entries()].map((e) => [e[0], e[1]]),
            tasks: [...this.tasks.entries()].map((e) => [e[0], e[1]]),
            lambdas: [...this.lambdas.entries()].map((e) => [e[0], e[1].bsqemit()]),
            codepacks: [...this.codepacks.entries()].map((e) => [e[0], e[1].bsqemit()]),
            msgformats: [...this.msgformats.entries()].map((e) => [e[0], e[1].bsqemit()]),
            stringformats: [...this.stringformats.entries()].map((e) => [e[0], e[1].bsqemit()])
        };
    }
    static bsqparse(jv: any): TIRNamespaceDeclaration {
        const ns = new TIRNamespaceDeclaration(jv[1].ns);
        jv.consts.forEach((e: any) => ns.consts.set(e.name, TIRNamespaceConstDecl.bsqparse(e.value)));
        jv.functions.forEach((e: any) => ns.functions.set(e[0], e[1].map((f: any) => TIRNamespaceFunctionDecl.bsqparse(f))));
        jv.operators.forEach((e: any) => ns.operators.set(e[0], e[1].map((f: any) => TIRNamespaceOperatorDecl.bsqparse(f))));
        jv.concepts.forEach((e: any) => ns.concepts.set(e[0], e[1]));
        jv.objects.forEach((e: any) => ns.objects.set(e[0], e[1]));
        jv.tasks.forEach((e: any) => ns.tasks.set(e[0], e[1]));
        jv.lambdas.forEach((e: any) => ns.lambdas.set(e[0], TIRNamespaceLambdaDecl.bsqparse(e[1])));
        jv.codepacks.forEach((e: any) => ns.codepacks.set(e[0], TIRCodePack.bsqparse(e[1])));
        jv.msgformats.forEach((e: any) => ns.msgformats.set(e[0], TIRInfoTemplate.bsqparse(e[1])));
        jv.stringformats.forEach((e: any) => ns.stringformats.set(e[0], TIRStringTemplate.bsqparse(e[1])));
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
    readonly validatorRegexs: Map<TIRTypeKey, BSQRegex>;
    readonly validatorPaths: Map<TIRTypeKey, BSQPathValidator>;

    getNamespace(ns: string): TIRNamespaceDeclaration {
        assert(this.namespaceMap.has(ns), "Missing namespace?");
        return this.namespaceMap.get(ns) as TIRNamespaceDeclaration;
    }

    getTypeAs<T extends TIRType>(tkey: TIRTypeKey): T {
        assert(this.typeMap.has(tkey), "Missing type");
        return this.typeMap.get(tkey) as T;
    }

    constructor(namespaceMap: Map<string, TIRNamespaceDeclaration>, typeMap: Map<TIRTypeKey, TIRType>, fieldMap: Map<TIRTypeKey, TIRMemberFieldDecl>, invokeMap: Map<TIRTypeKey, TIRInvoke>, pcodemap: Map<TIRPCodeKey, TIRCodePack>, literalRegexs: BSQRegex[], validatorRegexs: Map<TIRTypeKey, BSQRegex>, validatorPaths: Map<TIRTypeKey, BSQPathValidator>) {
        this.namespaceMap = namespaceMap;
        this.typeMap = typeMap;
        this.fieldMap = fieldMap;
        this.invokeMap = invokeMap;
        this.pcodemap = pcodemap;
        this.literalRegexs = literalRegexs;
        this.validatorRegexs = validatorRegexs;
        this.validatorPaths = validatorPaths;
    }

    private isConcreteSubtypeOf(t: TIRTypeKey, oftype: TIRConceptType): boolean {
        if(t === oftype.tkey) {
            return true;
        }
        else {
            const tdecl = this.typeMap.get(t) as TIRType;
            if(tdecl.supertypes === undefined) {
                return false;
            }
            else {
                for(const st in tdecl.supertypes) {
                    if(this.isConcreteSubtypeOf(st, oftype)) {
                        return true;
                    }
                }
                return false;
            }
        }
    }

    private isConcreteType(tt: TIRType): boolean {
        return !(tt instanceof TIRConceptType) && !(tt instanceof TIRConceptSetType) && !(tt instanceof TIRUnionType);
    }

    private getConcreteSubtypesOf(oftype: TIRConceptType): TIRTypeKey[] {
        let subtypes: TIRTypeKey[] = [];
        this.typeMap.forEach((tt) => {
            if(this.isConcreteType(tt) && this.isConcreteSubtypeOf(tt.tkey, oftype)) {
                subtypes.push(tt.tkey);
            }
        });

        return subtypes.sort();
    }

    private getConcreteSubtypesOfAny(oftypes: TIRConceptType[]): TIRTypeKey[] {
        let subtypes: Set<TIRTypeKey> = new Set<TIRTypeKey>();
        this.typeMap.forEach((tt) => {
            oftypes.forEach((oftt) => {
                if (this.isConcreteType(tt) && this.isConcreteSubtypeOf(tt.tkey, oftt)) {
                    subtypes.add(tt.tkey);
                }
            });
        });

        return [...subtypes].sort();
    }

    private getConcreteSubtypes(tt: TIRType): TIRTypeKey[] {
        if(tt instanceof TIRConceptType) {
            return this.getConcreteSubtypesOf(tt);
        }
        else if(tt instanceof TIRConceptSetType) {
            return this.getConcreteSubtypesOfAny(tt.conceptTypes.map((ct) => this.typeMap.get(ct) as TIRConceptType));
        }
        else if(tt instanceof TIRUnionType) {
            let allilt = new Set<TIRTypeKey>();
            tt.options.forEach((opt) => {
                const optilt = this.getConcreteSubtypes(this.typeMap.get(opt) as TIRType);
                optilt.forEach((ilt) => {
                    allilt.add(ilt);
                });
            });

            return [...allilt].sort();
        }
        else {
            return [tt.tkey];
        }
    }

    private getReferenceGraphTypes(tt: TIRType): TIRTypeKey[] {
        if (tt instanceof TIRObjectEntityType) {
            return tt.memberFields.map((ff) => ff.tkey);
        }
        else if (tt instanceof TIROkEntityType) {
            return [tt.typeT];
        }
        else if (tt instanceof TIRErrEntityType) {
            return [tt.typeE];
        }
        else if (tt instanceof TIRSomethingEntityType) {
            return [tt.typeT];
        }
        else if (tt instanceof TIRMapEntryEntityType) {
            return [tt.typeK, tt.typeV];
        }
        else if (tt instanceof TIRListEntityType) {
            return [tt.typeT];
        }
        else if (tt instanceof TIRStackEntityType) {
            return [tt.typeT];
        }
        else if (tt instanceof TIRQueueEntityType) {
            return [tt.typeT];
        }
        else if (tt instanceof TIRSetEntityType) {
            return [tt.typeT];
        }
        else if (tt instanceof TIRMapEntityType) {
            return [tt.typeK, tt.typeV];
        }
        else if (tt instanceof TIRTaskType) {
            return tt.memberFields.map((mf) => mf.tkey);
        }
        else if (tt instanceof TIRTupleType) {
            return [...tt.types];
        }
        else if (tt instanceof TIRRecordType) {
            return tt.entries.map((entry) => entry.pname);
        }
        else if (tt instanceof TIREListType) {
            return [...tt.types];
        }
        else {
            return [];
        }
    }

    private topoVisitType(tt: TIRTypeKey, visited: Set<TIRTypeKey>, tordered: TIRTypeKey[], subtinfo: Map<TIRTypeKey, TIRTypeKey[]>) {
        if (visited.has(tt)) {
            return;
        }

        visited.add(tt);

        const ttdecl = this.typeMap.get(tt) as TIRType;
        if (this.isConcreteType(ttdecl)) {
            const ctypes = this.getReferenceGraphTypes(this.typeMap.get(tt) as TIRType);
            ctypes.forEach((succ) => {
                this.topoVisitType(succ, visited, tordered, subtinfo);
            });
        }
        else {
            const subs = subtinfo.get(tt) as TIRTypeKey[];
            subs.forEach((succ) => {
                this.topoVisitType(succ, visited, tordered, subtinfo);
            });
        }

        tordered.push(tt);
    }

    private sccVisitType(tt: TIRTypeKey, scc: Set<TIRTypeKey>, marked: Set<TIRTypeKey>, subtinfo: Map<TIRTypeKey, TIRTypeKey[]>) {
        if (marked.has(tt)) {
            return;
        }

        scc.add(tt);
        marked.add(tt);
        
        const ttdecl = this.typeMap.get(tt) as TIRType;
        if (this.isConcreteType(ttdecl)) {
            const ctypes = this.getReferenceGraphTypes(this.typeMap.get(tt) as TIRType);
            ctypes.forEach((succ) => {
                this.sccVisitType(succ, scc, marked, subtinfo);
            });
        }
        else {
            const subs = subtinfo.get(tt) as TIRTypeKey[];
            subs.forEach((succ) => {
                this.sccVisitType(succ, scc, marked, subtinfo);
            });
        }
    }

    private computeEntryPointRecursiveTypeInfo(entrytypes: TIRTypeKey[], subtinfo: Map<TIRTypeKey, TIRTypeKey[]>): Map<TIRTypeKey, boolean> {
        let visited = new Set<TIRTypeKey>();
        let tordered: TIRTypeKey[] = [];
        entrytypes.forEach((tt) => {
            this.topoVisitType(tt, visited, tordered, subtinfo);
        });

        tordered = tordered.reverse();

        let marked = new Set<TIRTypeKey>();
        let recursive: (Set<TIRTypeKey>)[] = [];
        for (let i = 0; i < tordered.length; ++i) {
            let scc = new Set<TIRTypeKey>();
            this.sccVisitType(tordered[i], scc, marked, subtinfo);

            const rtt = this.getReferenceGraphTypes(this.typeMap.get(tordered[i]) as TIRType);
            if (scc.size > 1 || rtt.includes(tordered[i])) {
                recursive.push(scc);
            }
        }

        let recursiveMap = new Map<TIRTypeKey, boolean>();
        tordered.forEach((tt) => {
            const scc = recursive.find((scc) => scc.has(tt));
            recursiveMap.set(tt, scc !== undefined);
        });

        return recursiveMap;
    }

    private generateExportedTypeInfoForTIRType(tt: TIRType, recursiveMap: Map<TIRTypeKey, boolean>, subtinfo: Map<TIRTypeKey, TIRTypeKey[]>): TypeInfo.BSQType {
        if (tt instanceof TIRObjectEntityType) {
            const fields = tt.allfields.map((ff) => {
                return { fname: this.fieldMap.get(ff.fkey)!.name, ftype: ff.ftype };
            });

            return new TypeInfo.StdEntityType(tt.tkey, tt.consinvariants.length !== 0, fields, recursiveMap.get(tt.tkey) as boolean);
        }
        else if (tt instanceof TIREnumEntityType) {
            return new TypeInfo.EnumType(tt.tkey, tt.enums);
        }
        else if (tt instanceof TIRTypedeclEntityType) {
            const hasvalidate = tt.consinvariantsall.length !== 0 || tt.apivalidates.length !== 0;
            return new TypeInfo.TypedeclType(tt.tkey, tt.representation, tt.valuetype, recursiveMap.get(tt.tkey) as boolean, hasvalidate, tt.strvalidator !== undefined ? tt.strvalidator.vtype : undefined, tt.pthvalidator !== undefined ? tt.pthvalidator.vtype : undefined);
        }
        else if (tt instanceof TIRPrimitiveInternalEntityType) {
            return new TypeInfo.PrimitiveType(tt.tkey);
        }
        else if (tt instanceof TIRValidatorEntityType) {
            return new TypeInfo.ValidatorREType(tt.tkey);
        }
        else if (tt instanceof TIRStringOfEntityType) {
            return new TypeInfo.StringOfType(tt.validatortype);
        }
        else if (tt instanceof TIRASCIIStringOfEntityType) {
            return new TypeInfo.ASCIIStringOfType(tt.validatortype);
        }
        else if (tt instanceof TIRPathValidatorEntityType) {
            return new TypeInfo.ValidatorPthType(tt.tkey);
        }
        else if (tt instanceof TIRPathEntityType) {
            return new TypeInfo.PathType(tt.validatortype);
        }
        else if (tt instanceof TIRPathFragmentEntityType) {
            return new TypeInfo.PathFragmentType(tt.validatortype);
        }
        else if (tt instanceof TIRPathGlobEntityType) {
            return new TypeInfo.PathGlobType(tt.validatortype);
        }
        else if (tt instanceof TIROkEntityType) {
            return new TypeInfo.OkType(tt.typeT, tt.typeE, recursiveMap.get(tt.tkey) as boolean);
        }
        else if (tt instanceof TIRErrEntityType) {
            return new TypeInfo.ErrorType(tt.typeT, tt.typeE, recursiveMap.get(tt.tkey) as boolean);
        }
        else if (tt instanceof TIRSomethingEntityType) {
            return new TypeInfo.SomethingType(tt.typeT, recursiveMap.get(tt.tkey) as boolean);
        }
        else if (tt instanceof TIRMapEntryEntityType) {
            return new TypeInfo.MapEntryType(tt.typeK, tt.typeV, recursiveMap.get(tt.tkey) as boolean);
        }
        else if (tt instanceof TIRListEntityType) {
            return new TypeInfo.ListType(tt.typeT, recursiveMap.get(tt.tkey) as boolean);
        }
        else if (tt instanceof TIRStackEntityType) {
            return new TypeInfo.StackType(tt.typeT, recursiveMap.get(tt.tkey) as boolean);
        }
        else if (tt instanceof TIRQueueEntityType) {
            return new TypeInfo.QueueType(tt.typeT, recursiveMap.get(tt.tkey) as boolean);
        }
        else if (tt instanceof TIRSetEntityType) {
            return new TypeInfo.SetType(tt.typeT, recursiveMap.get(tt.tkey) as boolean);
        }
        else if (tt instanceof TIRMapEntityType) {
            return new TypeInfo.MapType(tt.typeK, tt.typeV, recursiveMap.get(tt.tkey) as boolean);
        }
        else if (tt instanceof TIRTaskType) {
            assert(false, "NOT IMPLEMENTED TYPE -- TIRTaskType generateExportedTypeInfoForTIRType");
            return (undefined as any) as TypeInfo.BSQType;
        }
        else if (tt instanceof TIRConceptType) {
            if (tt.isOptionConcept()) {
                return new TypeInfo.OptionType(tt.binds.get("T") as TIRTypeKey, recursiveMap.get(tt.tkey) as boolean);
            }
            else if(tt.isResultConcept()) {
                return new TypeInfo.ResultType(tt.binds.get("T") as TIRTypeKey, tt.binds.get("E") as TIRTypeKey, recursiveMap.get(tt.tkey) as boolean);
            }
            else {
                return new TypeInfo.StdConceptType(tt.tkey, subtinfo.get(tt.tkey) as TIRTypeKey[], recursiveMap.get(tt.tkey) as boolean);
            }
        }
        else if (tt instanceof TIRConceptSetType) {
            return new TypeInfo.ConceptSetType(tt.conceptTypes, subtinfo.get(tt.tkey) as TIRTypeKey[], recursiveMap.get(tt.tkey) as boolean);
        }
        else if (tt instanceof TIRTupleType) {
            return new TypeInfo.TupleType(tt.types, recursiveMap.get(tt.tkey) as boolean);
        }
        else if (tt instanceof TIRRecordType) {
            return new TypeInfo.RecordType(tt.entries, recursiveMap.get(tt.tkey) as boolean);
        }
        else if (tt instanceof TIRUnionType) {
            return new TypeInfo.UnionType(tt.options, recursiveMap.get(tt.tkey) as boolean);
        }
        else if (tt instanceof TIREListType) {
            assert(false, "NOT IMPLEMENTED TYPE -- TIREListType generateExportedTypeInfoForTIRType");
            return (undefined as any) as TypeInfo.BSQType;
        }
        else {
            assert(false, "UNKNOWN TYPE -- generateExportedTypeInfoForTIRType");
            return (undefined as any) as TypeInfo.BSQType;
        }
    }

    generateTypeInfo(entrytypes: TIRTypeKey[], aliases: Map<string, TIRTypeKey>): TypeInfo.AssemblyInfo {
        let subtinfo = new Map<TIRTypeKey, TypeInfo.BSQTypeKey[]>();
        this.typeMap.forEach((v) => {
            if(!this.isConcreteType(v)) {
                const csinfo = this.getConcreteSubtypes(v);
                subtinfo.set(v.tkey, csinfo);
            }
        });

        const rescursiveMap = this.computeEntryPointRecursiveTypeInfo(entrytypes, subtinfo);

        let typerefs = new Map<TypeInfo.BSQTypeKey, TypeInfo.BSQType>();
        this.typeMap.forEach((v, k) => {
            typerefs.set(k, this.generateExportedTypeInfoForTIRType(v, rescursiveMap, subtinfo));
        });

        let aliasmap = new Map<string, TypeInfo.BSQType>();
        aliases.forEach((v, k) => {
            aliasmap.set(k, typerefs.get(v) as TypeInfo.BSQType);
        });

        let namespaces = new Map<string, TypeInfo.NamespaceDecl>();
        this.namespaceMap.forEach((v) => {
            let nstypes: TIRTypeKey[] = [];
            v.concepts.forEach((c) => {
                c.forEach((cc) => {
                    if(typerefs.has(cc)) {
                        nstypes.push(cc);
                    }
                });
            });
            v.objects.forEach((o) => {
                o.forEach((oo) => {
                    if(typerefs.has(oo)) {
                        nstypes.push(oo);
                    }
                });
            });
        
            namespaces.set(v.ns, new TypeInfo.NamespaceDecl(v.ns, nstypes));
        });

        let revalidators = new Map<TypeInfo.BSQTypeKey, string>();
        this.validatorRegexs.forEach((v, k) => {
            revalidators.set(k, v.regexstr);
        });

        let pthvalidators = new Map<TypeInfo.BSQTypeKey, string>();
        this.validatorPaths.forEach((v, k) => {
            pthvalidators.set(k, "[TODO]");
        });

        return new TypeInfo.AssemblyInfo(aliasmap, namespaces, typerefs, revalidators, pthvalidators);
    }

    bsqemit(): any {
        return {
            namespaceMap: [...this.namespaceMap.entries()].map((e) => [e[0], e[1].bsqemit()]),
            typeMap: [...this.typeMap.entries()].map((e) => [e[0], e[1].bsqemit()]),
            fieldMap: [...this.fieldMap.entries()].map((e) => [e[0], e[1].bsqemit()]),
            invokeMap: [...this.invokeMap.entries()].map((e) => [e[0], e[1].bsqemit()]),
            pcodemap: [...this.pcodemap.entries()].map((e) => [e[0], e[1].bsqemit()]),
            literalRegexs: this.literalRegexs.map((r) => r.jemit()),
            validatorRegexs: [...this.validatorRegexs.entries()].map((e) => [e[0], e[1].jemit()]),
            validatorPaths: [...this.validatorPaths.entries()].map((e) => [e[0], e[1].jemit()])
        };
    }
    static bsqparse(jv: any): TIRAssembly {
        const nsmap = new Map<string, TIRNamespaceDeclaration>();
        jv.namespaceMap.forEach((e: any) => nsmap.set(e[0], TIRNamespaceDeclaration.bsqparse(e[1])));

        const typemap = new Map<TIRTypeKey, TIRType>();
        jv.typeMap.forEach((e: any) => typemap.set(e[0], TIRType.bsqparse(e.value)));

        const fieldmap = new Map<TIRTypeKey, TIRMemberFieldDecl>();
        jv.fieldMap.forEach((e: any) => fieldmap.set(e[0], TIRMemberFieldDecl.bsqparse(e[1])));

        const invokemap = new Map<TIRTypeKey, TIRInvoke>();
        jv.invokeMap.forEach((e: any) => invokemap.set(e[0], TIRInvoke.bsqparse(e[1])));

        const pcodemap = new Map<TIRPCodeKey, TIRCodePack>();
        jv.pcodemap.forEach((e: any) => pcodemap.set(e[0], TIRCodePack.bsqparse(e[1])));

        const literalRegexs = jv[1].literalRegexs.map((r: any) => BSQRegex.jparse(r));

        const validatorRegexs = new Map<string, BSQRegex>();
        jv.validatorRegexs.forEach((e: any) => validatorRegexs.set(e[0], BSQRegex.jparse(e[1])));

        const validatorPaths = new Map<string, BSQPathValidator>();
        jv.validatorPaths.forEach((e: any) => validatorPaths.set(e[0], BSQPathValidator.jparse(e[1])));

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
