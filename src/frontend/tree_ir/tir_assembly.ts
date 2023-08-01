
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

const s_iident = "  ";


function sinfo_bsqemit(sinfo: SourceInfo): string {
    return `TreeIR::SourceInfo{${sinfo.line}, ${sinfo.column}, ${sinfo.pos}, ${sinfo.span}}`;
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

    bsqemit(): string {
        let pfx = `TIRTree:TypeName{"${this.ns}"ValidNamespace, "${this.name}"ValidTypeName`;
        if(this.templates !== undefined) {
            const ttstr = this.templates.map((t) => `"${t}"ValidTypeKey`).join(", ");
            pfx += `, List{${ttstr}}`;
        }
        pfx += "}";

        return pfx;
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

    bsqemit(): string {
        if(this.ddlit === undefined) {
            return `TIRTree:FunctionParameter{"${this.name}"ValidIdentifier, "${this.type}"ValidTypeKey}`;
        }
        else {
            return "[NOT IMPLEMENTED -- function param with literal default value]";
        }
    }
}

class TIRPreConditionDecl {
    readonly exp: TIRExpression;
    readonly args: TIRFunctionParameter[];

    constructor(exp: TIRExpression, args: TIRFunctionParameter[]) {
        this.exp = exp;
        this.args = args;
    }

    bsqemit(ii: string): string {
        return `TreeIR::PreConditionDecl{\n${ii + s_iident}${this.exp.bsqemit(ii + s_iident)},\n${ii + s_iident}List{${this.args.map((arg) => arg.bsqemit())}}\n${ii}}`
    }
}

class TIRPostConditionDecl {
    readonly exp: TIRExpression;
    readonly args: TIRFunctionParameter[];

    constructor(exp: TIRExpression, args: TIRFunctionParameter[]) {
        this.exp = exp;
        this.args = args;
    }

    bsqemit(ii: string): string {
        return `TreeIR::PostConditionDecl{\n${ii + s_iident}${this.exp.bsqemit(ii + s_iident)},\n${ii + s_iident}List{${this.args.map((arg) => arg.bsqemit())}}\n${ii}}`
    }
}

class TIRInvokeSampleDeclInline {
    readonly sinfo: SourceInfo;
    readonly istest: boolean;
    readonly args: string; //a tuple of the arguments
    readonly output: string;

    constructor(sinfo: SourceInfo, istest: boolean, args: string, output: string) {
        this.sinfo = sinfo;
        this.istest = istest;
        this.args = args;
        this.output = output;
    }

    bsqemit(ii: string): string {
        return `TreeIR::InlineSampleDecl{`
        + `\n${ii + s_iident}${sinfo_bsqemit(this.sinfo)}`
        + `,\n${ii + s_iident}${this.istest}`
        + `,\n${ii + s_iident}${this.args}`
        + `,\n${ii + s_iident}${this.output}`
        + `\n${ii}}`;
    }
}

class TIRInvokeSampleDeclFile {
    readonly sinfo: SourceInfo;
    readonly istest: boolean;
    readonly filepath: string; //may use the $root and $src meta variables

    constructor(sinfo: SourceInfo, istest: boolean, filepath: string) {
        this.sinfo = sinfo;
        this.istest = istest;
        this.filepath = filepath;
    }

    bsqemit(ii: string): string {
        return `TreeIR::InlineSampleDecl{`
        + `\n${ii + s_iident}${sinfo_bsqemit(this.sinfo)}`
        + `,\n${ii + s_iident}${this.istest}`
        + `,\n${ii + s_iident}${this.filepath}`
        + `\n${ii}}`;
    }
}

class TIRObjectInvariantDecl {
    readonly exp: TIRExpression;
    readonly args: TIRFunctionParameter[];

    constructor(exp: TIRExpression, args: TIRFunctionParameter[]) {
        this.exp = exp;
        this.args = args;
    }

    bsqemit(ii: string): string {
        return `{`
        + `\n${ii + s_iident}${this.exp.bsqemit(ii + s_iident)}`
        + `,\n${ii + s_iident}List{${this.args.map((arg) => arg.bsqemit())}}`
        + `\n${ii}}`;
    }
}

class TIRObjectValidateDecl {
    readonly exp: TIRExpression;
    readonly args: TIRFunctionParameter[];

    constructor(exp: TIRExpression, args: TIRFunctionParameter[]) {
        this.exp = exp;
        this.args = args;
    }

    bsqemit(ii: string): string {
        return `{`
        + `\n${ii + s_iident}${this.exp.bsqemit(ii + s_iident)}`
        + `,\n${ii + s_iident}List{${this.args.map((arg) => arg.bsqemit())}}`
        + `\n${ii}}`;
    }
}

class TIRTypedeclInvariantDecl {
    readonly exp: TIRExpression;
    readonly vtype: TIRTypeKey;

    constructor(exp: TIRExpression, vtype: TIRTypeKey) {
        this.exp = exp;
        this.vtype = vtype;
    }

    bsqemit(ii: string): string {
        return `{`
        + `\n${ii + s_iident}${this.exp.bsqemit(ii + s_iident)}`
        + `,\n${ii + s_iident}"${this.vtype}"ValidTypeKey`
        + `\n${ii}}`;
    }
}

class TIRTypedeclValidateDecl {
    readonly exp: TIRExpression;
    readonly vtype: TIRTypeKey;

    constructor(exp: TIRExpression, vtype: TIRTypeKey) {
        this.exp = exp;
        this.vtype = vtype;
    }

    bsqemit(ii: string): string {
        return `{`
        + `\n${ii + s_iident}${this.exp.bsqemit(ii + s_iident)}`
        + `,\n${ii + s_iident}"${this.vtype}"ValidTypeKey`
        + `\n${ii}}`;
    }
}

class TIRTaskStatusEffect {
    readonly statusinfo: TIRTypeKey[];

    constructor(statusinfo: TIRTypeKey[]) {
        this.statusinfo = statusinfo;
    }

    bsqemit(ii: string): string {
        return "[NOT IMPLEMENTED -- task status effect]";
    }
}

class TIRTaskEventEffect {
    readonly eventinfo: TIRTypeKey[];

    constructor(eventinfo: TIRTypeKey[]) {
        this.eventinfo = eventinfo;
    }

    bsqemit(ii: string): string {
        return "[NOT IMPLEMENTED -- task event effect]"
    }
}

class TIRTaskEnvironmentEffect {
    readonly readvars: string[]; //string "*" is wildcard
    readonly writevars: string[]; //string "*" is wildcard

    constructor(readvars: string[], writevars: string[]) {
        this.readvars = readvars;
        this.writevars = writevars;
    }

    bsqemit(ii: string): string {
        return "[NOT IMPLEMENTED -- task environment effect]"
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

    bsqemit(ii: string): string {
        return "[NOT IMPLEMENTED -- task resource effect]"
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

    bsqemit(ii: string): string {
        return "[NOT IMPLEMENTED -- task ensures]"
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
    readonly samplesinline: TIRInvokeSampleDeclInline[];
    readonly samplesfile: TIRInvokeSampleDeclFile[];

    constructor(invkey: TIRInvokeKey, name: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: string[], recursive: boolean, tbinds: Map<string, TIRTypeKey>, pcodes: Map<string, TIRPCodeKey>, isMemberMethod: boolean, isVirtual: boolean, isDynamicOperator: boolean, isLambda: boolean, params: TIRFunctionParameter[], isThisRef: boolean, resultType: TIRTypeKey, preconds: TIRPreConditionDecl[], postconds: TIRPostConditionDecl[], samplesinline: TIRInvokeSampleDeclInline[], samplesfile: TIRInvokeSampleDeclFile[]) {
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
        this.samplesinline = samplesinline;
        this.samplesfile = samplesfile;
    }

    bsqemit_inv(ii: string): string {
        const bindopts = [...this.tbinds.entries()].sort((a, b) => a[0].localeCompare(b[0])).map((ee) => `"${ee[0]}" => "${ee[1]}"ValidTypeKey`);
        const binds = bindopts.length !== 0 ? `Map{${bindopts.join(", ")}}` : "Map{}";

        const pcodeopts = [...this.pcodes.entries()].sort((a, b) => a[0].localeCompare(b[0])).map((ee) => `"${ee[0]}" => "${ee[1]}"ValidPCodeKey`);
        const pcodes = pcodeopts.length !== 0 ? `Map{${pcodeopts.join(", ")}}` : "Map{}";

        const paramopts = this.params.map((pp) => pp.bsqemit());
        const params = paramopts.length !== 0 ? `List{${paramopts.join(", ")}}` : "List{}";

        const precondopts = this.preconditions.map((pp) => pp.bsqemit(ii + s_iident + s_iident));
        const preconds = precondopts.length !== 0 ? `List{${ii + s_iident + s_iident}${precondopts.join("\n, " + ii + s_iident + s_iident)}\n${ii + s_iident}}` : "List{}";
        
        const postcondopts = this.postconditions.map((pp) => pp.bsqemit(ii + s_iident + s_iident));
        const postconds = postcondopts.length !== 0 ? `List{${ii + s_iident + s_iident}${postcondopts.join("\n, " + ii + s_iident + s_iident)}\n${ii + s_iident}}` : "List{}";

        const isampleopts = this.samplesinline.map((pp) => pp.bsqemit(ii + s_iident + s_iident));
        const isamples = isampleopts.length !== 0 ? `List{${ii + s_iident + s_iident}${isampleopts.join("\n, " + ii + s_iident + s_iident)}\n${ii + s_iident}}` : "List{}";

        const fsampleopts = this.samplesfile.map((pp) => pp.bsqemit(ii + s_iident + s_iident));
        const fsamples = fsampleopts.length !== 0 ? `List{${ii + s_iident + s_iident}${fsampleopts.join("\n, " + ii + s_iident + s_iident)}\n${ii + s_iident}}` : "List{}";

        return `{`
        + `\n${ii + s_iident}"${this.invkey}"TreeIR::ValidTypeKey`
        + `\n${ii + s_iident}"${this.name}"ValidIdentifier`
        + `\n${ii + s_iident}${sinfo_bsqemit(this.startSourceLocation)}`
        + `\n${ii + s_iident}${sinfo_bsqemit(this.endSourceLocation)}`
        + `\n${ii + s_iident}"${this.srcFile}"String`
        + `\n${ii + s_iident}${"[" + this.attributes.join(", ") + "]"}`
        + `\n${ii + s_iident}${this.isrecursive ? "true" : "false"}`
        + `\n${ii + s_iident}${binds}`
        + `\n${ii + s_iident}${pcodes}`
        + `\n${ii + s_iident}${this.isMemberMethod ? "true" : "false"}`
        + `\n${ii + s_iident}${this.isVirtual ? "true" : "false"}`
        + `\n${ii + s_iident}${this.isDynamicOperator ? "true" : "false"}`
        + `\n${ii + s_iident}${this.isLambda ? "true" : "false"}`
        + `\n${ii + s_iident}${this.isThisRef ? "true" : "false"}`
        + `\n${ii + s_iident}${params}`
        + `\n${ii + s_iident}"${this.resultType}"ValidTypeKey`
        + `\n${ii + s_iident}${preconds}`
        + `\n${ii + s_iident}${postconds}`
        + `\n${ii + s_iident}${isamples}`
        + `\n${ii + s_iident}${fsamples}`;
    }

    abstract bsqemit(ii: string): string;
}

class TIRInvokeAbstractDeclaration extends TIRInvoke {
    constructor(invkey: TIRInvokeKey, name: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: string[], recursive: boolean, tbinds: Map<string, TIRTypeKey>, pcodes: Map<string, TIRPCodeKey>, isMemberMethod: boolean, isDynamicOperator: boolean, params: TIRFunctionParameter[], isThisRef: boolean, resultType: TIRTypeKey, preconds: TIRPreConditionDecl[], postconds: TIRPostConditionDecl[], samplesinline: TIRInvokeSampleDeclInline[], samplesfile: TIRInvokeSampleDeclFile[]) {
        super(invkey, name, sinfoStart, sinfoEnd, srcFile, attributes, recursive, tbinds, pcodes, isMemberMethod, true, isDynamicOperator, false, params, isThisRef, resultType, preconds, postconds, samplesinline, samplesfile);
    }

    bsqemit(ii: string): string {
        return this.bsqemit_inv(ii) 
        + `\n${ii}}`;
    }
}

class TIRInvokeImplementation extends TIRInvoke {
    readonly body: TIRStatement[];

    constructor(invkey: TIRInvokeKey, name: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: string[], recursive: boolean, tbinds: Map<string, TIRTypeKey>, pcodes: Map<string, TIRPCodeKey>, isMemberMethod: boolean, isVirtual: boolean, isDynamicOperator: boolean, isLambda: boolean, params: TIRFunctionParameter[], isThisRef: boolean, resultType: TIRTypeKey, preconds: TIRPreConditionDecl[], postconds: TIRPostConditionDecl[], samplesinline: TIRInvokeSampleDeclInline[], samplesfile: TIRInvokeSampleDeclFile[], body: TIRStatement[]) {
        super(invkey, name, sinfoStart, sinfoEnd, srcFile, attributes, recursive, tbinds, pcodes, isMemberMethod, isVirtual, isDynamicOperator, isLambda, params, isThisRef, resultType, preconds, postconds, samplesinline, samplesfile);

        this.body = body;
    }

    bsqemit(ii: string): string {
        const bodyopts = this.body.map((stmt) => stmt.bsqemit(ii + s_iident));
        const body = bodyopts.length !== 0 ? `List{${ii + s_iident}${bodyopts.join("\n, " + ii + s_iident)}\n${ii + s_iident}}` : "List{}";

        return this.bsqemit_inv(ii)
        + `,\n${ii + s_iident}${body}`
        + `\n${ii}}`;
    }
}

class TIRInvokeSynthesis extends TIRInvoke {
    constructor(invkey: TIRInvokeKey, name: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: string[], recursive: boolean, tbinds: Map<string, TIRTypeKey>, pcodes: Map<string, TIRPCodeKey>, isMemberMethod: boolean, isVirtual: boolean, isDynamicOperator: boolean, isLambda: boolean, params: TIRFunctionParameter[], isThisRef: boolean, resultType: TIRTypeKey, preconds: TIRPreConditionDecl[], postconds: TIRPostConditionDecl[], samplesinline: TIRInvokeSampleDeclInline[], samplesfile: TIRInvokeSampleDeclFile[]) {
        super(invkey, name, sinfoStart, sinfoEnd, srcFile, attributes, recursive, tbinds, pcodes, isMemberMethod, isVirtual, isDynamicOperator, isLambda, params, isThisRef, resultType, preconds, postconds, samplesinline, samplesfile);
    }

    bsqemit(ii: string): string {
        return this.bsqemit_inv(ii) 
        + `\n${ii}}`;
    }
}

class TIRInvokePrimitive extends TIRInvoke {
    readonly body: string;

    constructor(invkey: TIRInvokeKey, name: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: string[], recursive: boolean, tbinds: Map<string, TIRTypeKey>, pcodes: Map<string, TIRPCodeKey>, params: TIRFunctionParameter[], resultType: TIRTypeKey, body: string) {
        super(invkey, name, sinfoStart, sinfoEnd, srcFile, attributes, recursive, tbinds, pcodes, false, false, false, false, params, false, resultType, [], [], [], []);

        this.body = body;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_inv(ii)
        + `,\n${ii + s_iident}"${this.body}"`
        + `\n${ii}}`;
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

    bsqemit_decl(ii: string): string {
        const attropts = this.attributes.map((a) => `"${a}"`);
        const attrs = attropts.length !== 0 ? `List{${attropts.join(", ")}}` : "List{}";

        return `{`
        + `\n${ii + s_iident}"${this.tkey}"ValidTypeKey`
        + `,\n${ii + s_iident}"${this.name}"ValidIdentifier`
        + `,\n${ii + s_iident}${sinfo_bsqemit(this.sourceLocation)}`
        + `,\n${ii + s_iident}"${this.srcFile}"`
        + `,\n${ii + s_iident}${attrs}`;
    }

    abstract bsqemit(ii: string): string;
}

class TIRConstMemberDecl extends TIRMemberDecl {
    readonly declaredType: TIRTypeKey;
    readonly value: TIRExpression;

    constructor(tkey: TIRTypeKey, name: string, srcInfo: SourceInfo, srcFile: string, attributes: string[], declaredtype: TIRTypeKey, value: TIRExpression) {
        super(tkey, name, srcInfo, srcFile, attributes);
        this.declaredType = declaredtype;
        this.value = value;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_decl(ii)
        + `,\n${ii + s_iident}"${this.declaredType}"ValidTypeKey`
        + `,\n${ii + s_iident}${this.value.bsqemit(ii + s_iident)}`
        + `\n${ii}}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_decl(ii)
        + `,\n${ii + s_iident}"${this.ikey}"ValidInvokeKey`
        + `,\n${ii + s_iident}${this.invoke.bsqemit(ii + s_iident)}`
        + `\n${ii}}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_decl(ii)
        + `,\n${ii + s_iident}"${this.fkey}"ValidFieldKey`
        + `,\n${ii + s_iident}"${this.declaredType}"ValidTypeKey`
        + `\n${ii}}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_decl(ii)
        + `,\n${ii + s_iident}"${this.ikey}"ValidInvokeKey`
        + `,\n${ii + s_iident}${this.invoke.bsqemit(ii + s_iident)}`
        + `\n${ii}}`;
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

    bsqemit_type(ii: string): string {
        const superopts = this.supertypes !== undefined ? ("List{" + [...this.supertypes].map((st) => `"${st}"ValidTypeKey`).join(", ") + "}") : "none";

        return `{`
        + `\n${ii + s_iident}"${this.tkey}"ValidTypeKey`
        + `,\n${ii + s_iident}${superopts}`;
    }

    abstract bsqemit(ii: string): string;
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

    bsqemit_ootype(ii: string): string {
        const attropts = this.attributes.map((a) => `"${a}"`);
        const attrs = attropts.length !== 0 ? `List{${attropts.join(", ")}}` : "List{}";

        const constopts = this.constMembers.map((cm) => cm.bsqemit(ii + s_iident + s_iident));
        const constmembers = constopts.length !== 0 ? `List{\n${ii + s_iident + s_iident}${constopts.join(`,\n${ii + s_iident + s_iident}`)}\n${ii + s_iident}}` : "List{}";

        const staticopts = this.staticFunctions.map((sf) => sf.bsqemit(ii + s_iident + s_iident));
        const staticfunctions = staticopts.length !== 0 ? `List{\n${ii + s_iident + s_iident}${staticopts.join(`,\n${ii + s_iident + s_iident}`)}\n${ii + s_iident}}` : "List{}";

        const fieldopts = this.memberFields.map((mf) => mf.bsqemit(ii + s_iident + s_iident));
        const memberfields = fieldopts.length !== 0 ? `List{\n${ii + s_iident + s_iident}${fieldopts.join(`,\n${ii + s_iident + s_iident}`)}\n${ii + s_iident}}` : "List{}";

        const methodopts = this.memberMethods.map((mm) => mm.bsqemit(ii + s_iident + s_iident));
        const membermethods = methodopts.length !== 0 ? `List{\n${ii + s_iident + s_iident}${methodopts.join(`,\n${ii + s_iident + s_iident}`)}\n${ii + s_iident}}` : "List{}";

        return this.bsqemit_type(ii)
        + `,\n${ii + s_iident}${this.tname.bsqemit()}`
        + `,\n${ii + s_iident}${sinfo_bsqemit(this.sourceLocation)}`
        + `,\n${ii + s_iident}"${this.srcFile}"`
        + `,\n${ii + s_iident}${attrs}`
        + `,\n${ii + s_iident}${constmembers}`
        + `,\n${ii + s_iident}${staticfunctions}`
        + `,\n${ii + s_iident}${memberfields}`
        + `,\n${ii + s_iident}${membermethods}`
        + `,\n${ii + s_iident}${this.iskeytype}`;
    }
}

abstract class TIREntityType extends TIROOType {
    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], iskeytype: boolean) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, iskeytype);
    }

    bsqemit_entitytype(ii: string): string {
        return this.bsqemit_ootype(ii);
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

    bsqemit(ii: string): string {
        const allfopts = "List{" + this.allfields.map((af) => `{fkey="${af.fkey}"ValidFieldKey, ftype="${af.ftype}"ValidFieldType}`).join(", ") + "}";
        
        const consinvopts = this.consinvariants.map((ci) => ci.bsqemit(ii + s_iident + s_iident));
        const consinvariants = consinvopts.length !== 0 ? `List{\n${ii + s_iident + s_iident}${consinvopts.join(`,\n${ii + s_iident + s_iident}`)}\n${ii + s_iident}}` : "List{}";

        const apivalidateopts = this.apivalidates.map((av) => av.bsqemit(ii + s_iident + s_iident));
        const apivalidates = apivalidateopts.length !== 0 ? `List{\n${ii + s_iident + s_iident}${apivalidateopts.join(`,\n${ii + s_iident + s_iident}`)}\n${ii + s_iident}}` : "List{}";

        const vtableopts = "Map{" + [...this.vtable].map((v) => `"${v[0]}"ValidIdentifier => "${v[1]}"ValidInvokeKey`).join(", ") + "}";
        const bindopts = "Map{" + [...this.binds].map((b) => `"${b[0]}" => "${b[1]}"ValidTypeKey`).join(", ") + "}";

        return this.bsqemit_entitytype(ii)
        + `,\n${ii + s_iident}${allfopts}`
        + `,\n${ii + s_iident}${consinvariants}`
        + `,\n${ii + s_iident}${apivalidates}`
        + `,\n${ii + s_iident}${vtableopts}`
        + `,\n${ii + s_iident}${bindopts}`
        + `\n${ii}}`;
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

    bsqemit(ii: string): string {
        const valmap = `Map{\n${ii + s_iident + s_iident}` + [...this.litvals].map((x) => `"${x[0]}"ValidIdentifier => ${x[1].bsqemit(ii + s_iident + s_iident)}`).join(", ") + `\n${ii + s_iident}}`;
        return this.bsqemit_entitytype(ii)
        + `,\n${ii + s_iident}List{${this.enums.map((e) => `"${e}"ValidIdentifier`).join(", ")}}`
        + `,\n${ii + s_iident}${valmap}`
        + `\n${ii}}`;
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

    bsqemit(ii: string): string {
        const consinvallopts = this.consinvariantsall.map((ci) => ci.bsqemit(ii + s_iident + s_iident));
        const consinvariantsall = consinvallopts.length !== 0 ? `List{\n${ii + s_iident + s_iident}${consinvallopts.join(`,\n${ii + s_iident + s_iident}`)}\n${ii + s_iident}}` : "List{}";

        const consinvexplicitopts = this.consinvariantsall.map((ci) => ci.bsqemit(ii + s_iident + s_iident));
        const consinvariantsexplicit = consinvexplicitopts.length !== 0 ? `List{\n${ii + s_iident + s_iident}${consinvexplicitopts.join(`,\n${ii + s_iident + s_iident}`)}\n${ii + s_iident}}` : "List{}";


        const apivalidateopts = this.apivalidates.map((av) => av.bsqemit(ii + s_iident + s_iident));
        const apivalidates = apivalidateopts.length !== 0 ? `List{\n${ii + s_iident + s_iident}${apivalidateopts.join(`,\n${ii + s_iident + s_iident}`)}\n${ii + s_iident}}` : "List{}";

        const strvalidator = this.strvalidator !== undefined ? this.strvalidator.vre.bsqemit(ii + s_iident + s_iident) : "none";
        const pthvalidator = this.pthvalidator !== undefined ? this.pthvalidator.vpth.bsqemit(ii + s_iident + s_iident) : "none";

        return this.bsqemit_entitytype(ii)
        + `,\n${ii + s_iident}${this.valuetype}ValidTypeKey`
        + `,\n${ii + s_iident}${this.representation}ValidTypeKey`
        + `,\n${ii + s_iident}${consinvariantsall}`
        + `,\n${ii + s_iident}${consinvariantsexplicit}`
        + `,\n${ii + s_iident}${apivalidates}`
        + `,\n${ii + s_iident}${strvalidator}`
        + `,\n${ii + s_iident}${pthvalidator}`
        + `\n${ii}}`;
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

    bsqemit(ii: string): string {
        return ["TreeIR::PrimitiveInternalEntityType", this.bsqemit_internalentity()];
    }
}

//class representing Validator regex types
class TIRValidatorEntityType extends TIRInternalEntityType {
    readonly revalidator: BSQRegex;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], revalidator: BSQRegex) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false);
        this.revalidator = revalidator;
    }

    bsqemit(ii: string): string {
        return ["TreeIR::ValidatorEntityType", { ...this.bsqemit_internalentity(), revalidator: this.revalidator.jemit() }];
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

    bsqemit(ii: string): string {
        return ["TreeIR::StringOfEntityType", { ...this.bsqemit_internalentity(), validatortype: this.validatortype, revalidator: this.revalidator.jemit() }];
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

    bsqemit(ii: string): string {
        return ["TreeIR::ASCIIStringOfEntityType", { ...this.bsqemit_internalentity(), validatortype: this.validatortype, revalidator: this.revalidator.jemit() }];
    }
}

//class representing PathValidator types
class TIRPathValidatorEntityType extends TIRInternalEntityType {
    readonly pthvalidator: BSQPathValidator;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], pthvalidator: BSQPathValidator) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false);
        this.pthvalidator = pthvalidator;
    }

    bsqemit(ii: string): string {
        return ["TreeIR::PathValidatorEntityType", { ...this.bsqemit_internalentity(), pthvalidator: this.pthvalidator.jemit() }];
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

    bsqemit(ii: string): string {
        return ["TreeIR::PathEntityType", { ...this.bsqemit_internalentity(), validatortype: this.validatortype, pthvalidator: this.pthvalidator.jemit() }];
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

    bsqemit(ii: string): string {
        return ["TreeIR::PathFragmentEntityType", { ...this.bsqemit_internalentity(), validatortype: this.validatortype, pthvalidator: this.pthvalidator.jemit() }];
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

    bsqemit(ii: string): string {
        return ["TreeIR::PathGlobEntityType", { ...this.bsqemit_internalentity(), validatortype: this.validatortype, pthvalidator: this.pthvalidator.jemit() }];
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

    bsqemit(ii: string): string {
        return ["TreeIR::OkEntityType", { ...this.bsqemit_constructable(), typeT: this.typeT, typeE: this.typeE }];
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

    bsqemit(ii: string): string {
        return ["TreeIR::ErrEntityType", { ...this.bsqemit_constructable(), typeT: this.typeT, typeE: this.typeE }];
    }
}

class TIRSomethingEntityType extends TIRConstructableEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes);
        this.typeT = typeT;
    }

    bsqemit(ii: string): string {
        return ["TreeIR::SomethingEntityType", { ...this.bsqemit_constructable(), typeT: this.typeT }];
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

    bsqemit(ii: string): string {
        return ["TreeIR::MapEntryEntityType", { ...this.bsqemit_constructable(), typeK: this.typeK, typeV: this.typeV }];
    }
}

//class representing special havoc type
class TIRHavocEntityType extends TIRInternalEntityType {
    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[]) {
        super(tkey, tname, srcInfo, srcFile, attributes, [], false);
    }

    bsqemit(ii: string): string {
        return ["TreeIR::HavocEntityType", this.bsqemit_internalentity()];
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

    bsqemit(ii: string): string {
        return ["TreeIR::ListEntityType", { ...this.bsqemit_collection(), typeT: this.typeT }];
    }
}

//class representing Stack<T>
class TIRStackEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes);
        this.typeT = typeT;
    }

    bsqemit(ii: string): string {
        return ["TreeIR::StackEntityType", { ...this.bsqemit_collection(), typeT: this.typeT }];
    }
}

//class representing Queue<T>
class TIRQueueEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes);
        this.typeT = typeT;
    }

    bsqemit(ii: string): string {
        return ["TreeIR::QueueEntityType", { ...this.bsqemit_collection(), typeT: this.typeT }];
    }
}

//class representing Set<T>
class TIRSetEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], typeT: TIRTypeKey) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes);
        this.typeT = typeT;
    }

    bsqemit(ii: string): string {
        return ["TreeIR::SetEntityType", { ...this.bsqemit_collection(), typeT: this.typeT }];
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

    bsqemit(ii: string): string {
        return ["TreeIR::MapEntityType", { ...this.bsqemit_collection(), typeK: this.typeK, typeV: this.typeV }];
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

    bsqemit(ii: string): string {
        return ["TreeIR::TaskType", { ...this.bsqemit_ootype(), binds: [...this.binds], controls: this.controls.map((cc) => ({ val: cc.val ? cc.val.bsqemit() : null, cname: cc.cname })), actions: this.actions, mainfunc: this.mainfunc, onfuncs: { onCancel: this.onfuncs.onCanel || null, onFailure: this.onfuncs.onFailure || null, onTimeout: this.onfuncs.onTimeout || null }, lfuncs: { logStart: this.lfuncs.logStart || null, logEnd: this.lfuncs.logEnd || null, taskEnsures: this.lfuncs.taskEnsures || null, taskWarns: this.lfuncs.taskWarns || null }, statuseffect: this.statuseffect.bsqemit(), eventeffect: this.eventeffect.bsqemit(), enveffect: this.enveffect.bsqemit(), resourceeffect: this.resourceeffect.map((eff) => eff.bsqemit()), tskensures: this.ensures.map((ee) => ee.bsqemit()) }];
    }
}

class TIRConceptType extends TIROOType {
    readonly binds: Map<string, TIRTypeKey>;

    constructor(tkey: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], supertypes: TIRTypeKey[], binds: Map<string, TIRTypeKey>) {
        super(tkey, tname, srcInfo, srcFile, attributes, supertypes, false);
        this.binds = binds;
    }

    bsqemit(ii: string): string {
        return ["TreeIR::ConceptType", { ...this.bsqemit_ootype(), binds: [...this.binds] }];
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

    bsqemit(ii: string): string {
        return ["TreeIR::ConceptSetType", { ...this.bsqemit_type(), conceptTypes: this.conceptTypes }];
    }
}

class TIRTupleType extends TIRType {
    readonly types: TIRTypeKey[];

    constructor(tkey: TIRTypeKey, types: TIRTypeKey[], supertypes: TIRTypeKey[]) {
        super(tkey, supertypes);
        this.types = types;
    }

    bsqemit(ii: string): string {
        return ["TreeIR::TupleType", { ...this.bsqemit_type(), types: this.types }];
    }
}

class TIRRecordType extends TIRType {
    readonly entries: { pname: string, ptype: TIRTypeKey }[];

    constructor(tkey: TIRTypeKey, entries: { pname: string, ptype: TIRTypeKey }[], supertypes: TIRTypeKey[]) {
        super(tkey, supertypes);
        this.entries = entries;
    }

    bsqemit(ii: string): string {
        return ["TreeIR::RecordType", { ...this.bsqemit_type(), entries: this.entries }];
    }
}

class TIRUnionType extends TIRType {
    readonly options: TIRTypeKey[];

    constructor(tkey: TIRTypeKey, options: TIRTypeKey[]) {
        super(tkey, undefined);
        this.options = options;
    }

    bsqemit(ii: string): string {
        return ["TreeIR::UnionType", { ...this.bsqemit_type(), options: this.options }];
    }
}

class TIREListType extends TIRType {
    readonly types: TIRTypeKey[];

    constructor(tkey: TIRTypeKey, types: TIRTypeKey[]) {
        super(tkey, undefined);
        this.types = types;
    }

    bsqemit(ii: string): string {
        return ["TreeIR::EListType", { ...this.bsqemit_type(), types: this.types }];
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

    bsqemit(ii: string): string {
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

    bsqemit(ii: string): string {
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

    bsqemit(ii: string): string {
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

    bsqemit(ii: string): string {
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

    bsqemit(ii: string): string { {
        return ["TreeIR::CodePack", { ns: this.ns, codekey: this.codekey, invk: this.invk, isrecursive: this.recursive, terms: this.terms, pcodes: this.pcodes, capturedValues: this.capturedValues, capturedCodePacks: this.capturedCodePacks }];
    }
    static bsqparse(jv: any): TIRCodePack {
        assert(Array.isArray(jv) && jv[0] === "TreeIR::CodePack", "CodePack");
        return new TIRCodePack(jv[1].ns, jv[1].codekey, jv[1].invk, jv[1].isrecursive, jv[1].terms, jv[1].pcodes, jv[1].capturedValues, jv[1].capturedCodePacks);
    }
}

abstract class TIRInfoTemplate {
    abstract bsqemit(ii: string): string;
}

class TIRInfoTemplateRecord extends TIRInfoTemplate {
    readonly entries: { name: string, value: TIRInfoTemplate }[];

    constructor(entries: { name: string, value: TIRInfoTemplate }[]) {
        super();
        this.entries = entries;
    }

    bsqemit(ii: string): string {
        return ["TreeIR::InfoTemplateRecord", { entries: this.entries.map((e) => ({ name: e.name, value: e.value.bsqemit() })) }];
    }
}

class TIRInfoTemplateTuple extends TIRInfoTemplate {
    readonly entries: TIRInfoTemplate[];

    constructor(entries: TIRInfoTemplate[]) {
        super();
        this.entries = entries;
    }

    bsqemit(ii: string): string {
        return ["TreeIR::InfoTemplateTuple", { entries: this.entries.map((e) => e.bsqemit()) }];
    }
}

class TIRInfoTemplateConst extends TIRInfoTemplate {
    readonly litexp: TIRLiteralValue;

    constructor(litexp: TIRLiteralValue) {
        super();
        this.litexp = litexp;
    }

    bsqemit(ii: string): string {
        return ["TreeIR::InfoTemplateConst", { litexp: this.litexp.bsqemit() }];
    }
}

class TIRInfoTemplateMacro extends TIRInfoTemplate {
    readonly macro: string;

    constructor(macro: string) {
        super();
        this.macro = macro;
    }

    bsqemit(ii: string): string {
        return ["TreeIR::InfoTemplateMacro", { macro: this.macro }];
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

    bsqemit(ii: string): string {
        return ["TreeIR::InfoTemplateValue", { argpos: this.argpos, argtype: this.argtype }];
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

    bsqemit(ii: string): string {
        return ["TreeIR::StringTemplate", { str: this.str }];
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

    bsqemit(ii: string): string {
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
                return [...tdecl.supertypes].some((st) => this.isConcreteSubtypeOf(st, oftype));
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

    bsqemit(ii: string): string {
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
}

export {
    TIRTypeName,
    TIRTypeKey, TIRInvokeKey, TIRFieldKey, TIRPCodeKey,
    TIRFunctionParameter,
    TIRObjectInvariantDecl, TIRObjectValidateDecl, TIRTypedeclInvariantDecl, TIRTypedeclValidateDecl,
    TIRTaskStatusEffect, TIRTaskEventEffect, TIRTaskEnvironmentEffect, TIRTaskResourceEffect, TIRTaskEnsures,
    TIRInvoke, TIRPreConditionDecl, TIRPostConditionDecl, TIRInvokeSampleDeclInline, TIRInvokeSampleDeclFile, TIRInvokeAbstractDeclaration, TIRInvokeImplementation, TIRInvokeSynthesis, TIRInvokePrimitive,
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
