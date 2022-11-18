
import { TIRExpression, TIRLiteralValue } from "./tir_body";

import { SourceInfo } from "../build_decls";
import { BSQRegex } from "../bsqregex";
import { PathValidator } from "../path_validator";
import * as assert from "assert";

class TIRTypeName {
    readonly ns: string;
    readonly name: string;
    readonly templates: TIRTypeKey[] | undefined;

    constructor(ns: string, name: string, templates?: TIRTypeKey[] | undefined) {
        this.ns = ns;
        this.name = name;
        this.templates = templates || [];
    }
}

class TIRNamespaceMemberName {
    readonly ns: string;
    readonly name: string;

    constructor(ns: string, name: string) {
        this.ns = ns;
        this.name = name;
    }
}

class TIRTypeMemberName {
    readonly tname: TIRTypeName;
    readonly name: string;
    readonly templates: string[] | undefined;

    constructor(tname: TIRTypeName, name: string, templates?: string[] | undefined) {
        this.tname = tname;
        this.name = name;
        this.templates = templates || [];
    }
}

type TIRTypeKey = string;

type TIRNamespaceConstKey = string;
type TIRMemberConstKey = string;
type TIRLitKey = string;

type TIRInvokeKey = string;
type TIRPropertyKey = string;
type TIRFieldKey = string;

type TIRTupleIndex = number;


class TIRFunctionParameter {
    readonly name: string;
    readonly type: TIRTypeKey;
    readonly litexp: {val: TIRLiteralValue, vkey: TIRLitKey | undefined} | undefined;

    constructor(name: string, type: TIRTypeKey, litexp: TIRLiteralValue | undefined) {
        this.name = name;
        this.type = type;
        this.litexp = litexp;
    }
}

class TIRPreConditionDecl {
    readonly invkey: TIRInvokeKey; //The invoke key that is assoicated with this expression -- e.g. you can call this function to check the expression
    readonly exp: TIRExpression;
    readonly args: TIRFunctionParameter[];

    constructor(invkey: TIRInvokeKey, exp: TIRExpression, args: TIRFunctionParameter[]) {
        this.invkey = invkey;
        this.exp = exp;
        this.args = args;
    }
}

class TIRPostConditionDecl {
    readonly invkey: TIRInvokeKey; //The invoke key that is assoicated with this expression -- e.g. you can call this function to check the expression
    readonly exp: TIRExpression;
    readonly args: TIRFunctionParameter[];
    readonly origargs: TIRFunctionParameter[];

    constructor(invkey: TIRInvokeKey, exp: TIRExpression, args: TIRFunctionParameter[], origargs: TIRFunctionParameter[]) {
        this.invkey = invkey;
        this.exp = exp;
        this.args = args;
        this.origargs = origargs;
    }
}

class TIRInvariantDecl {
    readonly invkey: TIRInvokeKey; //The invoke key that is assoicated with this expression -- e.g. you can call this function to check the expression
    readonly exp: TIRExpression;
    readonly args: TIRFunctionParameter[];

    constructor(invkey: TIRInvokeKey, exp: TIRExpression, args: TIRFunctionParameter[]) {
        this.invkey = invkey;
        this.exp = exp;
        this.args = args;
    }
}

class TIRValidateDecl {
    readonly invkey: TIRInvokeKey; //The invoke key that is assoicated with this expression -- e.g. you can call this function to check the expression
    readonly exp: TIRExpression;
    readonly args: TIRFunctionParameter[];

    constructor(invkey: TIRInvokeKey, exp: TIRExpression, args: TIRFunctionParameter[]) {
        this.invkey = invkey;
        this.exp = exp;
        this.args = args;
    }
}

enum TIRTaskEffectFlag {
    Status,
    Event,
    Resource,
    Environment
}

class TIRTaskEnvironmentEffect {
    readonly evar: string; //string "*" is wildcard
    readonly isread: boolean;
    readonly iswrite: boolean;

    constructor(evar: string, isread: boolean, iswrite: boolean) {
        this.evar = evar;
        this.isread = isread;
        this.iswrite = iswrite;
    }
}

class TIRTaskResourceEffect {
    readonly pathdescriptor: TIRTypeKey; //the resource validator
    readonly isread: boolean;
    readonly iswrite: boolean;

    readonly invkey: TIRInvokeKey; //The invoke key that is assoicated with this expression -- e.g. you can call this function to check the expression
    readonly pathglob: TIRExpression | undefined; //returns a glob string of type PathGlob<pathdescriptor>
    readonly args: TIRFunctionParameter[];

    constructor(pathdescriptor: TIRTypeKey,  isread: boolean, iswrite: boolean, invkey: TIRInvokeKey, pathglob: TIRExpression | undefined, args: TIRFunctionParameter[]) {
        this.pathdescriptor = pathdescriptor;
        this.isread = isread;
        this.iswrite = iswrite;

        this.invkey = invkey;
        this.pathglob = pathglob;
        this.args = args;
    }
}

class TIRTaskEnsures {
    readonly sinfo: SourceInfo;
    readonly invkey: TIRInvokeKey; //The invoke key that is assoicated with this expression -- e.g. you can call this function to check the expression
    readonly exp: TIRExpression;
    readonly args: TIRFunctionParameter[];

    constructor(sinfo: SourceInfo, invkey: TIRInvokeKey, exp: TIRExpression, args: TIRFunctionParameter[]) {
        this.sinfo = sinfo;
        this.invkey = invkey;
        this.exp = exp;
        this.args = args;
    }
}

class TIRInvokeDecl {
    readonly invkey: TIRInvokeKey;
    readonly iname: TIRNamespaceMemberName | TIRTypeMemberName;
    readonly name: string;

    readonly startSourceLocation: SourceInfo;
    readonly endSourceLocation: SourceInfo;
    readonly srcFile: string;
    readonly bodyID: string;

    readonly attributes: string[];
    readonly recursive: boolean;

    readonly isMemberMethod: boolean;
    readonly isVirtual: boolean;
    readonly isDynamicOperator: boolean;
    readonly isLambda: boolean;

    readonly isThisRef: boolean;
    readonly params: TIRFunctionParameter[];
    
    readonly resultType: TIRTypeKey;

    readonly preconditions: TIRPreConditionDecl[];
    readonly postconditions: TIRPostConditionDecl[];

    readonly body: TIRBodyImplementation;

    constructor(invkey: TIRInvokeKey, iname: TIRNamespaceMemberName | TIRTypeMemberName, name: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, bodyID: string, srcFile: string, attributes: string[], recursive: boolean, isMemberMethod: boolean, isVirtual: boolean, isDynamicOperator: boolean, isLambda: boolean, params: TIRFunctionParameter[], isThisRef: boolean, resultType: TIRTypeKey, preconds: TIRPreConditionDecl[], postconds: TIRPostConditionDecl[], body: TIRBodyImplementation) {
        this.invkey = invkey;
        this.iname = iname;
        this.name = name;

        this.startSourceLocation = sinfoStart;
        this.endSourceLocation = sinfoEnd;
        this.srcFile = srcFile;
        this.bodyID = bodyID;

        this.attributes = attributes;
        this.recursive = recursive;

        this.isMemberMethod = isMemberMethod;
        this.isVirtual = isVirtual;
        this.isDynamicOperator = isDynamicOperator;
        this.isLambda = isLambda;

        this.isThisRef = isThisRef;
        this.params = params;

        this.resultType = resultType;

        this.preconditions = preconds;
        this.postconditions = postconds;

        this.body = body;
    }
}

class TIRConstMemberDecl {
    readonly ckey: TIRMemberConstKey;
    readonly cname: TIRTypeMemberName;
    readonly name: string;
    readonly defin: TIRTypeKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];

    readonly declaredType: TIRTypeKey;
    readonly value: TIRExpression;

    readonly invkey: TIRInvokeKey; //The invoke key that is assoicated with this expression -- e.g. you can call this function to check the expression

    constructor(ckey: TIRMemberConstKey, cname: TIRTypeMemberName, name: string, defin: TIRTypeKey, srcInfo: SourceInfo, srcFile: string, attributes: string[], declaredtype: TIRTypeKey, value: TIRExpression, invkey: TIRInvokeKey) {
        this.ckey = ckey;
        this.cname = cname;
        this.name = name;
        this.defin = defin;
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.declaredType = declaredtype;
        this.value = value;
        this.invkey = invkey;
    }
}

class TIRStaticFunctionDecl {
    readonly ikey: TIRInvokeKey;
    readonly fname: TIRTypeMemberName;
    readonly name: string;
    readonly defin: TIRTypeKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly invoke: TIRInvokeDecl;

    constructor(defin: TIRTypeKey, sinfo: SourceInfo, srcFile: string, invoke: TIRInvokeDecl) {
        this.ikey = invoke.invkey;
        this.fname = invoke.iname as TIRTypeMemberName;
        this.name = invoke.name;
        this.defin = defin;
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.attributes = invoke.attributes;
        this.invoke = invoke;
    }
}

class TIRMemberFieldDecl {
    readonly fkey: TIRFieldKey;
    readonly fname: TIRTypeMemberName;
    readonly name: string;
    readonly defin: TIRTypeKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];

    readonly declaredType: TIRTypeKey;

    constructor(fkey: TIRFieldKey, fname: TIRTypeMemberName, name: string, defin: TIRTypeKey, srcInfo: SourceInfo, srcFile: string, attributes: string[], declaredtype: TIRTypeKey) {
        this.fkey = fkey;
        this.fname = fname;
        this.name = name;
        this.defin = defin;
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.declaredType = declaredtype;
    }
}

class TIRMemberMethodDecl {
    readonly ikey: TIRInvokeKey;
    readonly mname: TIRTypeMemberName;
    readonly name: string;
    readonly defin: TIRTypeKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly invoke: TIRInvokeDecl;

    constructor(defin: TIRTypeKey, sinfo: SourceInfo, srcFile: string, invoke: TIRInvokeDecl) {
        this.ikey = invoke.invkey;
        this.mname = invoke.iname as TIRTypeMemberName;
        this.name = invoke.name;
        this.defin = defin;
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.attributes = invoke.attributes;
        this.invoke = invoke;
    }
}

abstract class TIRType {
    readonly tid: TIRTypeKey;

    constructor(tid: TIRTypeKey) {
        this.tid = tid;
    }
}

class TIRLiteralType extends TIRType {
    readonly lexp: TIRLiteralValue;

    constructor(tid: TIRTypeKey, lexp: TIRLiteralValue) {
        super(tid);
        this.lexp = lexp;
    }
}

abstract class TIROOType extends TIRType {
    readonly tname: TIRTypeName;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];

    //declared provides -- not saturated set
    readonly provides: TIRTypeKey[];

    //Members that are declared on this
    readonly invariants: TIRInvariantDecl[]; 
    readonly validates: TIRValidateDecl[];

    readonly constMembers: TIRConstMemberDecl[];
    readonly staticFunctions: TIRStaticFunctionDecl[];
    readonly memberFields: TIRMemberFieldDecl[];
    readonly memberMethods: TIRMemberMethodDecl[];

    readonly allfields: {fkey: TIRFieldKey, ftype: TIRTypeKey}[];

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberFields: TIRMemberFieldDecl[], memberMethods: TIRMemberMethodDecl[], invariants: TIRInvariantDecl[], validates: TIRValidateDecl[], allfields: {fkey: TIRFieldKey, ftype: TIRTypeKey}[]) {
        super(tid);
        this.tname = tname;
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.provides = provides;
        this.invariants = invariants;
        this.validates = validates;
        this.constMembers = constMembers;
        this.staticFunctions = staticFunctions;
        this.memberFields = memberFields;
        this.memberMethods = memberMethods;
        this.allfields = allfields;
    }
}

abstract class TIREntityType extends TIROOType {
    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberFields: TIRMemberFieldDecl[], memberMethods: TIRMemberMethodDecl[], invariants: TIRInvariantDecl[], validates: TIRValidateDecl[], allfields: {fkey: TIRFieldKey, ftype: TIRTypeKey}[]) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, memberFields, memberMethods, invariants, validates, allfields);
    }
}

//Represents types declared as entities in the code
class TIRObjectEntityType extends TIREntityType {
    readonly consinvariants: {invk: TIRInvokeKey, args: {fkey: TIRFieldKey, argidx: number, ftype: TIRTypeKey}[]}[]; 
    readonly apivalidates: {invk: TIRInvokeKey, args: {fkey: TIRFieldKey, argidx: number, ftype: TIRTypeKey}[]}[];
    readonly vtable: Map<string, TIRInvokeKey>; 
    readonly binds: Map<string, TIRTypeKey>;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberFields: TIRMemberFieldDecl[], memberMethods: TIRMemberMethodDecl[], invariants: TIRInvariantDecl[], validates: TIRValidateDecl[], consinvariants: {invk: TIRInvokeKey, args: {fkey: TIRFieldKey, argidx: number, ftype: TIRTypeKey}[]}[], apivalidates: {invk: TIRInvokeKey, args: {fkey: TIRFieldKey, argidx: number, ftype: TIRTypeKey}[]}[], vtable: Map<string, TIRInvokeKey>, allfields: {fkey: TIRFieldKey, ftype: TIRTypeKey}[], binds: Map<string, TIRTypeKey>) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, memberFields, memberMethods, invariants, validates, allfields);
        this.consinvariants = consinvariants;
        this.apivalidates = apivalidates;
        this.vtable = vtable;
        this.binds = binds;
    }
}

//Represents enum types declared as entities in the code
class TIREnumEntityType extends TIREntityType {
    readonly enums: {ename: string, value: TIRLiteralValue, reprtype: TIRTypeKey}[];

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], enums: {ename: string, value: TIRLiteralValue, reprtype: TIRTypeKey}[]) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods, [], [], []);
        this.enums = enums;
    }
}

//Represents typedecl T = X ... types where the representation is a single primitve typed value
class TIRTypedeclEntityType extends TIREntityType {
    readonly valuetype: TIRTypeKey; //result of .value()
    readonly representation: TIRTypeKey; //result of getUnderlyingRepresentation opcode -- a TIRResolvedPrimitiveInternalEntityAtomType

    readonly consinvariantsall: {invk: TIRInvokeKey, vtype: TIRTypeKey}[]; 
    readonly consinvariantsexplicit: {invk: TIRInvokeKey, vtype: TIRTypeKey}[]; 
    readonly apivalidates: {invk: TIRInvokeKey, vtype: TIRTypeKey}[];

    readonly strvalidator: {vtype: TIRTypeKey, vre: BSQRegex} | undefined; //TIRValidatorEntityType;
    readonly pthvalidator: {vtype: TIRTypeKey, vpth: PathValidator} | undefined; //TIRPathValidatorEntityType;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], invariants: TIRInvariantDecl[], validates: TIRValidateDecl[], consinvariantsall: {invk: TIRInvokeKey, vtype: TIRTypeKey}[], consinvariantsexplicit: {invk: TIRInvokeKey, vtype: TIRTypeKey}[], apivalidates: {invk: TIRInvokeKey, vtype: TIRTypeKey}[], valuetype: TIRTypeKey, representation: TIRTypeKey, strvalidator: {vtype: TIRTypeKey, vre: BSQRegex} | undefined, pthvalidator: {vtype: TIRTypeKey, vpth: PathValidator} | undefined) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods, invariants, validates, []);
        this.valuetype = valuetype;
        this.representation = representation;
        this.consinvariantsall = consinvariantsall;
        this.consinvariantsexplicit = consinvariantsexplicit;
        this.apivalidates = apivalidates;
        this.strvalidator = strvalidator;
        this.pthvalidator = pthvalidator;
    }
}

//base class for all the primitive types that are defined
abstract class TIRInternalEntityType extends TIREntityType {
    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberFields: TIRMemberFieldDecl[], memberMethods: TIRMemberMethodDecl[]) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, memberFields, memberMethods, [], [], []);
    }
} 

//class representing all the primitive values (Int, Bool, String, ...). ALl of these are special implemented values
class TIRPrimitiveInternalEntityType extends TIRInternalEntityType {
    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[]) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods);
    }
} 

//class representing Validator regex types
class TIRValidatorEntityType extends TIRInternalEntityType {
    readonly revalidator: BSQRegex;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], staticFunctions: TIRStaticFunctionDecl[], revalidator: BSQRegex) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, [], staticFunctions, [], []);
        this.revalidator = revalidator;
    }
}

//class representing StringOf<T> types
class TIRStringOfEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey; //TIRValidatorEntityType;
    readonly revalidator: BSQRegex;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], validatortype: TIRTypeKey, revalidator: BSQRegex) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods);
        this.validatortype = validatortype;
        this.revalidator = revalidator;
    }
}

//class representing ASCIIStringOf<T> types
class TIRASCIIStringOfEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey; //TIRValidatorEntityType;
    readonly revalidator: BSQRegex;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], validatortype: TIRTypeKey, revalidator: BSQRegex) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods);
        this.validatortype = validatortype;
        this.revalidator = revalidator;
    }
}

//class representing PathValidator types
class TIRPathValidatorEntityType extends TIRInternalEntityType {
    readonly pthvalidator: PathValidator;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], staticFunctions: TIRStaticFunctionDecl[], pthvalidator: PathValidator) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, [], staticFunctions, [], []);
        this.pthvalidator = pthvalidator;
    }
}

//class representing a Path<T> type
class TIRPathEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey //TIRPathValidatorEntityType;
    readonly pthvalidator: PathValidator;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], validatortype: TIRTypeKey, pthvalidator: PathValidator) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods);
        this.validatortype = validatortype;
        this.pthvalidator = pthvalidator;
    }
}

//class representing a PathFragment<T> type
class TIRPathFragmentEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey //TIRPathValidatorEntityType;
    readonly pthvalidator: PathValidator;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], validatortype: TIRTypeKey, pthvalidator: PathValidator) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods);
        this.validatortype = validatortype;
        this.pthvalidator = pthvalidator;
    }
}

class TIRPathGlobEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey //TIRPathValidatorEntityType;
    readonly pthvalidator: PathValidator;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], validatortype: TIRTypeKey, pthvalidator: PathValidator) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods);
        this.validatortype = validatortype;
        this.pthvalidator = pthvalidator;
    }
}

//class representing Ok, Err, Something types
abstract class TIRConstructableEntityType extends TIRInternalEntityType {
    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[]) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods);
    }
}

class TIROkEntityType extends TIRConstructableEntityType {
    readonly typeT: TIRTypeKey;
    readonly typeE: TIRTypeKey;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], typeT: TIRTypeKey, typeE: TIRTypeKey) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, memberMethods);
        this.typeT = typeT;
        this.typeE = typeE;
    }
}

class TIRErrEntityType extends TIRConstructableEntityType {
    readonly typeT: TIRTypeKey;
    readonly typeE: TIRTypeKey;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], typeT: TIRTypeKey, typeE: TIRTypeKey) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, memberMethods);
        this.typeT = typeT;
        this.typeE = typeE;
    }
}

class TIRSomethingEntityType extends TIRConstructableEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], typeT: TIRTypeKey) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, memberMethods);
        this.typeT = typeT;
    }
}

//class representing special havoc type
class TIRHavocEntityType extends TIRInternalEntityType {
    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[]) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, [], [], [], []);
    }
}

//abstract class for all the builtin collection types
abstract class TIRPrimitiveCollectionEntityType extends TIRInternalEntityType {
    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[]) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods);
    }
}

//class representing List<T>
class TIRListEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], typeT: TIRTypeKey) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, memberMethods);
        this.typeT = typeT;
    }
}

//class representing Stack<T>
class TIRStackEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], typeT: TIRTypeKey) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, memberMethods);
        this.typeT = typeT;
    }
}

//class representing Queue<T>
class TIRQueueEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], typeT: TIRTypeKey) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, memberMethods);
        this.typeT = typeT;
    }
}

//class representing Set<T>
class TIRSetEntityType extends TIRPrimitiveCollectionEntityType {
    readonly typeT: TIRTypeKey;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], typeT: TIRTypeKey) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, memberMethods);
        this.typeT = typeT;
    }
}

//class representing Map<K, V>
class TIRMapEntityTIRType extends TIRPrimitiveCollectionEntityType {
    readonly typeK: TIRTypeKey;
    readonly typeV: TIRTypeKey;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], typeK: TIRTypeKey, typeV: TIRTypeKey) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, memberMethods);
        this.typeK = typeK;
        this.typeV = typeV;
    }
}

class TIRTaskType extends TIROOType {
    readonly binds: Map<string, TIRTypeKey>;

    readonly defaults: {dkey: TIRMemberConstKey, dname: string}[]; //const members
    readonly actions: {akey: TIRInvokeKey, aname: string}[]; //methods
    readonly mainfunc: {mkey: TIRInvokeKey, mname: string}; //a static function
    readonly onfuncs: { onCanel: TIRInvokeKey | undefined, onFailure: TIRInvokeKey | undefined, onTimeout: TIRInvokeKey | undefined };

    readonly effects: TIRTaskEffectFlag[];
    readonly enveffect: TIRTaskEnvironmentEffect[];
    readonly resourceeffect: TIRTaskResourceEffect[];

    readonly ensures: TIRTaskEnsures[];

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberFields: TIRMemberFieldDecl[], memberMethods: TIRMemberMethodDecl[], 
        binds: Map<string, TIRTypeKey>, defaults: {dkey: TIRMemberConstKey, dname: string}[], actions: {akey: TIRInvokeKey, aname: string}[], mainfunc: {mkey: TIRInvokeKey, mname: string}, 
        onfuncs: { onCanel: TIRInvokeKey | undefined, onFailure: TIRInvokeKey | undefined, onTimeout: TIRInvokeKey | undefined },
        effects: TIRTaskEffectFlag[], enveffect: TIRTaskEnvironmentEffect[], resourceeffect: TIRTaskResourceEffect[], ensures: TIRTaskEnsures[]
    ) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, memberFields, memberMethods, [], [], []);
        this.binds = binds;
        this.defaults = defaults;
        this.actions = actions;
        this.mainfunc = mainfunc;
        this.onfuncs = onfuncs;
        this.effects = effects;
        this.enveffect = enveffect;
        this.resourceeffect = resourceeffect;
        this.ensures = ensures;
    }
}

class TIRConceptType extends TIROOType {
    readonly binds: Map<string, TIRTypeKey>;

    readonly subtypes: Set<TIRTypeKey>;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberFields: TIRMemberFieldDecl[], memberMethods: TIRMemberMethodDecl[], invariants: TIRInvariantDecl[], validates: TIRValidateDecl[], binds: Map<string, TIRTypeKey>, subtypes: Set<TIRTypeKey>, allfields: {fkey: TIRFieldKey, ftype: TIRTypeKey}[]) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, memberFields, memberMethods, invariants, validates, allfields);
        this.binds = binds;
        this.subtypes = subtypes;
    }

    isAnyConcept(): boolean {
        return this.tid === "Any";
    }

    isSomeConcept(): boolean {
        return this.tid === "Some";
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

    constructor(tid: TIRTypeKey, concepts: TIRTypeKey[]) {
        super(tid);
        this.conceptTypes = concepts;
    }
}

class TIRTupleType extends TIRType {
    readonly types: TIRTypeKey[];

    constructor(tid: TIRTypeKey, types: TIRTypeKey[]) {
        super(tid);
        this.types = types;
    }
}

class TIRRecordType extends TIRType {
    readonly entries: {pname: TIRPropertyKey, ptype: TIRTypeKey}[];

    constructor(tid: TIRTypeKey, entries: {pname: TIRPropertyKey, ptype: TIRTypeKey}[]) {
        super(tid);
        this.entries = entries;
    }
}

class TIREphemeralListType extends TIRType {
    readonly types: TIRTypeKey[];

    constructor(tid: TIRTypeKey, types: TIRTypeKey[]) {
        super(tid);
        this.types = types;
    }
}

class TIRUnionType extends TIRType {
    readonly options: TIRTypeKey[];

    constructor(tid: TIRTypeKey, options: TIRTypeKey[]) {
        super(tid);
        this.options = options;
    }
}

class TIRCodePackType extends TIRType {
    readonly invtarget: TIRInvokeKey;
    readonly callargs: TIRTypeKey[];
    readonly capturedargs: {argname: string, argtype: TIRTypeKey}[];
    readonly resulttype: TIRTypeKey;

    constructor(tid: TIRTypeKey, invtarget: TIRInvokeKey, callargs: TIRTypeKey[], capturedargs: {argname: string, argtype: TIRTypeKey}[], resulttype: TIRTypeKey) {
        super(tid);
        this.invtarget = invtarget;
        this.callargs = callargs;
        this.capturedargs = capturedargs;
        this.resulttype = resulttype;
    }
}

class TIRNamespaceConstDecl {
    readonly ckey: TIRNamespaceConstKey;
    readonly cname: TIRNamespaceMemberName;
    readonly name: string;
    readonly defin: string;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];

    readonly declaredType: TIRTypeKey;
    readonly value: TIRExpression;

    readonly invkey: TIRInvokeKey; //The invoke key that is assoicated with this expression -- e.g. you can call this function to check the expression

    constructor(ckey: TIRNamespaceConstKey, cname: TIRNamespaceMemberName, name: string, defin: string, srcInfo: SourceInfo, srcFile: string, attributes: string[], declaredtype: TIRTypeKey, value: TIRExpression, invkey: TIRInvokeKey) {
        this.ckey = ckey;
        this.cname = cname;
        this.name = name;
        this.defin = defin;
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.declaredType = declaredtype;
        this.value = value;
        this.invkey = invkey;
    }
}

class TIRNamespaceFunctionDecl {
    readonly ikey: TIRInvokeKey;
    readonly fname: TIRNamespaceMemberName;
    readonly name: string;
    readonly defin: string;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly invoke: TIRInvokeDecl;

    constructor(defin: string, sinfo: SourceInfo, srcFile: string, invoke: TIRInvokeDecl) {
        this.ikey = invoke.invkey;
        this.fname = invoke.iname as TIRNamespaceMemberName;
        this.name = invoke.name;
        this.defin = defin;
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.attributes = invoke.attributes;
        this.invoke = invoke;
    }
}

class TIRNamespaceOperatorDecl {
    readonly ikey: TIRInvokeKey;
    readonly fname: TIRNamespaceMemberName;
    readonly name: string;
    readonly defin: string;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly invoke: TIRInvokeDecl;

    constructor(defin: string, sinfo: SourceInfo, srcFile: string, invoke: TIRInvokeDecl) {
        this.ikey = invoke.invkey;
        this.fname = invoke.iname as TIRNamespaceMemberName;
        this.name = invoke.name;
        this.defin = defin;
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.attributes = invoke.attributes;
        this.invoke = invoke;
    }
}

class TIRInfoTemplate {
}

class TIRInfoTemplateRecord extends TIRInfoTemplate {
    readonly entries: { name: string, value: TIRInfoTemplate }[];

    constructor(entries: { name: string, value: TIRInfoTemplate }[]) {
        super();
        this.entries = entries;
    }
}

class TIRInfoTemplateTuple extends TIRInfoTemplate {
    readonly entries: TIRInfoTemplate[];

    constructor(entries: TIRInfoTemplate[]) {
        super();
        this.entries = entries;
    }
}

class TIRInfoTemplateConst extends TIRInfoTemplate {
    readonly litexp: {val: TIRLiteralValue, vkey: TIRLitKey | undefined};

    constructor(litexp: {val: TIRLiteralValue, vkey: TIRLitKey | undefined}) {
        super();
        this.litexp = litexp;
    }
}

class TIRInfoTemplateMacro extends TIRInfoTemplate {
    readonly macro: string;

    constructor(macro: string) {
        super();
        this.macro = macro;
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
}

class TIRStringTemplate {
    readonly str: string;

    //
    //TODO: want to pre-process this for formats and such
    //

    constructor(str: string) {
        this.str = str;
    }
}

class TIRNamespaceDeclaration {
    readonly ns: string;

    consts: Map<string, TIRNamespaceConstDecl>;
    functions: Map<string, TIRNamespaceFunctionDecl>;
    operators: Map<string, TIRNamespaceOperatorDecl[]>;
    concepts: Map<string, TIRTypeKey>;
    objects: Map<string, TIRTypeKey>;
    
    tasks: Map<string, TIRTypeKey>;
    msgformats: Map<string, TIRInfoTemplate>;
    stringformats: Map<string, TIRStringTemplate>;

    constructor(ns: string) {
        this.ns = ns;
        this.consts = new Map<string, TIRNamespaceConstDecl>();
        this.functions = new Map<string, TIRNamespaceFunctionDecl>();
        this.operators = new Map<string, TIRNamespaceOperatorDecl[]>();
        this.concepts = new Map<string, TIRTypeKey>();
        this.objects = new Map<string, TIRTypeKey>();

        this.tasks = new Map<string, TIRTypeKey>();
        this.msgformats = new Map<string, TIRInfoTemplate>();
        this.stringformats = new Map<string, TIRStringTemplate>();
    }
}

class TIRAssembly {
    readonly namespaceMap: Map<string, TIRNamespaceDeclaration> = new Map<string, TIRNamespaceDeclaration>();
    readonly typeMap: Map<TIRTypeKey, TIRType> = new Map<TIRTypeKey, TIRType>();

    readonly literalRegexs: BSQRegex[] = [];
    readonly validatorRegexs: Map<string, BSQRegex> = new Map<string, BSQRegex>();
    readonly validatorPaths: Map<string, PathValidator> = new Map<string, PathValidator>();

    getNamespace(ns: string): TIRNamespaceDeclaration {
        assert(this.namespaceMap.has(ns), "Missing namespace?");
        return this.namespaceMap.get(ns) as TIRNamespaceDeclaration;
    }

    getTypeAs<T extends TIRType>(tkey: TIRTypeKey): T {
        assert(this.typeMap.has(tkey), "Missing type");
        return this.typeMap.get(tkey) as T;
    }
}

export {
    TIRTypeName, TIRNamespaceMemberName, TIRTypeMemberName, TIRNamespaceConstKey, TIRMemberConstKey,
    TIRTypeKey, TIRInvokeKey, TIRPropertyKey, TIRFieldKey, TIRTupleIndex,
    TIRFunctionParameter,
    TIRInvariantDecl, TIRValidateDecl,
    TIRTaskEffectFlag, TIRTaskEnvironmentEffect, TIRTaskResourceEffect, TIRTaskEnsures,
    TIRInvokeDecl,
    TIRConstMemberDecl, TIRStaticFunctionDecl, TIRMemberFieldDecl, TIRMemberMethodDecl,
    TIRType,
    TIRLiteralType,
    TIROOType, TIREntityType, TIRObjectEntityType, TIREnumEntityType, TIRTypedeclEntityType, TIRInternalEntityType, TIRPrimitiveInternalEntityType,
    TIRValidatorEntityType, TIRStringOfEntityType, TIRASCIIStringOfEntityType,
    TIRPathValidatorEntityType, TIRPathEntityType, TIRPathFragmentEntityType, TIRPathGlobEntityType,
    TIRConstructableEntityType, TIROkEntityType, TIRErrEntityType, TIRSomethingEntityType,
    TIRHavocEntityType,
    TIRPrimitiveCollectionEntityType, TIRListEntityType, TIRStackEntityType, TIRQueueEntityType, TIRSetEntityType, TIRMapEntityTIRType,
    TIRTaskType,
    TIRConceptType, TIRConceptSetType,
    TIRTupleType, TIRRecordType,
    TIREphemeralListType,
    TIRCodePackType,
    TIRUnionType,
    TIRInfoTemplate, TIRInfoTemplateRecord, TIRInfoTemplateTuple, TIRInfoTemplateConst, TIRInfoTemplateMacro, TIRInfoTemplateValue,
    TIRStringTemplate,
    TIRNamespaceConstDecl, TIRNamespaceFunctionDecl,
    TIRNamespaceDeclaration,
    TIRAssembly
};