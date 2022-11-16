import { TIRExpression, TIRLiteralValue } from "./tir_body";
import { SourceInfo } from "../build_decls";

class TIRTypeName {
    readonly ns: string;
    readonly names: string[];
    readonly templates: string[] | undefined;

    constructor(ns: string, names: string[], templates?: string[] | undefined) {
        this.ns = ns;
        this.names = names;
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

type TIRNameSpaceConstKey = string;
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
    readonly cmkey: TIRMemberConstKey; //The special storage name for the value

    constructor(ckey: TIRMemberConstKey, cname: TIRTypeMemberName, name: string, defin: TIRTypeKey, srcInfo: SourceInfo, srcFile: string, attributes: string[], declaredtype: TIRTypeKey, value: TIRExpression, invkey: TIRInvokeKey, cmkey: TIRMemberConstKey) {
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
        this.cmkey = cmkey;
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
    readonly tname: TIRTypeName;

    constructor(tid: TIRTypeKey, tname: TIRTypeName) {
        this.tid = tid;
        this.tname = tname;
    }
}

class TIRLiteralType extends TIRType {
    readonly lexp: TIRLiteralValue;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, lexp: TIRLiteralValue) {
        super(tid, tname);
        this.lexp = lexp;
    }
}

abstract class TIREntityType extends TIRType {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];

    //declared provides -- not saturated set
    readonly provides: TIRTypeKey[];

    //Members that are declared on this
    readonly constMembers: TIRConstMemberDecl[];
    readonly staticFunctions: TIRStaticFunctionDecl[];
    readonly memberFields: TIRMemberFieldDecl[];
    readonly memberMethods: TIRMemberMethodDecl[];

    //saturated lookup info -- includes super types as well
    readonly invariants: TIRInvariantDecl[]; 
    readonly validates: TIRValidateDecl[];

    readonly vtable: Map<string, TIRInvokeKey>; 
    readonly allfields: TIRFieldKey[];

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberFields: TIRMemberFieldDecl[], memberMethods: TIRMemberMethodDecl[], invariants: TIRInvariantDecl[], validates: TIRValidateDecl[], vtable: Map<string, TIRInvokeKey>, allfields: TIRFieldKey[]) {
        super(tid, tname);
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.provides = provides;
        this.constMembers = constMembers;
        this.staticFunctions = staticFunctions;
        this.memberFields = memberFields;
        this.memberMethods = memberMethods;
        this.invariants = invariants;
        this.validates = validates;
        this.vtable = vtable;
        this.allfields = allfields;
    }
}

//Represents types declared as entities in the code
class TIRObjectEntityType extends TIREntityType {
    readonly binds: Map<string, TIRTypeKey>;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberFields: TIRMemberFieldDecl[], memberMethods: TIRMemberMethodDecl[], invariants: TIRInvariantDecl[], validates: TIRValidateDecl[], vtable: Map<string, TIRInvokeKey>, allfields: TIRFieldKey[], binds: Map<string, TIRTypeKey>) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, memberFields, memberMethods, invariants, validates, vtable, allfields);
        this.binds = binds;
    }
}

//Represents enum types declared as entities in the code
class TIREnumEntityType extends TIREntityType {
    readonly enumtype: TIRTypeKey;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], vtable: Map<string, TIRInvokeKey>, enumtype: TIRTypeKey) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods, [], [], vtable, []);
        this.enumtype = enumtype;
    }
}

//Represents typedecl T = X ... types where the representation is a single primitve typed value
class TIRTypedeclEntityType extends TIREntityType {
    readonly valuetype: TIRTypeKey; //result of .value()
    readonly representation: TIRTypeKey; //result of getUnderlyingRepresentation opcode -- a TIRResolvedPrimitiveInternalEntityAtomType

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], invariants: TIRInvariantDecl[], validates: TIRValidateDecl[], vtable: Map<string, TIRInvokeKey>, valuetype: TIRTypeKey, representation: TIRTypeKey) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods, invariants, validates, vtable, []);
        this.valuetype = valuetype;
        this.representation = representation;
    }
}

//base class for all the primitive types that are defined
abstract class TIRInternalEntityType extends TIREntityType {
    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberFields: TIRMemberFieldDecl[], memberMethods: TIRMemberMethodDecl[], invariants: TIRInvariantDecl[], validates: TIRValidateDecl[], vtable: Map<string, TIRInvokeKey>, allfields: TIRFieldKey[]) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, memberFields, memberMethods, invariants, validates, vtable, allfields);
    }
} 

//class representing all the primitive values (Int, Bool, String, ...). ALl of these are special implemented values
class TIRPrimitiveInternalEntityType extends TIRInternalEntityType {
    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[]) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods, [], [], new Map<string, TIRInvokeKey>(), []);
    }
} 

//class representing Validator regex types
class TIRValidatorEntityType extends TIRInternalEntityType {
    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], staticFunctions: TIRStaticFunctionDecl[]) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, [], staticFunctions, [], [], [], [], new Map<string, TIRInvokeKey>(), []);
    }
}

//class representing StringOf<T> types
class TIRStringOfEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey; //TIRValidatorEntityType;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], validatortype: TIRTypeKey) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods, [], [], new Map<string, TIRInvokeKey>(), []);
        this.validatortype = validatortype;
    }
}

//class representing ASCIIStringOf<T> types
class TIRASCIIStringOfEntityTIRType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey; //TIRValidatorEntityType;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], validatortype: TIRTypeKey) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods, [], [], new Map<string, TIRInvokeKey>(), []);
        this.validatortype = validatortype;
    }
}

//class representing PathValidator types
class TIRPathValidatorEntityType extends TIRInternalEntityType {
    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], staticFunctions: TIRStaticFunctionDecl[]) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, [], staticFunctions, [], [], [], [], new Map<string, TIRInvokeKey>(), []);
    }
}

//class representing a Path<T> type
class TIRPathEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey //TIRPathValidatorEntityType;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], validatortype: TIRTypeKey) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods, [], [], new Map<string, TIRInvokeKey>(), []);
        this.validatortype = validatortype;
    }
}

//class representing a PathFragment<T> type
class TIRPathFragmentEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey //TIRPathValidatorEntityType;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], validatortype: TIRTypeKey) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods, [], [], new Map<string, TIRInvokeKey>(), []);
        this.validatortype = validatortype;
    }
}

class TIRPathGlobEntityType extends TIRInternalEntityType {
    readonly validatortype: TIRTypeKey //TIRPathValidatorEntityType;

    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[], validatortype: TIRTypeKey) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods, [], [], new Map<string, TIRInvokeKey>(), []);
        this.validatortype = validatortype;
    }
}

//class representing Ok, Err, Something types
abstract class TIRConstructableEntityType extends TIRInternalEntityType {
    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[]) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods, [], [], new Map<string, TIRInvokeKey>(), []);
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
        super(tid, tname, srcInfo, srcFile, attributes, provides, [], [], [], [], [], [], new Map<string, TIRInvokeKey>(), []);
    }
}

//abstract class for all the builtin collection types
abstract class TIRPrimitiveCollectionEntityType extends TIRInternalEntityType {
    constructor(tid: TIRTypeKey, tname: TIRTypeName, srcInfo: SourceInfo, srcFile: string, attributes: string[], provides: TIRTypeKey[], constMembers: TIRConstMemberDecl[], staticFunctions: TIRStaticFunctionDecl[], memberMethods: TIRMemberMethodDecl[]) {
        super(tid, tname, srcInfo, srcFile, attributes, provides, constMembers, staticFunctions, [], memberMethods, [], [], new Map<string, TIRInvokeKey>(), []);
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

class TIRTaskType extends TIRType {
    readonly task: TaskTypeDecl;
    readonly binds: Map<string, ResolvedType>;

    constructor(typeID: string, task: TaskTypeDecl, binds: Map<string, ResolvedType>) {
        super(typeID);
        this.task = task;
        this.binds = binds;
    }

    static create(object: TaskTypeDecl, binds: Map<string, ResolvedType>): ResolvedTaskAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        if (object.terms.length !== 0) {
            name += "<" + object.terms.map((arg) => (binds.get(arg.name) as ResolvedType).typeID).join(", ") + ">";
        }

        return new ResolvedTaskAtomType(name, object, binds);
    }
}

class TIRConceptType extends TIRType {
    readonly typeID: string;
    readonly concept: ConceptTypeDecl;
    readonly binds: Map<string, ResolvedType>;

    constructor(typeID: string, concept: ConceptTypeDecl, binds: Map<string, ResolvedType>) {
        this.typeID = typeID;
        this.concept = concept;
        this.binds = binds;
    }

    static create(concept: ConceptTypeDecl, binds: Map<string, ResolvedType>): ResolvedConceptAtomTypeEntry {
        let name = (concept.ns !== "Core" ? (concept.ns + "::") : "") + concept.name;
        if (concept.terms.length !== 0) {
            name += "<" + concept.terms.map((arg) => (binds.get(arg.name) as ResolvedType).typeID).join(", ") + ">";
        }

        return new ResolvedConceptAtomTypeEntry(name, concept, binds);
    }
}

class TIRConcepSetType extends TIRType {
    readonly conceptTypes: ResolvedConceptAtomTypeEntry[];

    constructor(typeID: string, concepts: ResolvedConceptAtomTypeEntry[]) {
        super(typeID);
        this.conceptTypes = concepts;
    }

    static create(concepts: ResolvedConceptAtomTypeEntry[]): ResolvedConceptAtomType {
        const sortedConcepts = concepts.sort((a, b) => a.typeID.localeCompare(b.typeID));
        const name = sortedConcepts.map((cpt) => cpt.typeID).join("&");

        return new ResolvedConceptAtomType(name, sortedConcepts);
    }

    isAnyConcept(): boolean {
        return this.conceptTypes.length === 1 && this.conceptTypes[0].typeID === "Any";
    }

    isSomeConcept(): boolean {
        return this.conceptTypes.length === 1 && this.conceptTypes[0].typeID === "Some";
    }

    isTupleConcept(): boolean {
        return this.conceptTypes.length === 1 && this.conceptTypes[0].typeID === "Tuple";
    }

    isRecordConcept(): boolean {
        return this.conceptTypes.length === 1 && this.conceptTypes[0].typeID === "Record";
    }

    isIOptionConcept(): boolean {
        return this.conceptTypes.length === 1 && this.conceptTypes[0].typeID === "IOption";
    }

    isISomethingConcept(): boolean {
        return this.conceptTypes.length === 1 && this.conceptTypes[0].typeID === "ISomething";
    }

    isOptionConcept(): boolean {
        return this.conceptTypes.length === 1 && this.conceptTypes[0].concept.attributes.includes("__option_type");
    }

    isIResultTConcept(): boolean {
        return this.conceptTypes.length === 1 && this.conceptTypes[0].typeID === "IResultT";
    }

    isIResultEConcept(): boolean {
        return this.conceptTypes.length === 1 && this.conceptTypes[0].typeID === "IResultE";
    }

    isResultConcept(): boolean {
        return this.conceptTypes.length === 1 && this.conceptTypes[0].concept.attributes.includes("__result_type");
    }

    getTBind(): ResolvedType {
        return this.conceptTypes[0].binds.get("T") as ResolvedType;
    }

    getEBind(): ResolvedType {
        return this.conceptTypes[0].binds.get("E") as ResolvedType;
    }
}

class TIRTupleType extends TIRType {
    readonly types: ResolvedType[];

    constructor(typeID: string, types: ResolvedType[]) {
        super(typeID);
        this.types = types;
    }

    static create(types: ResolvedType[]): ResolvedTupleAtomType {
        const name = types.map((entry) => entry.typeID).join(", ");

        return new ResolvedTupleAtomType("[" + name + "]", types);
    }
}

class TIRRecordType extends TIRType {
    readonly entries: {pname: string, ptype: ResolvedType}[];

    constructor(typeID: string, entries: {pname: string, ptype: ResolvedType}[]) {
        super(typeID);
        this.entries = entries;
    }

    static create(entries: {pname: string, ptype: ResolvedType}[]): ResolvedRecordAtomType {
        let simplifiedEntries = [...entries].sort((a, b) => a.pname.localeCompare(b.pname));
        const name = simplifiedEntries.map((entry) => entry.pname + ": " + entry.ptype.typeID).join(", ");

        return new ResolvedRecordAtomType("{" + name + "}", simplifiedEntries);
    }
}

class TIREphemeralListType extends TIRType {
    readonly types: ResolvedType[];

    constructor(typeID: string, types: ResolvedType[]) {
        super(typeID);
        this.types = types;
    }

    static create(entries: ResolvedType[]): ResolvedEphemeralListType {
        const name = entries.map((entry) => entry.typeID).join(", ");

        return new ResolvedEphemeralListType("(|" + name + "|)", entries);
    }
}

class TIRUnionType extends TIRType {
    readonly typeID: string;
    readonly options: ResolvedAtomType[];

    constructor(typeID: string, options: ResolvedAtomType[]) {
        this.typeID = typeID;
        this.options = options;
    }

    static isGroundedType(options: ResolvedAtomType[]): boolean {
        return options.every((opt) => {
            if(opt instanceof ResolvedConceptAtomType) {
                return opt.conceptTypes.every((cpt) => !cpt.concept.attributes.includes("__universal"));
            }
            else if (opt instanceof ResolvedTupleAtomType) {
                return opt.types.every((tt) => ResolvedType.isGroundedType(tt.options));
            }
            else if (opt instanceof ResolvedRecordAtomType) {
                return opt.entries.every((entry) => ResolvedType.isGroundedType(entry.ptype.options));
            }
            else {
                return true;
            }
        });
    }

    static isUniqueType(tt: ResolvedAtomType): boolean {
        return !(tt instanceof ResolvedConceptAtomType);
    }

    static isNumericType(options: ResolvedAtomType[]): boolean {
        if(options.length !== 1 || !(options[0] instanceof ResolvedEntityAtomType)) {
            return false;
        }
        const atom = options[0] as ResolvedEntityAtomType;

        if(atom instanceof ResolvedPrimitiveInternalEntityAtomType) {
            return atom.object.attributes.includes("__numeric");
        }
        
        if(atom instanceof ResolvedTypedeclEntityAtomType) {
            return atom.representation.object.attributes.includes("__numeric");
        }
        
        return false;
    }

    static createInvalid(): ResolvedType {
        return new ResolvedType("[INVALID]", []);
    }

    static createSingle(type: ResolvedAtomType): ResolvedType {
        return new ResolvedType(type.typeID, [type]);
    }

    static create(types: ResolvedAtomType[]): ResolvedType {
        assert(types.length !== 0, "Invalid Type??")
         
        if (types.length === 1) {
            return ResolvedType.createSingle(types[0]);
        }
        else {
            const atoms = types.sort((a, b) => a.typeID.localeCompare(b.typeID));
            const name = atoms.map((arg) => arg.typeID).join(" | ");

            return new ResolvedType(name, atoms);
        }
    }

    tryGetUniqueLiteralTypeInfo(): ResolvedLiteralAtomType | undefined {
        if (this.options.length !== 1) {
            return undefined;
        }

        if (this.options[0] instanceof ResolvedLiteralAtomType) {
            return (this.options[0] as ResolvedLiteralAtomType);
        }
        else {
            return undefined;
        }
    }

    tryGetUniqueOOTypeInfo(): [OOPTypeDecl | undefined, Map<string, ResolvedType>] {
        if (this.options.length !== 1) {
            return [undefined, new Map<string, ResolvedType>()];
        }

        if (this.options[0] instanceof ResolvedEntityAtomType) {
            return [this.options[0].object, this.options[0].getBinds()];
        }
        else if (this.options[0] instanceof ResolvedConceptAtomType && this.options[0].conceptTypes.length === 1) {
            return [this.options[0].conceptTypes[0].concept, this.options[0].conceptTypes[0].binds];
        }
        else {
            return [undefined, new Map<string, ResolvedType>()];
        }
    }

    tryGetUniqueEntityBindsInfo(): Map<string, ResolvedType> | undefined{
        if (this.options.length !== 1) {
            return undefined;
        }

        if (this.options[0] instanceof ResolvedEntityAtomType) {
            return this.options[0].getBinds();
        }
        else {
            return undefined;
        }
    }

    tryGetUniqueEntityTypeInfo(): ResolvedEntityAtomType | undefined {
        if (this.options.length !== 1) {
            return undefined;
        }

        if (this.options[0] instanceof ResolvedEntityAtomType) {
            return (this.options[0] as ResolvedEntityAtomType);
        }
        else {
            return undefined;
        }
    }

    tryGetUniqueTaskTypeInfo(t: ResolvedType): ResolvedTaskAtomType | undefined {
        if (t.options.length !== 1) {
            return undefined;
        }

        if (t.options[0] instanceof ResolvedTaskAtomType) {
            return (t.options[0] as ResolvedTaskAtomType);
        }
        else {
            return undefined;
        }
    }

    isSameType(otype: ResolvedType): boolean {
        return this.typeID === otype.typeID;
    }

    isNoneType(): boolean {
        return this.typeID === "None";
    }

    isSomeType(): boolean {
        return this.typeID === "Some";
    }

    isAnyType(): boolean {
        return this.typeID === "Any";
    }

    isNothingType(): boolean {
        return this.typeID === "Nothing";
    }

    isSomethingType(): boolean {
        if(this.options.length !== 1 || !(this.options[0] instanceof ResolvedConstructableEntityAtomType)) {
            return false;
        }

        return (this.options[0] instanceof ResolvedSomethingEntityAtomType);
    }

    isOptionType(): boolean {
        if(this.options.length !== 1 || !(this.options[0] instanceof ResolvedConceptAtomType)) {
            return false;
        }

        return(this.options[0] as ResolvedConceptAtomType).isOptionConcept();
    }

    isOkType(): boolean {
        if(this.options.length !== 1 || !(this.options[0] instanceof ResolvedConstructableEntityAtomType)) {
            return false;
        }

        return this.options[0] instanceof ResolvedOkEntityAtomType;
    }

    isErrType(): boolean {
        if(this.options.length !== 1 || !(this.options[0] instanceof ResolvedConstructableEntityAtomType)) {
            return false;
        }

        return (this.options[0] instanceof ResolvedErrEntityAtomType);
    }

    isResultType(): boolean {
        if(this.options.length !== 1 || !(this.options[0] instanceof ResolvedConceptAtomType)) {
            return false;
        }

        return (this.options[0] as ResolvedConceptAtomType).isResultConcept();
    }

    isInvalidType(): boolean {
        return this.options.length === 0;
    }
}

class ResolvedFunctionTypeParam {
    readonly name: string;
    readonly type: ResolvedType | ResolvedFunctionType;
    readonly litexp: TIRLiteralValue | undefined;

    constructor(name: string, type: ResolvedType | ResolvedFunctionType, litexp: TIRLiteralValue | undefined) {
        this.name = name;
        this.type = type;
        this.litexp = litexp;
    }
}

class ResolvedFunctionType {
    readonly typeID: string;
    readonly isThisRef: boolean;
    readonly recursive: "yes" | "no" | "cond";
    readonly params: ResolvedFunctionTypeParam[];
    readonly resultType: ResolvedType;
    readonly isPred: boolean;

    constructor(typeID: string, isThisRef: boolean, recursive: "yes" | "no" | "cond", params: ResolvedFunctionTypeParam[], resultType: ResolvedType, isPred: boolean) {
        this.typeID = typeID;
        this.isThisRef = isThisRef;
        this.recursive = recursive;
        this.params = params;
        this.resultType = resultType;
        this.isPred = isPred;
    }

    static create(isThisRef: boolean, recursive: "yes" | "no" | "cond", params: ResolvedFunctionTypeParam[], resultType: ResolvedType, isPred: boolean): ResolvedFunctionType {
        const cvalues = params.map((param) => param.name + param.type.typeID + (param.litexp !== undefined ? ("==" + param.litexp.lidstr) : ""));
        let cvalue = cvalues.join(", ");

        const lstr = isPred ? "pred" : "fn";
        const name = (isThisRef ? "ref" : "") + lstr + "(" + cvalue + ") -> " + resultType.typeID;
        return new ResolvedFunctionType(name, isThisRef, recursive, params, resultType, isPred);
    }
}

export {
    TIRTypeName, TIRNamespaceMemberName, TIRTypeMemberName, TIRNameSpaceConstKey, TIRMemberConstKey,
    TIRTypeKey, TIRInvokeKey, TIRPropertyKey, TIRFieldKey, TIRTupleIndex,
    TIRFunctionParameter,
    TIRInvariantDecl, TIRValidateDecl,
    TIRInvokeDecl,
    TIRConstMemberDecl, TIRStaticFunctionDecl, TIRMemberFieldDecl, TIRMemberMethodDecl,
    TIRType,
    TIRLiteralType,
    TIREntityType, TIRObjectEntityType, TIREnumEntityType, TIRTypedeclEntityType, TIRInternalEntityType, TIRPrimitiveInternalEntityType,
    TIRValidatorEntityType, TIRStringOfEntityType, TIRASCIIStringOfEntityTIRType,
    TIRPathValidatorEntityType, TIRPathEntityType, TIRPathFragmentEntityType, TIRPathGlobEntityType,
    TIRConstructableEntityType, TIROkEntityType, TIRErrEntityType, TIRSomethingEntityType,
    TIRHavocEntityType,
    TIRPrimitiveCollectionEntityType, TIRListEntityType, TIRStackEntityType, TIRQueueEntityType, TIRSetEntityType, TIRMapEntityTIRType,
    TIRTaskType,
    TIRConceptType, TIRConcepSetType,
    TIRTupleType, TIRRecordType,
    TIREphemeralListType,
    TIRCodePackType,
    TIRUnionType
};
