import * as assert from "assert";
import * as path from "path";

import { TIRASCIIStringOfEntityType, TIRAssembly, TIRConceptType, TIRConstMemberDecl, TIREnumEntityType, TIRInvokeAbstractDeclaration, TIRInvokeImplementation, TIRInvokeKey, TIRInvokePrimitive, TIRListEntityType, TIRMapEntityType, TIRMemberFieldDecl, TIRMemberMethodDecl, TIRNamespaceConstDecl, TIRNamespaceDeclaration, TIRNamespaceFunctionDecl, TIRNamespaceOperatorDecl, TIRObjectEntityType, TIROOType, TIRPathEntityType, TIRPathFragmentEntityType, TIRPathGlobEntityType, TIRPathValidatorEntityType, TIRPrimitiveInternalEntityType, TIRQueueEntityType, TIRSetEntityType, TIRStackEntityType, TIRStaticFunctionDecl, TIRStringOfEntityType, TIRTaskType, TIRType, TIRTypedeclEntityType, TIRTypeKey, TIRValidatorEntityType } from "../../../frontend/tree_ir/tir_assembly";
import { TIRCodePack, TIRLiteralValue } from "../../../frontend/tree_ir/tir_body";
import { BodyEmitter } from "./body_emitter";
import { emitBuiltinMemberFunction } from "./builtin_emitter";

class NamespaceEmitter {
    private readonly m_assembly: TIRAssembly;
    private readonly m_ns: string;

    private m_coreImports: Set<TIRTypeKey> = new Set<TIRTypeKey>();

    constructor(assembly: TIRAssembly, ns: string) {
        this.m_assembly = assembly;
        this.m_ns = ns;
    }

    private updateCoreImports(bemitter: BodyEmitter) {
        bemitter.m_coreImports.forEach((ii) => this.m_coreImports.add(ii));
    }

    private emitMemberConst(ootype: TIROOType, cdecl: TIRConstMemberDecl): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(cdecl.srcFile), this.m_ns); 

        const cstr = `${cdecl.name}: ${bemitter.emitExpression(cdecl.value, true)}`;

        this.updateCoreImports(bemitter);
        return cstr;
    }

    private emitMemberFunction(ootype: TIROOType, fdecl: TIRStaticFunctionDecl, indent: string): string | undefined {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(fdecl.srcFile), this.m_ns); 

        const args = fdecl.invoke.params.map((pp) => pp.name).join(", ");

        let body: string | undefined = "[NOT SET]";
        assert(!(fdecl.invoke instanceof TIRInvokeAbstractDeclaration), "should not be doing this!!");
            
        if(fdecl.invoke instanceof TIRInvokePrimitive) {
            body = emitBuiltinMemberFunction(ootype, fdecl, bemitter);
        }
        else {
            const fimpl = fdecl.invoke as TIRInvokeImplementation;
            body = bemitter.emitBodyStatementList(fimpl.body, fimpl.preconditions, fimpl.postconditions, indent, `${fdecl.tkey}::${fdecl.name}`, false);
        }

        if(body === undefined) {
            return undefined;
        }
        const cstr =  `function(${args}) ${body}`;
        
        this.updateCoreImports(bemitter);
        return cstr;
    }

    private emitMemberMethod(ootype: TIROOType, mdecl: TIRMemberMethodDecl, indent: string): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(mdecl.srcFile), this.m_ns); 

        const args = [(ootype instanceof TIRTaskType ? "self" : "$_this"), ...mdecl.invoke.params.map((pp) => pp.name)].join(", ");

        assert(!(mdecl.invoke instanceof TIRInvokeAbstractDeclaration) && !(mdecl.invoke instanceof TIRInvokePrimitive), "should not be doing this!!");
            
        const mimpl = mdecl.invoke as TIRInvokeImplementation;
        const body = bemitter.emitBodyStatementList(mimpl.body, mimpl.preconditions, mimpl.postconditions, indent, `${mdecl.tkey}::${mdecl.name}`, mdecl.attributes.includes("action") || mdecl.invoke.isThisRef);
        
        const cstr = `function(${args}) ${body}`;
        
        this.updateCoreImports(bemitter);
        return cstr;
    }

    private emitOOTypeFunctions(ootype: TIROOType): string[] {
        const finline = ootype.staticFunctions.filter((ff) => ff.invoke.tbinds.size === 0 && ff.invoke.pcodes.size === 0).map((ff) => ff.name + ": " + this.emitMemberFunction(ootype, ff, "    "));
        const fkey = ootype.staticFunctions.filter((ff) => ff.invoke.tbinds.size !== 0 || ff.invoke.pcodes.size !== 0).map((ff) => `"${ff.ikey}": ` + this.emitMemberFunction(ootype, ff, "        "));

        return [finline.join(",\n    "), `$Functions: {${fkey.join(",\n    ")}\n    }`];
    }

    private emitOOTypeMethods(ootype: TIROOType): string[] {
        const minline = ootype.memberMethods.filter((mm) => mm.invoke.tbinds.size === 0 && mm.invoke.pcodes.size === 0).map((mm) => mm.name + ": " + this.emitMemberMethod(ootype, mm, "    "));
        const mkey = ootype.memberMethods.filter((mm) => mm.invoke.tbinds.size !== 0 || mm.invoke.pcodes.size !== 0).map((mm) => `"${mm.ikey}": ` + this.emitMemberMethod(ootype, mm, "        "));

        return [minline.join(",\n    "), `$Methods: {${mkey.join(",\n    ")}\n    }`];
    }

    private emitTIREnumEntityType(ttype: TIREnumEntityType): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const entries = ttype.enums.map((ee) => `${ee}: ${bemitter.emitExpression((ttype.litvals.get(ee) as TIRLiteralValue).exp)}`);
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        this.updateCoreImports(bemitter);
        return `const BSQ${ttype.tname.name} = {${[...entries, ...funcs, ...methods].join(",\n    ")}\n};`;
    }

    private emitTIRTypedeclEntityType(ttype: TIRTypedeclEntityType): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        let consfuncs: string[] = [];
        if(ttype.consinvariantsall.length !== 0) {
            const checks = ttype.consinvariantsall.map((cc) => `$Runtime.raiseUserAssertIf(!${bemitter.emitExpression(cc.exp)}, "Failed invariant ${ttype.tkey} -- ${cc.exp.expstr}");`).join("\n    ") + "\n    ";
            consfuncs.push(`$constructorWithChecks_basetype: function($value) {${checks}return $value;\n    }`);
        }
        if(ttype.consinvariantsexplicit.length !== 0) {
            const checks = ttype.consinvariantsexplicit.map((cc) => `$Runtime.raiseUserAssertIf(!${bemitter.emitExpression(cc.exp)}, "Failed invariant ${ttype.tkey} -- ${cc.exp.expstr}");`).join("\n    ") + "\n    ";
            consfuncs.push(`$constructorWithChecks: function($value) {${checks}return $value;\n    }`);
        }

        this.updateCoreImports(bemitter);
        return `const BSQ${ttype.tname.name} = {${[...consts, ...funcs, ...methods, ...consfuncs].join(",\n    ")}\n};`;
    }

    private emitTIRObjectEntityType(ttype: TIRObjectEntityType): [boolean, string] {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        const fnames = ttype.allfields.map((ff) => (this.m_assembly.fieldMap.get(ff.fkey) as TIRMemberFieldDecl).name);

        let consfuncs: string[] = [];
        consfuncs.push(`$constructorDirect: function(${fnames.join(", ")} { return {${fnames.map((fn) => fn + ": " + fn).join(", ")}}; })`);

        if(ttype.consinvariants.length !== 0) {
            const checks = ttype.consinvariants.map((cc) => `$Runtime.raiseUserAssertIf(!${bemitter.emitExpression(cc.exp)}, "Failed invariant ${ttype.tkey} -- ${cc.exp.expstr}");`).join("\n    ") + "\n    ";
            consfuncs.push(`$constructorWithChecks_basetype: function(${fnames.map((fn) => "$" + fn).join(", ")}) {${checks}return {${fnames.map((fn) => fn + ": $" + fn).join(", ")}};\n    }`);
        }

        this.updateCoreImports(bemitter);
        if(ttype.binds.size === 0) {
            return [false, `const BSQ${ttype.tname.name} = {${[...consts, ...funcs, ...methods, ...consfuncs].join(",\n    ")}\n};`];
        }
        else {
            return [true, `"${ttype.tkey}": {${[...consts, ...funcs, ...methods, ...consfuncs].join(",\n    ")}\n}`];
        }
    }

    private emitTIRPrimitiveInternalEntityType(ttype: TIRPrimitiveInternalEntityType): string {
        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        return `const BSQ${ttype.tname.name} = {${[...consts, ...funcs, ...methods].join(",\n    ")}\n};`;
    }

    private emitTIRValidatorEntityType(ttype: TIRValidatorEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${[...funcs].join(",\n    ")}\n}`;
    }

    private emitTIRStringOfEntityType(ttype: TIRStringOfEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${[...funcs].join(",\n    ")}\n}`;
    }

    private emitTIRASCIIStringOfEntityType(ttype: TIRASCIIStringOfEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${[...funcs].join(",\n    ")}\n}`;
    }

    private emitTIRPathValidatorEntityType(ttype: TIRPathValidatorEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${[...funcs].join(",\n    ")}\n}`;
    }

    private emitTIRPathEntityType(ttype: TIRPathEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${[...funcs].join(",\n    ")}\n}`;
    }

    private emitTIRPathFragmentEntityType(ttype: TIRPathFragmentEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${[...funcs].join(",\n    ")}\n}`;
    }

    private emitTIRPathGlobEntityType(ttype: TIRPathGlobEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${[...funcs].join(",\n    ")}\n}`;
    }

    private emitTIRListEntityType(ttype: TIRListEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        return `"${ttype.tkey}": {${[...funcs, ...methods].join(",\n    ")}\n}`
    }

    private emitTIRStackEntityType(ttype: TIRStackEntityType): string {
        return "[NOT IMPLEMENTED -- STACK]";
    }

    private emitTIRQueueEntityType(ttype: TIRQueueEntityType): string {
        return "[NOT IMPLEMENTED -- QUEUE]";
    }

    private emitTIRSetEntityType(ttype: TIRSetEntityType): string {
        return "[NOT IMPLEMENTED -- SET]";
    }

    private emitTIRMapEntityType(ttype: TIRMapEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        return `"${ttype.tkey}": {${[...funcs, ...methods].join(",\n    ")}\n}`;
    }

    private emitTIRTaskType(ttype: TIRTaskType): string {
        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        const fnames = ttype.memberFields.map((ff) => (this.m_assembly.fieldMap.get(ff.fkey) as TIRMemberFieldDecl).name);

        let consfuncs: string[] = [];
        consfuncs.push(`$constructorDirect: function(${fnames.join(", ")} { return {${fnames.map((fn) => fn + ": " + fn).join(", ")}}; })`);

        //
        //TODO: main func and such here too!
        //

        return `const BSQ${ttype.tname.name} = {${[...consts, ...funcs, ...methods, ...consfuncs].join(",\n    ")}\n};`;
    }

    private emitTIRConceptType(ttype: TIRConceptType): [boolean, string] {
        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        if(ttype.binds.size === 0) {
            return [false, `const BSQ${ttype.tname.name} = {${[...consts, ...funcs, ...methods].join(",\n    ")}\n};`];
        }
        else {
            return [true, `"${ttype.tkey}": {${[...consts, ...funcs, ...methods].join(",\n    ")}\n}`];
        }
    }

    private emitConst(nsconst: TIRNamespaceConstDecl): string {
        
    }

    private emitFunction(nsfunc: TIRNamespaceFunctionDecl): string {
        
    }

    private emitOperator(nsoperator: TIRNamespaceDeclaration): string {
        
    }

    private emitCodePackFunction(pcode: TIRCodePack): string {
        
    }

    private emitType(ttype: TIRType): [boolean, string] | undefined {
        if(ttype instanceof TIREnumEntityType) {
            return [false, this.emitTIREnumEntityType(ttype)];
        }
        else if(ttype instanceof TIRTypedeclEntityType) {
            return [false, this.emitTIRTypedeclEntityType(ttype)];
        }
        else if(ttype instanceof TIRObjectEntityType) {
            return this.emitTIRObjectEntityType(ttype);
        }
        else if(ttype instanceof TIRPrimitiveInternalEntityType) {
            return [false, this.emitTIRPrimitiveInternalEntityType(ttype)];
        }
        else if(ttype instanceof TIRValidatorEntityType) {
            return [true, this.emitTIRValidatorEntityType(ttype)];
        }
        else if(ttype instanceof TIRStringOfEntityType) {
            return [true, this.emitTIRStringOfEntityType(ttype)];
        } 
        else if(ttype instanceof TIRASCIIStringOfEntityType) {
            return [true, this.emitTIRASCIIStringOfEntityType(ttype)];
        }
        else if(ttype instanceof TIRPathValidatorEntityType) {
            return [true, this.emitTIRPathValidatorEntityType(ttype)];
        }
        else if(ttype instanceof TIRPathEntityType) {
            return [true, this.emitTIRPathEntityType(ttype)];
        }
        else if(ttype instanceof TIRPathFragmentEntityType) {
            return [true, this.emitTIRPathFragmentEntityType(ttype)];
        }
        else if(ttype instanceof TIRPathGlobEntityType) {
            return [true, this.emitTIRPathGlobEntityType(ttype)];
        }
        else if(ttype instanceof TIRListEntityType) {
            return [true, this.emitTIRListEntityType(ttype)];
        }
        else if(ttype instanceof TIRStackEntityType) {
            return [true, this.emitTIRStackEntityType(ttype)];
        }
        else if(ttype instanceof TIRQueueEntityType) {
            return [true, this.emitTIRQueueEntityType(ttype)];
        }
        else if(ttype instanceof TIRSetEntityType) {
            return [true, this.emitTIRSetEntityType(ttype)];
        }
        else if(ttype instanceof TIRMapEntityType) {
            return [true, this.emitTIRMapEntityType(ttype)];
        }
        else if(ttype instanceof TIRTaskType) {
            return [false, this.emitTIRTaskType(ttype)];
        }
        else if(ttype instanceof TIRConceptType) {
            return this.emitTIRConceptType(ttype);
        }
        else {
            return undefined;
        }
    }
}

class AssemblyEmitter {
    readonly assembly: TIRAssembly;
    readonly corelib: string;
    readonly runtime: string;

    readonly namespacedecls: Map<string, string[]> = new Map<string, string[]>();
    readonly subtypeinfo: Map<TIRTypeKey, TIRTypeKey[]> = new Map<TIRTypeKey, TIRTypeKey[]>();
    readonly keyeqinfo: Map<TIRTypeKey, string> = new Map<TIRTypeKey, string>();
    readonly keylessinfo: Map<TIRTypeKey, string> = new Map<TIRTypeKey, string>();
    readonly vcallinfo: Map<TIRTypeKey, Map<TIRInvokeKey, TIRInvokeKey>> = new Map<TIRTypeKey, Map<TIRInvokeKey, TIRInvokeKey>>();

    constructor(assembly: TIRAssembly, corelib: string, runtime: string) {
        this.assembly = assembly;
        this.corelib = corelib;
        this.runtime = runtime;
    }

    private processAssembly() {
        xxxx;
    };

    generateJSCode(): {asmname: string, contents: string}[] {

    }
}

export {
    AssemblyEmitter
};
