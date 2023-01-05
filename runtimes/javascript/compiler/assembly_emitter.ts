import * as assert from "assert";
import * as path from "path";

import { TIRAssembly, TIRConstMemberDecl, TIREnumEntityType, TIRFieldKey, TIRInvokeAbstractDeclaration, TIRInvokeImplementation, TIRInvokePrimitive, TIRMemberFieldDecl, TIRMemberMethodDecl, TIRNamespaceConstDecl, TIRNamespaceDeclaration, TIRNamespaceFunctionDecl, TIRObjectEntityType, TIROOType, TIRPrimitiveInternalEntityType, TIRStaticFunctionDecl, TIRStringOfEntityType, TIRTaskType, TIRType, TIRTypedeclEntityType, TIRTypeKey, TIRValidatorEntityType } from "../../../frontend/tree_ir/tir_assembly";
import { TIRLiteralValue } from "../../../frontend/tree_ir/tir_body";
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

    private emitMemberFunction(ootype: TIROOType, fdecl: TIRStaticFunctionDecl): string | undefined {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(fdecl.srcFile), this.m_ns); 

        const args = fdecl.invoke.params.map((pp) => pp.name).join(", ");

        let body: string | undefined = "[NOT SET]";
        assert(!(fdecl.invoke instanceof TIRInvokeAbstractDeclaration), "should not be doing this!!");
            
        if(fdecl.invoke instanceof TIRInvokePrimitive) {
            body = emitBuiltinMemberFunction(ootype, fdecl, bemitter);
        }
        else {
            const fimpl = fdecl.invoke as TIRInvokeImplementation;
            body = bemitter.emitBodyStatementList(fimpl.body, fimpl.preconditions, fimpl.postconditions, "    ", `${fdecl.tkey}::${fdecl.name}`, false);
        }

        if(body === undefined) {
            return undefined;
        }
        const cstr = `${fdecl.name}: function(${args}) ${body}`;
        
        this.updateCoreImports(bemitter);
        return cstr;
    }

    private emitMemberMethod(ootype: TIROOType, mdecl: TIRMemberMethodDecl): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(mdecl.srcFile), this.m_ns); 

        const args = [(ootype instanceof TIRTaskType ? "self" : "$_this"), ...mdecl.invoke.params.map((pp) => pp.name)].join(", ");

        assert(!(mdecl.invoke instanceof TIRInvokeAbstractDeclaration) && !(mdecl.invoke instanceof TIRInvokePrimitive), "should not be doing this!!");
            
        const mimpl = mdecl.invoke as TIRInvokeImplementation;
        const body = bemitter.emitBodyStatementList(mimpl.body, mimpl.preconditions, mimpl.postconditions, "    ", `${mdecl.tkey}::${mdecl.name}`, mdecl.attributes.includes("action") || mdecl.invoke.isThisRef);
        
        const cstr = `${mdecl.name}: function(${args}) ${body}`;
        
        this.updateCoreImports(bemitter);
        return cstr;
    }

    private emitTIREnumEntityType(ttype: TIREnumEntityType): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const entries = ttype.enums.map((ee) => `${ee}: ${bemitter.emitExpression((ttype.litvals.get(ee) as TIRLiteralValue).exp)}`);
        const funcs = ttype.staticFunctions.map((sf) => this.emitMemberFunction(ttype, sf));
        const methods = ttype.memberMethods.map((mm) => this.emitMemberMethod(ttype, mm));

        const enums = `const BSQ${ttype.tname.name} = {${[...entries, ...funcs, ...methods].join(",\n    ")}\n};`;

        this.updateCoreImports(bemitter);
        return enums;
    }

    private emitTIRTypedeclEntityType(ttype: TIRTypedeclEntityType): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = ttype.staticFunctions.map((sf) => this.emitMemberFunction(ttype, sf));
        const methods = ttype.memberMethods.map((mm) => this.emitMemberMethod(ttype, mm));

        let consfuncs: string[] = [];
        if(ttype.consinvariantsall.length !== 0) {
            const checks = ttype.consinvariantsall.map((cc) => `$Runtime.raiseUserAssertIf(!${bemitter.emitExpression(cc.exp)}, "Failed invariant ${ttype.tkey} -- ${cc.exp.expstr}");`).join("\n    ") + "\n    ";
            consfuncs.push(`$constructorWithChecks_basetype: function($value) {${checks}return $value;\n    }`);
        }
        if(ttype.consinvariantsexplicit.length !== 0) {
            const checks = ttype.consinvariantsexplicit.map((cc) => `$Runtime.raiseUserAssertIf(!${bemitter.emitExpression(cc.exp)}, "Failed invariant ${ttype.tkey} -- ${cc.exp.expstr}");`).join("\n    ") + "\n    ";
            consfuncs.push(`$constructorWithChecks: function($value) {${checks}return $value;\n    }`);
        }

        const tdecl = `const BSQ${ttype.tname.name} = {${[...consts, ...funcs, ...methods, ...consfuncs].join(",\n    ")}\n};`;

        this.updateCoreImports(bemitter);
        return tdecl;
    }

    private emitTIRObjectEntityType(ttype: TIRObjectEntityType): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = ttype.staticFunctions.map((sf) => this.emitMemberFunction(ttype, sf));
        const methods = ttype.memberMethods.map((mm) => this.emitMemberMethod(ttype, mm));

        const fnames = ttype.allfields.map((ff) => (this.m_assembly.fieldMap.get(ff.fkey) as TIRMemberFieldDecl).name);

        let consfuncs: string[] = [];
        consfuncs.push(`$constructorDirect: function(${fnames.join(", ")} { return {${fnames.map((fn) => fn + ": " + fn).join(", ")}}; })`);

        if(ttype.consinvariants.length !== 0) {
            const checks = ttype.consinvariants.map((cc) => `$Runtime.raiseUserAssertIf(!${bemitter.emitExpression(cc.exp)}, "Failed invariant ${ttype.tkey} -- ${cc.exp.expstr}");`).join("\n    ") + "\n    ";
            consfuncs.push(`$constructorWithChecks_basetype: function(${fnames.map((fn) => "$" + fn).join(", ")}) {${checks}return {${fnames.map((fn) => fn + ": $" + fn).join(", ")}};\n    }`);
        }

        const odecl = `const BSQ${ttype.tname.name} = {${[...consts, ...funcs, ...methods, ...consfuncs].join(",\n    ")}\n};`;

        this.updateCoreImports(bemitter);
        return odecl;
    }

    private emitTIRPrimitiveInternalEntityType(ttype: TIRPrimitiveInternalEntityType): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = ttype.staticFunctions.map((sf) => this.emitMemberFunction(ttype, sf));
        const methods = ttype.memberMethods.map((mm) => this.emitMemberMethod(ttype, mm));

        const tdecl = `const BSQ${ttype.tname.name} = {${[...consts, ...funcs, ...methods].join(",\n    ")}\n};`;

        this.updateCoreImports(bemitter);
        return tdecl;
    }

    private emitTIRValidatorEntityType(ttype: TIRValidatorEntityType): string {
        
    }

    private emitTIRStringOfEntityType(ttype: TIRStringOfEntityType): string {
        
    }

    private emitTIRASCIIStringOfEntityType(): string {
        
    }

    private emitTIRPathValidatorEntityType(): string {
        
    }

    private emitTIRPathEntityType(): string {
        
    }

    private emitTIRPathFragmentEntityType(): string {
        
    }

    private emitTIRPathGlobEntityType(): string {
        
    }

    private emitTIROkEntityType(): string {
        
    }

    private emitTIRErrEntityType(): string {
        
    }

    private emitTIRSomethingEntityType(): string {
        
    }

    private emitTIRMapEntryEntityType(): string {
        
    }

    private emitTIRListEntityType(): string {
        
    }

    private emitTIRStackEntityType(): string {
        
    }

    private emitTIRQueueEntityType(): string {
        
    }

    private emitTIRSetEntityType(): string {
        
    }

    private emitTIRMapEntityType(): string {
        
    }

    private emitTIRTaskType(): string {
        
    }

    private emitTIRConceptType(): string {
        
    }

    private emitTIRConceptSetType(): string {

    }

    private emitTIRTupleType(): string {
        
    }

    private emitTIRRecordType(): string {
        
    }

    private emitTIRUnionType(): string {
        
    }

    private emitTIRCodePackType(): string {
        
    }



    private emitConst(ttype: TIRNamespaceConstDecl): string {
        
    }

    private emitFunction(ttype: TIRNamespaceFunctionDecl): string {
        
    }

    private emitOperator(ttype: TIRNamespaceDeclaration): string {
        
    }

    private emitType(ttype: TIRType): string {

    }
}

class AssemblyEmitter {
}

export {
    AssemblyEmitter
};
