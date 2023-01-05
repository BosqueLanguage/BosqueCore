import * as assert from "assert";
import * as path from "path";

import { TIRAssembly, TIRConstMemberDecl, TIREnumEntityType, TIRInvokeAbstractDeclaration, TIRInvokeImplementation, TIRInvokePrimitive, TIRMemberFieldDecl, TIRMemberMethodDecl, TIRNamespaceConstDecl, TIRNamespaceDeclaration, TIRNamespaceFunctionDecl, TIROOType, TIRStaticFunctionDecl, TIRTaskType, TIRType, TIRTypeKey } from "../../../frontend/tree_ir/tir_assembly";
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

        const cstr = `${bemitter.resolveTypeMemberAccess(cdecl.tkey)}.${cdecl.name} = ${bemitter.emitExpression(cdecl.value, true)};`;

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
            body = bemitter.emitBodyStatementList(fimpl.body, fimpl.preconditions, fimpl.postconditions, "", `${fdecl.tkey}::${fdecl.name}`, false);
        }

        if(body === undefined) {
            return undefined;
        }
        const cstr = `${bemitter.resolveTypeMemberAccess(fdecl.tkey)}.${fdecl.name} = function(${args}) ${body};`;
        
        this.updateCoreImports(bemitter);
        return cstr;
    }

    private emitMemberField(ootype: TIROOType, fdecl: TIRMemberFieldDecl): string {
        xxxx;
    }

    private emitMemberMethod(ootype: TIROOType, mdecl: TIRMemberMethodDecl): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(mdecl.srcFile), this.m_ns); 

        const args = [(ootype instanceof TIRTaskType ? "self" : "$_this"), ...mdecl.invoke.params.map((pp) => pp.name)].join(", ");

        assert(!(mdecl.invoke instanceof TIRInvokeAbstractDeclaration) && !(mdecl.invoke instanceof TIRInvokePrimitive), "should not be doing this!!");
            
        const mimpl = mdecl.invoke as TIRInvokeImplementation;
        const body = bemitter.emitBodyStatementList(mimpl.body, mimpl.preconditions, mimpl.postconditions, "", `${mdecl.tkey}::${mdecl.name}`, mdecl.attributes.includes("action") || mdecl.invoke.isThisRef);
        
        const cstr = `${bemitter.resolveTypeMemberAccess(mdecl.tkey)}.${mdecl.name} = function(${args}) ${body};`;
        
        this.updateCoreImports(bemitter);
        return cstr;
    }

    private emitTIREnumEntityType(ttype: TIREnumEntityType): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const entries = ttype.enums.map((ee) => `${ee}: ${bemitter.emitExpression((ttype.litvals.get(ee) as TIRLiteralValue).exp)}`).join(",\n    ");
        const enums = `BSQ${ttype.tname.name} = {${entries}\n};`;

        this.;

        this.updateCoreImports(bemitter);
        return enums;
    }

    private emitTIRTypedeclEntityType(): string {
        
    }

    private emitTIRObjectEntityType(): string {
        
    }

    private emitTIRPrimitiveInternalEntityType(): string {
        
    }

    private emitTIRValidatorEntityType(): string {
        
    }

    private emitTIRStringOfEntityType(): string {
        
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
