import * as assert from "assert";
import * as path from "path";

import { TIRAssembly, TIRConstMemberDecl, TIREnumEntityType, TIRMemberFieldDecl, TIRMemberMethodDecl, TIRNamespaceConstDecl, TIRNamespaceDeclaration, TIRNamespaceFunctionDecl, TIROOType, TIRStaticFunctionDecl, TIRType, TIRTypeKey } from "../../../frontend/tree_ir/tir_assembly";
import { TIRLiteralValue } from "../../../frontend/tree_ir/tir_body";
import { BodyEmitter } from "./body_emitter";

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

    }

    private emitMemberFunction(ootype: TIROOType, cdecl: TIRStaticFunctionDecl): string {

    }

    private emitMemberField(ootype: TIROOType, cdecl: TIRMemberFieldDecl): string {
    }

    private emitMemberMethod(ootype: TIROOType, cdecl: TIRMemberMethodDecl): string {

    }

    private emitTIREnumEntityType(ttype: TIREnumEntityType): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const entries = ttype.enums.map((ee) => `${ee}: ${bemitter.emitExpression((ttype.litvals.get(ee) as TIRLiteralValue).exp)}`).join(",\n    ");
        const enums = `BSQ${ttype.tname.name} = {${entries}\n};`;

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
