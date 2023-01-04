import * as assert from "assert";
import * as path from "path";

import { TIRAssembly, TIREnumEntityType } from "../../../frontend/tree_ir/tir_assembly";
import { BodyEmitter } from "./body_emitter";

class AssemblyEmitter {
    private readonly m_assembly: TIRAssembly;

    constructor(assembly: TIRAssembly) {
        this.m_assembly = assembly;
    }

    private emitTIREnumEntityType(ttype: TIREnumEntityType): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile));
        
        const entries = ttype.enums.map((ee) => `${ee}: ${this.}`)
        const enums = `BSQ${ttype.tname.name} = `;
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

    private emitTIRTypedeclEntityType(): string {
        
    }

    private emitTIRObjectEntityType(): string {
        
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
}

export {
    AssemblyEmitter
};
