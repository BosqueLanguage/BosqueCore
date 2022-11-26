import * as assert from "assert";

import { TIRAssembly, TIROOType } from "../../../frontend/tree_ir/tir_assembly";

class TypeEmitter {
    private readonly m_assembly: TIRAssembly;

    constructor(assembly: TIRAssembly) {
        this.m_assembly = assembly;
    }

    private emitNameofType(tt: TIROOType): string {
        return `${tt.tname.ns}$${tt.tname.name.replace(/::/g, "$")}$of$`; xxxx;
    }
}

export {
    TypeEmitter
};
