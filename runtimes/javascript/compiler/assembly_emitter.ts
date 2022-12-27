import * as assert from "assert";


class AssemblyEmitter {
    private readonly m_assembly: TIRAssembly;

    constructor(assembly: TIRAssembly, m_typeNameMap: Map<TIRTypeKey, string>) {
        this.m_assembly = assembly;
    }
    
    private generateJsNameForType(tt: TIRType) {
        xxxx;
    }

    private emitNameofOOType(tt: TIROOType): string {
        if (tt instanceof TIRListEntityType) {
            return `List$${this.getNameOfType(tt.typeT)}`
        }
        else if() {
            xxx;
        }
        else {
            return `${tt.tname.ns}$${tt.tname.name.replace(/::/g, "$")}$of$`; xxxx;
        }
    }
}

export {
    AssemblyEmitter
};
