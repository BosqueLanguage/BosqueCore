import { IRAssembly } from "./irassembly.js";

/*
    For now I plan to write this all in its own file. What we will want is a copy of the current IRAssembly
    for which we emit each fields corresponding BAPI representation, packing into a BSQAssembly::Assembly
    object that is then fed into the SMTEmitter... (at least I believe this is the idea)
*/
function emitIRAssembly(asm: IRAssembly): string {
    let v = asm.entities.map<string>(e => e.emitBAPI()); 
    return v.join();
}

export {
    emitIRAssembly
};