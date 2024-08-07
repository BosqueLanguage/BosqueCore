import { TemplateNameMapper } from "./type.js";


class FunctionInstantiationInfo {
    binds: TemplateNameMapper[] | undefined;

    constructor(binds: TemplateNameMapper[] | undefined) {
        this.binds = binds;
    }
}

class MethodInstantiationInfo {
    binds: TemplateNameMapper[] | undefined;

    constructor(binds: TemplateNameMapper[] | undefined) {
        this.binds = binds;
    }
}

class TypeInstantiationInfo {
    binds: TemplateNameMapper | undefined;
    functionbinds: Map<string, FunctionInstantiationInfo>;
    methodbinds: Map<string, MethodInstantiationInfo>;

    constructor(binds: TemplateNameMapper | undefined, functionbinds: Map<string, FunctionInstantiationInfo>, methodbinds: Map<string, MethodInstantiationInfo>) {
        this.binds = binds;

        this.functionbinds = functionbinds;
        this.methodbinds = methodbinds;
    }
}

class AssemblyInstantiationInfo {
    functionbinds: Map<string, FunctionInstantiationInfo>;
    typebinds: Map<string, TypeInstantiationInfo[]>;

    constructor(functionbinds: Map<string, FunctionInstantiationInfo>, typebinds: Map<string, TypeInstantiationInfo[]>) {
        this.functionbinds = functionbinds;
        this.typebinds = typebinds;
    }
}


export {
    FunctionInstantiationInfo,
    MethodInstantiationInfo,
    TypeInstantiationInfo,
    AssemblyInstantiationInfo
};
