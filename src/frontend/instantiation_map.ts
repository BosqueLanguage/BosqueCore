import { TemplateNameMapper } from "./type.js";


class FunctionInstantiationInfo {
    binds: TemplateNameMapper[] | undefined;

    constructor(binds: TemplateNameMapper[] | undefined) {
        this.binds = binds;
    }

    static createNoTemplateInfo(): FunctionInstantiationInfo {
        return new FunctionInstantiationInfo(undefined);
    }
}

class MethodInstantiationInfo {
    binds: TemplateNameMapper[] | undefined;

    constructor(binds: TemplateNameMapper[] | undefined) {
        this.binds = binds;
    }

    static createNoTemplateInfo(): MethodInstantiationInfo {
        return new MethodInstantiationInfo(undefined);
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

    static createNoTemplateInfo(functionbinds: Map<string, FunctionInstantiationInfo>, methodbinds: Map<string, MethodInstantiationInfo>): TypeInstantiationInfo {
        return new TypeInstantiationInfo(undefined, functionbinds, methodbinds);
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
