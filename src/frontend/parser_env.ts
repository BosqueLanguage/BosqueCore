
import assert from "node:assert";

import { SourceInfo } from "./build_decls.js";
import { Assembly, NamespaceDeclaration } from "./assembly.js";
import { TypeSignature, AutoTypeSignature, VoidTypeSignature } from "./type.js";

function isDeclAssignable(declkind: "var" | "ref" | "let" | "out" | "out?" | "inout"): boolean {
    return declkind === "var" || declkind === "out" || declkind === "out?" || declkind === "inout";
}

class VariableDefinitionInfo {
    readonly vkind: "var" | "ref" | "let" | "out" | "out?" | "inout";
    readonly name: string;


    constructor(vkind: "var" | "ref" | "let" | "out" | "out?" | "inout", name: string) {
        this.vkind = vkind;
        this.name = name;
    }
}

class BlockScopeInfo {
    locals: VariableDefinitionInfo[] = [];

    lookupVariableInfo(name: string): VariableDefinitionInfo | undefined {
        return this.locals.find((nn) => nn.name === name);
    }
}

abstract class ParserScopeInfo {
    readonly resultingType: TypeSignature | undefined; //undefined if this is a void call or an expression we don't know the type of
    
    readonly args: VariableDefinitionInfo[];
    readonly boundtemplates: Set<string>;
 
    readonly blockscope: BlockScopeInfo[];

    constructor(args: VariableDefinitionInfo[], boundtemplates: Set<string>, rtype: TypeSignature | undefined) {
        this.args = args;
        this.boundtemplates = boundtemplates;
        this.resultingType = rtype;
        this.blockscope = [new BlockScopeInfo()];
    }

    pushBlockScope() {
        this.blockscope.push(new BlockScopeInfo());
    }

    popBlockScope() {
        this.blockscope.pop();
    }

    checkCanDeclareLocalVar(name: string): boolean {
        if(name === "_" || name === "this" || name === "self" || name.startsWith("$")) {
            return false;
        }

        const islocalredecl = this.blockscope.some((bs) => bs.lookupVariableInfo(name) !== undefined);
        const isargredecl = this.args.some((arg) => arg.name === name);

        return !islocalredecl && !isargredecl;
    }

    checkCanAssignVariable(name: string): boolean {
        if(name === "_" || name === "this" || name === "self" || name.startsWith("$")) {
            return false;
        }

        //can't assign to a binder (so dont even check there) and can't assign to any lambda captures so no need to check there either
        for (let i = this.blockscope.length - 1; i >= 0; --i) {
            const vinfo = this.blockscope[i].lookupVariableInfo(name);
            if (vinfo !== undefined) {
                return isDeclAssignable(vinfo.vkind);
            }
        }

        const argi = this.args.find((arg) => arg.name === name);
        return argi !== undefined && isDeclAssignable(argi.vkind);
    }

    isDefinedVariable_helper(name: string): boolean{
        for (let i = this.blockscope.length - 1; i >= 0; --i) {
            const vv = this.blockscope[i].lookupVariableInfo(name);
            if(vv !== undefined) {
                return true;
            }
        }

        if(this.args.some((arg) => arg.name === name)) {
            return true;
        }

        return false;
    }

    abstract isDefinedVariable(srcname: string): boolean;
}

class StandardScopeInfo extends ParserScopeInfo {
    constructor(args: VariableDefinitionInfo[], boundtemplates: Set<string>, rtype: TypeSignature | undefined) {
        super(args, boundtemplates, rtype);
    }

    override isDefinedVariable(srcname: string): boolean {
        return this.isDefinedVariable_helper(srcname);
    }
}

class LambdaScopeInfo extends ParserScopeInfo {
    readonly enclosing: ParserScopeInfo;

    constructor(args: VariableDefinitionInfo[], boundtemplates: Set<string>, rtype: TypeSignature | undefined, enclosing: ParserScopeInfo) {
        super(args, boundtemplates, rtype);

        this.enclosing = enclosing;
    }

    override isDefinedVariable(srcname: string): boolean {
        const tdef = this.isDefinedVariable_helper(srcname);
        if(tdef) {
            return true;
        }
        else {
            return this.enclosing.isDefinedVariable(srcname);
        }
    }
}

class ParserEnvironment {
    readonly assembly: Assembly;

    readonly currentFile: string;
    currentNamespace: NamespaceDeclaration;

    scope: ParserScopeInfo | undefined;

    readonly SpecialVoidSignature: TypeSignature;
    readonly SpecialAutoSignature: TypeSignature;

    constructor(assembly: Assembly, currentFile: string, currentNamespace: NamespaceDeclaration) {
        this.assembly = assembly;

        this.currentFile = currentFile;
        this.currentNamespace = currentNamespace;

        this.scope = undefined;

        this.SpecialVoidSignature = new VoidTypeSignature(SourceInfo.implicitSourceInfo());
        this.SpecialAutoSignature = new AutoTypeSignature(SourceInfo.implicitSourceInfo());
    }

    getScope(): ParserScopeInfo {
        assert(this.scope !== undefined);
        return this.scope;
    }

    pushBlockScope() {
        assert(this.scope !== undefined);
        this.scope.blockscope.push(new BlockScopeInfo());
    }

    popBlockScope() {
        assert(this.scope !== undefined);
        this.scope.blockscope.pop();
    }

    identifierResolvesAsVariable(srcname: string): boolean {
        assert(this.scope !== undefined);

        return srcname.startsWith("$") || this.scope.isDefinedVariable(srcname);
    }

    addVariable(name: string, vkind: "var" | "ref" | "let" | "out" | "out?" | "inout", ignoreok: boolean): boolean {
        assert(this.scope !== undefined);

        if(name === "_") {
            return ignoreok;
        }
        else {
            if(!this.scope.checkCanDeclareLocalVar(name)) {
                return false;
            }

            this.scope.blockscope[this.scope.blockscope.length - 1].locals.push(new VariableDefinitionInfo(vkind, name));
            return true;
        }
    }

    assignVariable(srcname: string): boolean {
        assert(this.scope !== undefined);

        if(srcname === "_") {
            return true;
        }
        else {
            return this.scope.checkCanAssignVariable(srcname);
        }
    }

    isTemplateNameDefined(name: string): boolean {
        assert(this.scope !== undefined);

        return this.scope.boundtemplates.has(name);
    }

    pushLambdaScope(args: VariableDefinitionInfo[], rtype: TypeSignature | undefined) {
        assert(this.scope !== undefined);

        this.scope = new LambdaScopeInfo(args, this.scope.boundtemplates, rtype, this.scope);
    }

    popLambdaScope() {
        assert(this.scope !== undefined);
        assert(this.scope instanceof LambdaScopeInfo);

        this.scope = (this.scope as LambdaScopeInfo).enclosing;
    }

    pushStandardFunctionScope(args: VariableDefinitionInfo[], terms: Set<string>, rtype: TypeSignature | undefined) {
        assert(this.scope === undefined);

        this.scope = new StandardScopeInfo(args, terms, rtype);
    }

    popStandardFunctionScope() {
        assert(this.scope !== undefined);
        assert(this.scope instanceof StandardScopeInfo);

        this.scope = undefined;
    }
}

export { 
    VariableDefinitionInfo,
    BlockScopeInfo,
    ParserScopeInfo, StandardScopeInfo, LambdaScopeInfo,
    ParserEnvironment 
};

