
import {strict as assert} from "assert";

import { SourceInfo } from "./build_decls";
import { Assembly, NamespaceDeclaration } from "./assembly";
import { TypeSignature, AutoTypeSignature, VoidTypeSignature } from "./type";

abstract class SourceNameDefinitionInfo {
    readonly srcname: string;

    constructor(srcname: string) {
        this.srcname = srcname;
    }

    abstract isConst(): boolean;
    abstract getScopedName(): string;

    abstract markUsed(): void;
}

class LocalVariableDefinitionInfo extends SourceNameDefinitionInfo {
    readonly isconst: boolean;

    constructor(srcname: string, isconst: boolean) {
        super(srcname);
        this.isconst = isconst;
    }

    isConst(): boolean {
        return this.isconst;
    }
    getScopedName(): string {
        return this.srcname;
    }

    markUsed(): void {
        ;
    }
}

class BinderVariableDefinitionInfo extends SourceNameDefinitionInfo {
    readonly scopedname: string;
    isUsed: boolean = false;

    constructor(srcname: string, scopedname: string) {
        super(srcname);
        this.scopedname = scopedname;
    }

    isConst(): boolean {
        return true;
    }
    getScopedName(): string {
        return this.scopedname;
    }

    markUsed(): void {
        this.isUsed = true;
    }
}

abstract class BlockScopeInfo {
    locals: LocalVariableDefinitionInfo[] = [];

    abstract lookupVariableInfo(srcname: string): SourceNameDefinitionInfo | undefined;
    abstract definesBinderSourceName(srcname: string): boolean;
}

class SimpleBlockScopeInfo extends BlockScopeInfo {
    constructor() {
        super();
    }

    lookupVariableInfo(srcname: string): SourceNameDefinitionInfo | undefined {
        return this.locals.find((nn) => nn.srcname === srcname);
    }

    definesBinderSourceName(srcname: string): boolean {
        return false;
    }
}

class BinderBlockScopeInfo extends BlockScopeInfo {
    readonly binders: BinderVariableDefinitionInfo[];

    constructor(binders: BinderVariableDefinitionInfo[]) {
        super();

        this.binders = binders;
    }

    lookupVariableInfo(srcname: string): SourceNameDefinitionInfo | undefined {
        return this.locals.find((nn) => nn.srcname === srcname) || this.binders.find((nn) => nn.srcname === srcname);
    }

    definesBinderSourceName(srcname: string): boolean {
        return this.binders.find((nn) => nn.srcname === srcname) !== undefined;
    }
}

class BinderUnknownInConstantScopeInfo extends BlockScopeInfo {
    readonly binders: BinderVariableDefinitionInfo[] = [];

    constructor() {
        super();
    }

    lookupVariableInfo(srcname: string): SourceNameDefinitionInfo | undefined {
        const idecl = this.locals.find((nn) => nn.srcname === srcname) || this.binders.find((nn) => nn.srcname === srcname);
        if(idecl !== undefined) {
            return idecl;
        }

        if(srcname.startsWith("$")) {
            this.binders.push(new BinderVariableDefinitionInfo(srcname, srcname));
        }
        return this.binders.find((nn) => nn.srcname === srcname);
    }

    definesBinderSourceName(srcname: string): boolean {
        return srcname.startsWith("$");
    }
}

abstract class ParserScopeInfo {
    readonly resultingType: TypeSignature | undefined; //undefined if this is a void call or an expression we don't know the type of
    
    readonly args: LocalVariableDefinitionInfo[];
    readonly boundtemplates: Set<string>;
 
    readonly blockscope: BlockScopeInfo[];

    constructor(args: LocalVariableDefinitionInfo[], boundtemplates: Set<string>, rtype: TypeSignature | undefined) {
        this.args = args;
        this.boundtemplates = boundtemplates;
        this.resultingType = rtype;
        this.blockscope = [new SimpleBlockScopeInfo()];
    }

    pushBlockScope() {
        this.blockscope.push(new SimpleBlockScopeInfo());
    }

    popBlockScope() {
        this.blockscope.pop();
    }

    pushBinderBlockScope(binders: BinderVariableDefinitionInfo[]) {
        this.blockscope.push(new BinderBlockScopeInfo(binders));
    }

    popBinderBlockScope(): BinderBlockScopeInfo {
        return this.blockscope.pop() as BinderBlockScopeInfo;
    }

    getBinderVarName_helper(srcname: string): number {
        let bcount = 0;

        for (let i = this.blockscope.length - 1; i >= 0; --i) {
            if (this.blockscope[i].definesBinderSourceName(srcname)) {
                bcount++;
            }
        }

        if(this.args.some((arg) => arg.srcname === srcname)) {
            bcount++;
        }

        return bcount;
    }

    checkCanDeclareLocalVar(srcname: string): boolean {
        return this.blockscope.every((bs) => bs.lookupVariableInfo(srcname) !== undefined) && ! this.args.some((arg) => arg.srcname === srcname);
    }

    checkCanAssignVariable(srcname: string): boolean {
        //can't assign to a binder (so dont even check there) and can't assign to any lambda captures so no need to check there either
        for (let i = this.blockscope.length - 1; i >= 0; --i) {
            const vinfo = this.blockscope[i].lookupVariableInfo(srcname);
            if (vinfo !== undefined && !vinfo.isConst) {
                return true;
            }
        }

        const argi = this.args.find((arg) => arg.srcname === srcname);
        return argi !== undefined && !argi.isConst;
    }

    useVariable_helper(srcname: string): string | undefined {
        for (let i = this.blockscope.length - 1; i >= 0; --i) {
            const vv = this.blockscope[i].lookupVariableInfo(srcname);
            if(vv !== undefined) {
                vv.markUsed();
                return vv.getScopedName();
            }
        }

        if(this.args.some((arg) => arg.srcname === srcname)) {
            return srcname;
        }

        return undefined;
    }

    abstract getBinderVarName(srcname: string): string;

    abstract useVariable(srcname: string): [string, boolean] | undefined;
}

class StandardScopeInfo extends ParserScopeInfo {
    constructor(args: LocalVariableDefinitionInfo[], boundtemplates: Set<string>, rtype: TypeSignature | undefined) {
        super(args, boundtemplates, rtype);
    }

    getBinderVarName(srcname: string): string {
        const ctr = this.getBinderVarName_helper(srcname);
        return srcname + (ctr !== 0 ? "_" + ctr.toString() : "");
    }

    useVariable(srcname: string): [string, boolean] | undefined {
        const rname = this.useVariable_helper(srcname);
        if(rname !== undefined) {
            return [rname, false];
        }

        return undefined;
    }
}

class LambdaScopeInfo extends ParserScopeInfo {
    readonly enclosing: ParserScopeInfo;

    readonly capturedVars: Set<string> = new Set<string>();

    constructor(args: LocalVariableDefinitionInfo[], boundtemplates: Set<string>, rtype: TypeSignature | undefined, enclosing: ParserScopeInfo) {
        super(args, boundtemplates, rtype);

        this.enclosing = enclosing;
    }

    getBinderVarName(srcname: string): string {
        const ctr = (this.enclosing.getBinderVarName_helper(srcname) + this.getBinderVarName_helper(srcname));
        return srcname + (ctr !== 0 ? "_" + ctr.toString() : "");
    }

    useVariable(srcname: string): [string, boolean] | undefined {
        const rname = this.useVariable_helper(srcname);
        if(rname !== undefined) {
            return [rname, false];
        }

        const rvar = this.enclosing.useVariable(srcname);
        if(rvar !== undefined) {
            this.capturedVars.add(srcname);
            return [rvar[0], true];
        }

        return undefined;
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

    private getBinderVarName(vname: string): string {
        assert(this.scope !== undefined);
        return this.scope.getBinderVarName(vname);
    }

    getScope(): ParserScopeInfo {
        assert(this.scope !== undefined);
        return this.scope;
    }

    pushStandardBlockScope() {
        assert(this.scope !== undefined);
        this.scope.blockscope.push(new SimpleBlockScopeInfo());
    }

    popStandardBlockScope() {
        assert(this.scope !== undefined);
        this.scope.blockscope.pop();
    }

    pushBinderExpressionScope(bindernames: string[]) {
        assert(this.scope !== undefined);

        const bscope = new BinderBlockScopeInfo(bindernames.map((b) => {
            return new BinderVariableDefinitionInfo(b, this.getBinderVarName(b));
        }));
        
        this.scope.blockscope.push(bscope);
    }

    popBinderExpressionScope(): {srcname: string, scopedname: string}[] {
        assert(this.scope !== undefined);
        
        return (this.scope.blockscope.pop() as BinderBlockScopeInfo).binders.filter((b) => b.isUsed).map((b) => {
            return {srcname: b.srcname, scopedname: b.scopedname};
        });
    }

    pushBinderUnknownInConstantExpressionScope() {
        assert(this.scope !== undefined);

        const bscope = new BinderUnknownInConstantScopeInfo();
        this.scope.blockscope.push(bscope);
    }

    popBinderUnknownInConstantExpressionScope(): string[] {
        assert(this.scope !== undefined);
        
        return (this.scope.blockscope.pop() as BinderUnknownInConstantScopeInfo).binders.filter((b) => b.isUsed).map((b) => b.srcname);
    }

    identifierResolvesAsVariable(srcname: string): boolean {
        assert(this.scope !== undefined);

        return this.scope.useVariable(srcname) !== undefined;
    }

    addVariable(srcname: string, isconst: boolean): boolean {
        assert(this.scope !== undefined);

        if(!this.scope.checkCanDeclareLocalVar(srcname)) {
            return false;
        }

        this.scope.blockscope[this.scope.blockscope.length - 1].locals.push(new LocalVariableDefinitionInfo(srcname, isconst));
        return true;
    }

    assignVariable(srcname: string): boolean {
        assert(this.scope !== undefined);

        return this.scope.checkCanAssignVariable(srcname);
    }

    useVariable(srcname: string): [string, boolean] | undefined {
        assert(this.scope !== undefined);

        return this.scope.useVariable(srcname);
    }

    isTemplateNameDefined(name: string): boolean {
        assert(this.scope !== undefined);

        return this.scope.boundtemplates.has(name);
    }

    pushLambdaScope(args: LocalVariableDefinitionInfo[], rtype: TypeSignature | undefined): LambdaScopeInfo {
        assert(this.scope !== undefined);

        this.scope = new LambdaScopeInfo(args, this.scope.boundtemplates, rtype, this.scope);
        return this.scope as LambdaScopeInfo;
    }

    popLambdaScope() {
        assert(this.scope !== undefined);
        assert(this.scope instanceof LambdaScopeInfo);

        this.scope = (this.scope as LambdaScopeInfo).enclosing;
    }

    pushStandardFunctionScope(args: LocalVariableDefinitionInfo[], terms: Set<string>, rtype: TypeSignature | undefined) {
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
    SourceNameDefinitionInfo, LocalVariableDefinitionInfo, BinderVariableDefinitionInfo,
    BlockScopeInfo, SimpleBlockScopeInfo, BinderBlockScopeInfo, BinderUnknownInConstantScopeInfo,
    ParserScopeInfo, StandardScopeInfo, LambdaScopeInfo,
    ParserEnvironment 
};

