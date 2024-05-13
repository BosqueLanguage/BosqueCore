
import {strict as assert} from "assert";

import { SourceInfo } from "../build_decls";
import { Assembly } from "./assembly";
import { NominalTypeSignature, TypeSignature, AutoTypeSignature, VoidTypeSignature } from "./type";

abstract class SourceNameDefinitionInfo {
    readonly srcname: string;

    constructor(srcname: string) {
        this.srcname = srcname;
    }

    abstract isConst(): boolean;
    abstract getScopedName(): string;

    abstract markUsed();
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

    markUsed() {
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

    markUsed() {
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
    readonly binders: BinderVariableDefinitionInfo[] = [];

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

    abstract getBinderVarName(srcname: string): string;

    /*
    isVarSourceNameDefined(name: string): boolean {
        return this.args.has(name) || this.localscope.some((frame) => frame.locals.some((nn) => nn.srcname === name));
    }

    isVarScopeResolvedNameDefined(name: string): boolean {
        return this.localscope.some((frame) => frame.locals.some((nn) => nn.scopedname === name));
    }

    isTemplateNameDefined(name: string): boolean {
        return this.boundtemplates.has(name);
    }

    getVarInfoForSourceNameTry(name: string): LocalScopeVariableInfo | undefined {
        for (let i = this.localscope.length - 1; i >= 0; --i) {
            const vinfo = this.localscope[i].locals.find((fr) => fr.srcname === name);
            if (vinfo !== undefined) {
                return vinfo;
            }
        }

        return undefined;
    }

    getResolvedVarName(srcname: string): string {
        const vinfo = this.getVarInfoForSourceNameTry(srcname);
        return vinfo !== undefined ? vinfo.scopedname : srcname;
    }

    markUsedImplicitBinderIfNeeded(srcname: string) {
        const vinfo = this.getVarInfoForSourceNameTry(srcname);
        if (vinfo !== undefined && vinfo.isbinder) {
            vinfo.isUsed = true;
        }
    }

    getUsedImplicitBinderFromThisDef(srcname: string): boolean {
        if(this.localscope.length !== 0) {
            return false;
        }

        const thisvinfo = this.localscope[this.localscope.length - 1].locals.find((fr) => fr.srcname === srcname);
        return thisvinfo !== undefined ? thisvinfo.isUsed : false;
    }

    defineLocalVar(name: string, scopedname: string, isconst: boolean, isbinder: boolean) {
        this.localscope[this.localscope.length - 1].locals.push(new LocalScopeVariableInfo(name, scopedname, isconst, isbinder));
    }
    */
}

class StandardScopeInfo extends ParserScopeInfo {
    constructor(args: LocalVariableDefinitionInfo[], boundtemplates: Set<string>, rtype: TypeSignature | undefined) {
        super(args, boundtemplates, rtype);
    }

    getBinderVarName(srcname: string): string {
        const ctr = this.getBinderVarName_helper(srcname);
        return "$_" + srcname + (ctr !== 0 ? "_" + ctr.toString() : "");
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
        return "$_" + srcname + (ctr !== 0 ? "_" + ctr.toString() : "");
    }
}

class ParserEnvironment {
    readonly assembly: Assembly;

    readonly currentFile: string;
    readonly currentNamespace: string;

    scope: ParserScopeInfo | undefined;

    readonly SpecialVoidSignature: TypeSignature;
    readonly SpecialAutoSignature: TypeSignature;

    readonly wellknownTypes: Map<string, NominalTypeSignature>;

    constructor(assembly: Assembly, currentFile: string, currentNamespace: string, wellknownTypes: Map<string, NominalTypeSignature>) {
        this.assembly = assembly;

        this.currentFile = currentFile;
        this.currentNamespace = currentNamespace;

        this.scope = undefined;

        this.SpecialVoidSignature = new VoidTypeSignature(SourceInfo.implicitSourceInfo());
        this.SpecialAutoSignature = new AutoTypeSignature(SourceInfo.implicitSourceInfo());

        this.wellknownTypes = wellknownTypes;
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

    popBinderExpressionScope(): string[] {
        assert(this.scope !== undefined);
        
        return (this.scope.blockscope.pop() as BinderBlockScopeInfo).binders.filter((b) => b.isUsed).map((b) => b.srcname);
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

    useVariable(srcname: string): string {
        assert(this.scope !== undefined);

        xxxx;
    }

    /*
    isVarDefinedInAnyScope(srcname: string): boolean {
        return this.enclosingScope.isVarSourceNameDefined(srcname) || this.nestedScopes.some((sc) => sc.isVarSourceNameDefined(srcname));
    }

    useLocalVar(srcname: string): string {
        let rname: string | undefined = undefined;
        if (srcname.startsWith("$")) {
            for (let i = this.nestedScopes.length - 1; i >= 0; --i) {
                if (this.nestedScopes[i].isVarSourceNameDefined(srcname)) {
                    rname = this.nestedScopes[i].getResolvedVarName(srcname);
                    break;
                }
            }

            if(rname === undefined) {
                rname = this.enclosingScope.getResolvedVarName(srcname);
            }
        }
        else {
            rname = srcname;
        }

        const cscope = this.getCurrentFunctionScope();
        if (!cscope.isVarScopeResolvedNameDefined(srcname) && (cscope instanceof CapturingParserScope)) {
            cscope.capturedVars.add(rname);
        }
        
        return rname;
    }
    */
}

export { 
    SourceNameDefinitionInfo, LocalVariableDefinitionInfo, BinderVariableDefinitionInfo,
    BlockScopeInfo, SimpleBlockScopeInfo, BinderBlockScopeInfo,
    ParserScopeInfo, StandardScopeInfo, LambdaScopeInfo,
    ParserEnvironment 
};

