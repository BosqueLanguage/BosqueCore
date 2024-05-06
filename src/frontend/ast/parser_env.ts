import { SourceInfo } from "../build_decls";
import { Assembly, NamespaceDeclaration, TypeDecl } from "./assembly";
import { NominalTypeSignature, TypeSignature, AutoTypeSignature } from "./type";

class LocalScopeVariableInfo {
    readonly srcname: string;
    readonly scopedname: string;
    readonly isbinder: boolean;
    isUsed: boolean;

    constructor(srcname: string, scopedname: string, isbinder: boolean) {
        this.srcname = srcname;
        this.scopedname = scopedname;
        this.isbinder = isbinder;
        this.isUsed = false;
    }
}

class LocalScopeInfo {
    locals: LocalScopeVariableInfo[];

    constructor(locals: LocalScopeVariableInfo[]) {
        this.locals = locals;
    }
}

abstract class ParserScope {
    readonly resultingType: TypeSignature | undefined; //undefined if this is a void call
    
    readonly args: Set<string>;
    readonly boundtemplates: Set<string>;
 
    readonly localscope: LocalScopeInfo[];

    constructor(args: Set<string>, boundtemplates: Set<string>, rtype: TypeSignature | undefined) {
        this.args = args;
        this.boundtemplates = boundtemplates;
        this.resultingType = rtype;
        this.localscope = [];
    }

    pushLocalScope() {
        this.localscope.push(new LocalScopeInfo([]));
    }

    popLocalScope() {
        this.localscope.pop();
    }

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

    getBinderExtension(srcname: string): string {
        let bcount = 0;

        for (let i = this.localscope.length - 1; i >= 0; --i) {
            const vinfo = this.localscope[i].locals.find((fr) => fr.srcname === srcname);
            if (vinfo !== undefined) {
                bcount++;
            }
        }

        return bcount.toString();
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

    defineLocalVar(name: string, scopedname: string, isbinder: boolean) {
        this.localscope[this.localscope.length - 1].locals.push(new LocalScopeVariableInfo(name, scopedname, isbinder));
    }
}

class DeclLevelParserScope extends ParserScope {
    constructor() {
        super(new Set<string>(), new Set<string>(), undefined);
    }
}

abstract class CapturingParserScope extends ParserScope {
    capturedVars: Set<string>;
    capturedTemplates: Set<string>;

    constructor(args: Set<string>, boundtemplates: Set<string>, rtype: TypeSignature) {
        super(args, boundtemplates, rtype);

        this.capturedVars = new Set<string>();
        this.capturedTemplates = new Set<string>();
    }
}

class LambdaBodyParserScope extends CapturingParserScope {
    constructor(args: Set<string>, boundtemplates: Set<string>, rtype: TypeSignature) {
        super(args, boundtemplates, rtype);
    }
}

class ParserStandaloneExpressionScope extends CapturingParserScope {
    constructor(args: Set<string>, boundtemplates: Set<string>, rtype: TypeSignature) {
        super(args, boundtemplates, rtype);
    }
}

class StdParserFunctionScope extends CapturingParserScope {
    constructor(args: Set<string>, boundtemplates: Set<string>, rtype: TypeSignature) {
        super(args, boundtemplates, rtype);
    }
}

class ParserEnvironment {
    readonly assembly: Assembly;

    readonly currentFile: string;
    readonly currentNamespace: string;

    enclosingScope: ParserScope;
    nestedScopes: CapturingParserScope[];

    readonly SpecialVoidSignature: TypeSignature;

    readonly SpecialAnySignature: TypeSignature;
    readonly SpecialSomeSignature: TypeSignature;
    readonly SpecialNoneSignature: TypeSignature;
    readonly SpecialBoolSignature: TypeSignature;

    readonly SpecialAutoSignature: TypeSignature;

    constructor(assembly: Assembly, currentFile: string, currentNamespace: string, startScope: ParserScope) {
        this.assembly = assembly;

        this.currentFile = currentFile;
        this.currentNamespace = currentNamespace;

        this.enclosingScope = startScope;
        this.nestedScopes = [];

        this.SpecialVoidSignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), ["Core"], [{tname: "Void", terms: []}]);

        this.SpecialAnySignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), ["Core"], [{tname: "Any", terms: []}]);
        this.SpecialSomeSignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), ["Core"], [{tname: "Some", terms: []}]);

        this.SpecialNoneSignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), ["Core"], [{tname: "None", terms: []}]);
        this.SpecialNoneSignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), ["Core"], [{tname: "Nothing", terms: []}]);
        this.SpecialBoolSignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), ["Core"], [{tname: "Bool", terms: []}]);
        
        this.SpecialAutoSignature = new AutoTypeSignature(SourceInfo.implicitSourceInfo());
    }

    getCurrentFunctionScope(): ParserScope {
        return this.nestedScopes.length !== 0 ? this.nestedScopes[this.nestedScopes.length - 1] : this.enclosingScope;
    }

    pushFunctionScope(scope: CapturingParserScope) {
        this.nestedScopes.push(scope);
    }

    popFunctionScope(): CapturingParserScope {
        return this.nestedScopes.pop() as CapturingParserScope;
    }

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

    useTemplateType(tname: string): string {
        const cscope = this.getCurrentFunctionScope();

        if (cscope instanceof CapturingParserScope) {
            if (!cscope.isTemplateNameDefined(tname)) {
                cscope.capturedTemplates.add(tname);
            }
        }

        return tname;
    }

    private resolveImplicitNamespaceRootRecursive(fromns: NamespaceDeclaration, access: {tname: string, terms: TypeSignature[]}[]): [NamespaceDeclaration, {tname: string, terms: TypeSignature[]}[]] | undefined {
        if(access.length === 1) {
            const nns = fromns.subns.find((ns) => ns.name === access[0].tname);
            if(nns !== undefined) {
                return [nns, []];
            }
            else if(fromns.declaredNames.has(access[0].tname)) {
                return [fromns, access];
            }
            else {
                return undefined;
            }
        }
        else {
            const nsdecl = fromns.subns.find((ns) => ns.name === access[0].tname);
            return nsdecl !== undefined ? this.resolveImplicitNamespaceRootRecursive(nsdecl, scopedname.slice(1), declname) : undefined;    
        }
    }

    resolveEnclosingNamespaceInfo(fromns: NamespaceDeclaration, access: {tname: string, terms: TypeSignature[]}[]): [NamespaceDeclaration, {tname: string, terms: TypeSignature[]}[]]  | undefined {
        const coredecl = this.assembly.getToplevelNamespace("Core");

        //If core is explicit then we can skip any local lookup
        if (scopedname.length === 1 && scopedname[0] === "Core") {
            return coredecl.declaredNames.has(declname) ? this.assembly.getToplevelNamespace("Core") : undefined;
        }

        //if the scoped then we are looking for a specific decl in Core or in this namespace
        if (scopedname.length === 0) {
            if(coredecl.declaredNames.has(declname)) {
                return coredecl;
            }
            else {
                return fromns.declaredNames.has(declname) ? fromns : undefined;
            }
        }
        else {
            //we are doing a recursive search -- check any usings for the first item and then start the search

            const usingns = fromns.usings.find((nsuse) => nsuse.asns === scopedname[0])?.fromns.ns || [fromns.name];
            
            //TODO: we need to check that usingns is not Core or the current namespace -- which we should have already checked
            return this.resolveImplicitNamespaceRootRecursive(fromns, [...usingns, ...scopedname.slice(1)], declname);
        }
    }

    getBinderExtension(vname: string): string {
        return this.getCurrentFunctionScope().getBinderExtension(vname);
    }
}

export { 
    LocalScopeVariableInfo, LocalScopeInfo,
    ParserScope, DeclLevelParserScope, StdParserFunctionScope, CapturingParserScope, LambdaBodyParserScope, ParserStandaloneExpressionScope,
    ParserEnvironment 
};

