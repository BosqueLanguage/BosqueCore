import { SourceInfo } from "../build_decls";
import { Assembly } from "./assembly";
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

abstract class ParserTopLevelScope {
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

class StdParserFunctionScope extends ParserTopLevelScope {
    constructor(args: Set<string>, boundtemplates: Set<string>, rtype: TypeSignature | undefined) {
        super(args, boundtemplates, rtype);
    }
}

abstract class CapturingParserToplevelScope extends ParserTopLevelScope {
    capturedVars: Set<string>;
    capturedTemplates: Set<string>;

    constructor(args: Set<string>, boundtemplates: Set<string>, rtype: TypeSignature | undefined) {
        super(args, boundtemplates, rtype);

        this.capturedVars = new Set<string>();
        this.capturedTemplates = new Set<string>();
    }
}

class LambdaBodyParserScope extends CapturingParserToplevelScope {
    constructor(args: Set<string>, boundtemplates: Set<string>, rtype: TypeSignature | undefined) {
        super(args, boundtemplates, rtype);
    }
}

class ParserStandaloneExpressionScope extends CapturingParserToplevelScope {
    constructor(args: Set<string>, boundtemplates: Set<string>, rtype: TypeSignature | undefined) {
        super(args, boundtemplates, rtype);
    }
}

class FunctionScope {
    
    getCaptureVars(): Set<string> {
        return this.m_capturedvars;
    }

    getCaptureTemplates(): Set<string> {
        return this.m_capturedtemplates;
    }

    getBoundTemplates(): Set<string> {
        return this.m_boundtemplates;
    }

    getReturnType(): TypeSignature {
        return this.m_rtype;
    }
}

class ParserEnvironment {
    private m_currentFile: string | undefined;
    private m_currentNamespace: string | undefined;
    private m_taskenabled: boolean = false;

    private m_functionScopes: FunctionScope[];

    readonly assembly: Assembly;

    readonly SpecialAnySignature: TypeSignature;
    readonly SpecialSomeSignature: TypeSignature;
    readonly SpecialNoneSignature: TypeSignature;
    readonly SpecialBoolSignature: TypeSignature;
    
    readonly SpecialIntSignature: TypeSignature;
    readonly SpecialNatSignature: TypeSignature;
    readonly SpecialFloatSignature: TypeSignature;
    readonly SpecialDecimalSignature: TypeSignature;
    readonly SpecialBigIntSignature: TypeSignature;
    readonly SpecialBigNatSignature: TypeSignature;
    readonly SpecialRationalSignature: TypeSignature;
    readonly SpecialStringSignature: TypeSignature;

    readonly SpecialAutoSignature: TypeSignature;

    constructor(assembly: Assembly) {
        this.m_currentFile = undefined;
        this.m_currentNamespace = undefined;

        this.assembly = assembly;

        this.m_functionScopes = [];

        this.SpecialAnySignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), "Core", ["Any"], undefined);
        this.SpecialSomeSignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), "Core", ["Some"], undefined);
        this.SpecialNoneSignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), "Core", ["None"], undefined);
        this.SpecialBoolSignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), "Core", ["Bool"], undefined);

        this.SpecialIntSignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), "Core", ["Int"], undefined);
        this.SpecialNatSignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), "Core", ["Nat"], undefined);
        this.SpecialFloatSignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), "Core", ["Float"], undefined);
        this.SpecialDecimalSignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), "Core", ["Decimal"], undefined);
        this.SpecialBigIntSignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), "Core", ["BigInt"], undefined);
        this.SpecialBigNatSignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), "Core", ["BigNat"], undefined);
        this.SpecialRationalSignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), "Core", ["Rational"], undefined);
        this.SpecialStringSignature = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), "Core", ["String"], undefined);
        
        this.SpecialAutoSignature = new AutoTypeSignature(SourceInfo.implicitSourceInfo());
    }

    isFunctionScopeActive(): boolean {
        return this.m_functionScopes.length !== 0;
    }

    getCurrentFunctionScope(): FunctionScope {
        return this.m_functionScopes[this.m_functionScopes.length - 1];
    }

    pushFunctionScope(scope: FunctionScope) {
        this.m_functionScopes.push(scope);
    }

    popFunctionScope(): FunctionScope {
        return this.m_functionScopes.pop() as FunctionScope;
    }

    setNamespaceAndFile(ns: string, file: string) {
        this.m_currentFile = file;
        this.m_currentNamespace = ns;
        this.m_taskenabled = file.endsWith("bsqtask");
    }

    getCurrentFile(): string {
        return this.m_currentFile as string;
    }

    getCurrentNamespace(): string {
        return this.m_currentNamespace as string;
    }

    isVarDefinedInAnyScope(name: string): boolean {
        return this.m_functionScopes.some((sc) => sc.isVarNameDefined(name));
    }

    useLocalVar(name: string): string {
        if (this.isFunctionScopeActive()) {
            const oname = name;
            const cscope = this.getCurrentFunctionScope();

            if(oname === "$") {
                for (let i = this.m_functionScopes.length - 1; i >= 0; --i) {
                    if (this.m_functionScopes[i].isVarNameDefined(name)) {
                        this.m_functionScopes[i].markUsedImplicitBinder();
                    }
                }
            }

            if (name.startsWith("$")) {
                for (let i = this.m_functionScopes.length - 1; i >= 0; --i) {
                    if (this.m_functionScopes[i].isVarNameDefined(name)) {
                        name = this.m_functionScopes[i].getScopedVarName(name);
                        break;
                    }
                }
            }

            if (!cscope.isVarScopeResolvedNameDefined(name) && cscope.isPCodeEnv()) {
                cscope.getCaptureVars().add(name);
            }
        }
        
        return name;
    }

    useTemplateType(name: string): string {
        if (this.isFunctionScopeActive()) {
            const cscope = this.getCurrentFunctionScope();

            if (cscope.isPCodeEnv()) {
                if (!cscope.isTemplateNameDefined(name)) {
                    cscope.getCaptureTemplates().add(name);
                }
            }
        }

        return name;
    }

    tryResolveNamespace(ns: string | undefined, typename: string): string | undefined {
        if (ns !== undefined) {
            return ns;
        }

        const coredecl = this.assembly.getNamespace("Core");
        if (coredecl.declaredNames.has(typename)) {
            return "Core";
        }
        else {
            const nsdecl = this.assembly.getNamespace(this.m_currentNamespace as string);
            if (nsdecl.declaredNames.has(typename)) {
                return this.m_currentNamespace as string;
            }
            else {
                const fromns = nsdecl.usings.find((nsuse) => nsuse.names.indexOf(typename) !== -1);
                return fromns !== undefined ? fromns.fromns : undefined;
            }
        }
    }

    getBinderExtension(vname: string): string {
        return this.getCurrentFunctionScope().getBinderExtension(vname);
    }
}

export { 
    LocalScopeVariableInfo, LocalScopeInfo,
    ParserTopLevelScope, StdParserFunctionScope, CapturingParserToplevelScope, LambdaBodyParserScope, ParserStandaloneExpressionScope,
    ParserEnvironment 
};

