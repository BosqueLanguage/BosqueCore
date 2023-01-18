//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo } from "../build_decls";
import { Assembly } from "./assembly";
import { NominalTypeSignature, TypeSignature, AutoTypeSignature } from "./type";

class FunctionScope {
    private readonly m_rtype: TypeSignature;
    private m_capturedvars: Set<string>;
    private m_capturedtemplates: Set<string>;

    private readonly m_ispcode: boolean;
    private readonly m_args: Set<string>;
    private readonly m_boundtemplates: Set<string>;
    private m_locals: { name: string, scopedname: string, isbinder: boolean }[][];

    constructor(args: Set<string>, boundtemplates: Set<string>, rtype: TypeSignature, ispcode: boolean) {
        this.m_rtype = rtype;
        this.m_capturedvars = new Set<string>();
        this.m_capturedtemplates = new Set<string>();
        this.m_ispcode = ispcode;
        this.m_args = args;
        this.m_boundtemplates = boundtemplates;
        this.m_locals = [];
    }

    pushLocalScope() {
        this.m_locals.push([]);
    }

    popLocalScope() {
        this.m_locals.pop();
    }

    isPCodeEnv(): boolean {
        return this.m_ispcode;
    }

    isVarNameDefined(name: string): boolean {
        return this.m_args.has(name) || this.m_locals.some((frame) => frame.some((nn) => nn.name === name));
    }

    isTemplateNameDefined(name: string): boolean {
        return this.m_boundtemplates.has(name);
    }

    getScopedVarName(name: string): string {
        for (let i = this.m_locals.length - 1; i >= 0; --i) {
            const vinfo = this.m_locals[i].find((fr) => fr.name === name);
            if (vinfo !== undefined) {
                return vinfo.scopedname;
            }
        }

        return name;
    }

    defineLocalVar(name: string, scopedname: string, isbinder: boolean) {
        this.m_locals[this.m_locals.length - 1].push({ name: name, scopedname: scopedname, isbinder: isbinder });
    }

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

    taskOpsOk(): boolean {
        return this.m_taskenabled;
    }

    isVarDefinedInAnyScope(name: string): boolean {
        return this.m_functionScopes.some((sc) => sc.isVarNameDefined(name));
    }

    useLocalVar(name: string): string {
        if (this.isFunctionScopeActive()) {
            const cscope = this.getCurrentFunctionScope();

            if (name === "$") {
                for (let i = this.m_functionScopes.length - 1; i >= 0; --i) {
                    if (this.m_functionScopes[i].isVarNameDefined(name)) {
                        name = this.m_functionScopes[i].getScopedVarName(name);
                        break;
                    }
                }
            }

            if (!cscope.isVarNameDefined(name) && cscope.isPCodeEnv()) {
                cscope.getCaptureVars().add(name);
            }
        }
        
        return name;
    }

    useTemplateType(name: string): string {
        if (this.isFunctionScopeActive()) {
            const cscope = this.getCurrentFunctionScope();

            if (!cscope.isTemplateNameDefined(name) && cscope.isPCodeEnv()) {
                cscope.getCaptureTemplates().add(name);
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

    getBinderExtension(): string {
        if (this.isFunctionScopeActive()) {
            let bcount = 0;

            for (let i = this.m_functionScopes.length - 1; i >= 0; --i) {
                if (this.m_functionScopes[i].isVarNameDefined("$")) {
                    bcount++;
                }
            }

            return bcount.toString();
        }
        
        return "0";
    }
}

export { FunctionScope, ParserEnvironment };
