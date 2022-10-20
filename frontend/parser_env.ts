//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Assembly } from "./assembly";
import { NominalTypeSignature, TypeSignature, AutoTypeSignature } from "./type_signature";

class FunctionScope {
    private readonly m_rtype: TypeSignature;
    private m_capturedvars: Set<string>;
    private m_capturedtemplates: Set<string>;

    private readonly m_ispcode: boolean;
    private readonly m_args: Set<string>;
    private readonly m_boundtemplates: Set<string>;
    private m_locals: string[][];

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
        return this.m_args.has(name) || this.m_locals.some((frame) => frame.some((nn) => nn === name));
    }

    isTemplateNameDefined(name: string): boolean {
        return this.m_boundtemplates.has(name);
    }

    defineLocalVar(name: string) {
        this.m_locals[this.m_locals.length - 1].push(name);
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

        this.SpecialAnySignature = new NominalTypeSignature("Core", ["Any"], []);
        this.SpecialSomeSignature = new NominalTypeSignature("Core", ["Some"], []);
        this.SpecialNoneSignature = new NominalTypeSignature("Core", ["None"], []);
        this.SpecialBoolSignature = new NominalTypeSignature("Core", ["Bool"], []);

        this.SpecialIntSignature = new NominalTypeSignature("Core", ["Int"], []);
        this.SpecialNatSignature = new NominalTypeSignature("Core", ["Nat"], []);
        this.SpecialFloatSignature = new NominalTypeSignature("Core", ["Float"], []);
        this.SpecialDecimalSignature = new NominalTypeSignature("Core", ["Decimal"], []);
        this.SpecialBigIntSignature = new NominalTypeSignature("Core", ["BigInt"], []);
        this.SpecialBigNatSignature = new NominalTypeSignature("Core", ["BigNat"], []);
        this.SpecialRationalSignature = new NominalTypeSignature("Core", ["Rational"], []);
        this.SpecialStringSignature = new NominalTypeSignature("Core", ["String"], []);
        
        this.SpecialAutoSignature = new AutoTypeSignature();
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
        const cscope = this.getCurrentFunctionScope();

        if (!cscope.isVarNameDefined(name) && cscope.isPCodeEnv()) {
            cscope.getCaptureVars().add(name);
        }
        
        return name;
    }

    useTemplateType(name: string): string {
        const cscope = this.getCurrentFunctionScope();

        if (!cscope.isTemplateNameDefined(name) && cscope.isPCodeEnv()) {
            cscope.getCaptureTemplates().add(name);
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
}

export { FunctionScope, ParserEnvironment };
