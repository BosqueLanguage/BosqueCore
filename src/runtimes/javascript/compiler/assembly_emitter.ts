import * as assert from "assert";
import * as path from "path";

import { TIRASCIIStringOfEntityType, TIRAssembly, TIRConceptType, TIRConstMemberDecl, TIREnumEntityType, TIRInfoTemplate, TIRInfoTemplateConst, TIRInfoTemplateMacro, TIRInfoTemplateRecord, TIRInfoTemplateTuple, TIRInfoTemplateValue, TIRInvoke, TIRInvokeAbstractDeclaration, TIRInvokeImplementation, TIRInvokeKey, TIRInvokePrimitive, TIRListEntityType, TIRMapEntityType, TIRMemberFieldDecl, TIRMemberMethodDecl, TIRNamespaceConstDecl, TIRNamespaceDeclaration, TIRNamespaceFunctionDecl, TIRNamespaceOperatorDecl, TIRObjectEntityType, TIROOType, TIRPathEntityType, TIRPathFragmentEntityType, TIRPathGlobEntityType, TIRPathValidatorEntityType, TIRPrimitiveInternalEntityType, TIRQueueEntityType, TIRSetEntityType, TIRStackEntityType, TIRStaticFunctionDecl, TIRStringOfEntityType, TIRTaskType, TIRType, TIRTypedeclEntityType, TIRTypeKey, TIRValidatorEntityType } from "../../../frontend/tree_ir/tir_assembly";
import { TIRCodePack, TIRLiteralValue } from "../../../frontend/tree_ir/tir_body";
import { BodyEmitter } from "./body_emitter";
import { emitBuiltinMemberFunction, emitBuiltinNamespaceFunction } from "./builtin_emitter";

class NamespaceEmitter {
    private readonly m_assembly: TIRAssembly;
    private readonly m_ns: string;
    private readonly m_decl: TIRNamespaceDeclaration;

    private m_coreImports: Set<TIRTypeKey> = new Set<TIRTypeKey>();

    constructor(assembly: TIRAssembly, ns: string, nsdecl: TIRNamespaceDeclaration) {
        this.m_assembly = assembly;
        this.m_ns = ns;
        this.m_decl = nsdecl;
    }

    private updateCoreImports(bemitter: BodyEmitter) {
        bemitter.m_coreImports.forEach((ii) => this.m_coreImports.add(ii));
    }

    private emitMemberConst(ootype: TIROOType, cdecl: TIRConstMemberDecl): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(cdecl.srcFile), this.m_ns); 

        const cstr = `$CF_${cdecl.name}: false, $CV_${cdecl.name}: undefined, ${cdecl.name}: function() { if(!$CF_${cdecl.name}) { $CF_${cdecl.name} = true; $CV_${cdecl.name} = ${bemitter.emitExpression(cdecl.value, true)}; } return $CV_${cdecl.name}; }`;

        this.updateCoreImports(bemitter);
        return cstr;
    }

    private emitMemberFunction(ootype: TIROOType, fdecl: TIRStaticFunctionDecl, indent: string): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(fdecl.srcFile), this.m_ns); 

        const args = fdecl.invoke.params.map((pp) => pp.name).join(", ");

        let body: string | undefined = "[NOT SET]";
        assert(!(fdecl.invoke instanceof TIRInvokeAbstractDeclaration), "should not be doing this!!");
            
        if(fdecl.invoke instanceof TIRInvokePrimitive) {
            body = emitBuiltinMemberFunction(ootype, fdecl, bemitter);
        }
        else {
            const fimpl = fdecl.invoke as TIRInvokeImplementation;
            body = bemitter.emitBodyStatementList(fimpl.body, fimpl.preconditions, fimpl.postconditions, indent, `${fdecl.tkey}::${fdecl.name}`, false);
        }

        if(body === undefined) {
            return "";
        }
        const cstr =  `function(${args}) ${body}`;
        
        this.updateCoreImports(bemitter);
        return cstr;
    }

    private emitMemberMethod(ootype: TIROOType, mdecl: TIRMemberMethodDecl, indent: string): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(mdecl.srcFile), this.m_ns); 

        const args = [(ootype instanceof TIRTaskType ? "self" : "$_this"), ...mdecl.invoke.params.map((pp) => pp.name)].join(", ");

        assert(!(mdecl.invoke instanceof TIRInvokeAbstractDeclaration) && !(mdecl.invoke instanceof TIRInvokePrimitive), "should not be doing this!!");
            
        const mimpl = mdecl.invoke as TIRInvokeImplementation;
        const body = bemitter.emitBodyStatementList(mimpl.body, mimpl.preconditions, mimpl.postconditions, indent, `${mdecl.tkey}::${mdecl.name}`, mdecl.attributes.includes("action") || mdecl.invoke.isThisRef);
        
        const cstr = `function(${args}) ${body}`;
        
        this.updateCoreImports(bemitter);
        return cstr;
    }

    private emitOOTypeFunctions(ootype: TIROOType): string[] {
        const finline = ootype.staticFunctions.filter((ff) => ff.invoke.tbinds.size === 0 && ff.invoke.pcodes.size === 0).map((ff) => ff.name + ": " + this.emitMemberFunction(ootype, ff, "    "));
        const fkey = ootype.staticFunctions.filter((ff) => ff.invoke.tbinds.size !== 0 || ff.invoke.pcodes.size !== 0).map((ff) => `"${ff.ikey}": ` + this.emitMemberFunction(ootype, ff, "        "));

        return [finline.join(",\n    "), `$Functions: {${fkey.join(",\n    ")}\n    }`];
    }

    private emitOOTypeMethods(ootype: TIROOType): string[] {
        const minline = ootype.memberMethods.filter((mm) => mm.invoke.tbinds.size === 0 && mm.invoke.pcodes.size === 0).map((mm) => mm.name + ": " + this.emitMemberMethod(ootype, mm, "    "));
        const mkey = ootype.memberMethods.filter((mm) => mm.invoke.tbinds.size !== 0 || mm.invoke.pcodes.size !== 0).map((mm) => `"${mm.ikey}": ` + this.emitMemberMethod(ootype, mm, "        "));

        return [minline.join(",\n    "), `$Methods: {${mkey.join(",\n    ")}\n    }`];
    }

    private emitTIREnumEntityType(ttype: TIREnumEntityType): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const entries = ttype.enums.map((ee) => `${ee}: ${bemitter.emitExpression((ttype.litvals.get(ee) as TIRLiteralValue).exp)}`);
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        this.updateCoreImports(bemitter);
        return `const BSQ${ttype.tname.name} = {${[...entries, ...funcs, ...methods].join(",\n    ")}\n};`;
    }

    private emitTIRTypedeclEntityType(ttype: TIRTypedeclEntityType): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        let consfuncs: string[] = [];
        if(ttype.consinvariantsall.length !== 0) {
            const checks = ttype.consinvariantsall.map((cc) => `$Runtime.raiseUserAssertIf(!${bemitter.emitExpression(cc.exp)}, "Failed invariant ${ttype.tkey} -- ${cc.exp.expstr}");`).join("\n    ") + "\n    ";
            consfuncs.push(`$constructorWithChecks_basetype: function($value) {${checks}return $value;\n    }`);
        }
        if(ttype.consinvariantsexplicit.length !== 0) {
            const checks = ttype.consinvariantsexplicit.map((cc) => `$Runtime.raiseUserAssertIf(!${bemitter.emitExpression(cc.exp)}, "Failed invariant ${ttype.tkey} -- ${cc.exp.expstr}");`).join("\n    ") + "\n    ";
            consfuncs.push(`$constructorWithChecks: function($value) {${checks}return $value;\n    }`);
        }

        this.updateCoreImports(bemitter);
        return `const BSQ${ttype.tname.name} = {${[...consts, ...funcs, ...methods, ...consfuncs].join(",\n    ")}\n};`;
    }

    private emitTIRObjectEntityType(ttype: TIRObjectEntityType): [boolean, string] {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        const fnames = ttype.allfields.map((ff) => (this.m_assembly.fieldMap.get(ff.fkey) as TIRMemberFieldDecl).name);

        let consfuncs: string[] = [];
        consfuncs.push(`$constructorDirect: function(${fnames.join(", ")} { return {${fnames.map((fn) => fn + ": " + fn).join(", ")}}; })`);

        if(ttype.consinvariants.length !== 0) {
            const checks = ttype.consinvariants.map((cc) => `$Runtime.raiseUserAssertIf(!${bemitter.emitExpression(cc.exp)}, "Failed invariant ${ttype.tkey} -- ${cc.exp.expstr}");`).join("\n    ") + "\n    ";
            consfuncs.push(`$constructorWithChecks_basetype: function(${fnames.map((fn) => "$" + fn).join(", ")}) {${checks}return {${fnames.map((fn) => fn + ": $" + fn).join(", ")}};\n    }`);
        }

        this.updateCoreImports(bemitter);
        if(ttype.binds.size === 0) {
            return [false, `const BSQ${ttype.tname.name} = {${[...consts, ...funcs, ...methods, ...consfuncs].join(",\n    ")}\n};`];
        }
        else {
            return [true, `"${ttype.tkey}": {${[...consts, ...funcs, ...methods, ...consfuncs].join(",\n    ")}\n}`];
        }
    }

    private emitTIRPrimitiveInternalEntityType(ttype: TIRPrimitiveInternalEntityType): string {
        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        return `const BSQ${ttype.tname.name} = {${[...consts, ...funcs, ...methods].join(",\n    ")}\n};`;
    }

    private emitTIRValidatorEntityType(ttype: TIRValidatorEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${[...funcs].join(",\n    ")}\n}`;
    }

    private emitTIRStringOfEntityType(ttype: TIRStringOfEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${[...funcs].join(",\n    ")}\n}`;
    }

    private emitTIRASCIIStringOfEntityType(ttype: TIRASCIIStringOfEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${[...funcs].join(",\n    ")}\n}`;
    }

    private emitTIRPathValidatorEntityType(ttype: TIRPathValidatorEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${[...funcs].join(",\n    ")}\n}`;
    }

    private emitTIRPathEntityType(ttype: TIRPathEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${[...funcs].join(",\n    ")}\n}`;
    }

    private emitTIRPathFragmentEntityType(ttype: TIRPathFragmentEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${[...funcs].join(",\n    ")}\n}`;
    }

    private emitTIRPathGlobEntityType(ttype: TIRPathGlobEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${[...funcs].join(",\n    ")}\n}`;
    }

    private emitTIRListEntityType(ttype: TIRListEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        return `"${ttype.tkey}": {${[...funcs, ...methods].join(",\n    ")}\n}`
    }

    private emitTIRStackEntityType(ttype: TIRStackEntityType): string {
        return "[NOT IMPLEMENTED -- STACK]";
    }

    private emitTIRQueueEntityType(ttype: TIRQueueEntityType): string {
        return "[NOT IMPLEMENTED -- QUEUE]";
    }

    private emitTIRSetEntityType(ttype: TIRSetEntityType): string {
        return "[NOT IMPLEMENTED -- SET]";
    }

    private emitTIRMapEntityType(ttype: TIRMapEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        return `"${ttype.tkey}": {${[...funcs, ...methods].join(",\n    ")}\n}`;
    }

    private emitTIRTaskType(ttype: TIRTaskType): string {
        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        const fnames = ttype.memberFields.map((ff) => (this.m_assembly.fieldMap.get(ff.fkey) as TIRMemberFieldDecl).name);

        let consfuncs: string[] = [];
        consfuncs.push(`$constructorDirect: function(${fnames.join(", ")} { return {${fnames.map((fn) => fn + ": " + fn).join(", ")}}; })`);

        assert(false, "need to setup task mainfunc stuff here");

        //
        //TODO: onX funcs such here too!
        //

        return `const BSQ${ttype.tname.name} = {${[...consts, ...funcs, ...methods, ...consfuncs].join(",\n    ")}\n};`;
    }

    private emitTIRConceptType(ttype: TIRConceptType): [boolean, string] {
        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        if(ttype.binds.size === 0) {
            return [false, `const BSQ${ttype.tname.name} = {${[...consts, ...funcs, ...methods].join(",\n    ")}\n};`];
        }
        else {
            return [true, `"${ttype.tkey}": {${[...consts, ...funcs, ...methods].join(",\n    ")}\n}`];
        }
    }

    private emitConst(nsconst: TIRNamespaceConstDecl): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(nsconst.srcFile), this.m_ns);
        const cdcl = `let $CF_${nsconst.name} = false; let $CV_${nsconst.name} = undefined; function ${nsconst.name}() { if(!$CF_${nsconst.name}) { $CF_${nsconst.name} = true; $CV_${nsconst.name} = ${bemitter.emitExpression(nsconst.value, true)}; } return $CV_${nsconst.name}; }`;

        this.updateCoreImports(bemitter);
        return cdcl;
    }

    private emitNamespaceFunction(fdecl: TIRNamespaceFunctionDecl, indent: string): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(fdecl.srcFile), this.m_ns); 

        const args = fdecl.invoke.params.map((pp) => pp.name).join(", ");

        let body: string | undefined = "[NOT SET]";
        assert(!(fdecl.invoke instanceof TIRInvokeAbstractDeclaration), "should not be doing this!!");
            
        if(fdecl.invoke instanceof TIRInvokePrimitive) {
            body = emitBuiltinNamespaceFunction(fdecl, bemitter);
        }
        else {
            const fimpl = fdecl.invoke as TIRInvokeImplementation;
            body = bemitter.emitBodyStatementList(fimpl.body, fimpl.preconditions, fimpl.postconditions, indent, `${fdecl.ns}::${fdecl.name}`, false);
        }

        if(body === undefined) {
            return "";
        }
        const cstr =  `function(${args}) ${body}`;
        
        this.updateCoreImports(bemitter);
        return cstr;
    }


    private emitFunctionInline(nsfunc: TIRNamespaceFunctionDecl): string {
        return "const " + nsfunc.name + " = " + this.emitNamespaceFunction(nsfunc, "");
    }

    private emitFunctionKey(nsfunc: TIRNamespaceFunctionDecl): string {
       return `"${nsfunc.ikey}": ` + this.emitNamespaceFunction(nsfunc, "    ");
    }

    private emitOperator(nsoperator: TIRNamespaceOperatorDecl): string {
        assert(false, "NOT IMPLEMENTED -- operator");
    }

    private emitCodePackFunction(pcode: TIRCodePack): string {
        const invk = this.m_assembly.invokeMap.get(pcode.invk) as TIRInvoke;
        assert(invk instanceof TIRInvokeImplementation, "should not be doing this!!");

        const bemitter = new BodyEmitter(this.m_assembly, path.basename(invk.srcFile), this.m_ns); 

        const args = invk.params.map((pp) => pp.name).join(", ");            
        const body = bemitter.emitBodyStatementList(invk.body, [], [], "        ", pcode.codekey, false);

        if(body === undefined) {
            return "";
        }
        const cstr =  `function(${args}) ${body}`;
        
        this.updateCoreImports(bemitter);

        return `"${pcode.invk}": ` + cstr;
    }

    private emitType(ttype: TIRType): [boolean, string] {
        if(ttype instanceof TIREnumEntityType) {
            return [false, this.emitTIREnumEntityType(ttype)];
        }
        else if(ttype instanceof TIRTypedeclEntityType) {
            return [false, this.emitTIRTypedeclEntityType(ttype)];
        }
        else if(ttype instanceof TIRObjectEntityType) {
            return this.emitTIRObjectEntityType(ttype);
        }
        else if(ttype instanceof TIRPrimitiveInternalEntityType) {
            return [false, this.emitTIRPrimitiveInternalEntityType(ttype)];
        }
        else if(ttype instanceof TIRValidatorEntityType) {
            return [true, this.emitTIRValidatorEntityType(ttype)];
        }
        else if(ttype instanceof TIRStringOfEntityType) {
            return [true, this.emitTIRStringOfEntityType(ttype)];
        } 
        else if(ttype instanceof TIRASCIIStringOfEntityType) {
            return [true, this.emitTIRASCIIStringOfEntityType(ttype)];
        }
        else if(ttype instanceof TIRPathValidatorEntityType) {
            return [true, this.emitTIRPathValidatorEntityType(ttype)];
        }
        else if(ttype instanceof TIRPathEntityType) {
            return [true, this.emitTIRPathEntityType(ttype)];
        }
        else if(ttype instanceof TIRPathFragmentEntityType) {
            return [true, this.emitTIRPathFragmentEntityType(ttype)];
        }
        else if(ttype instanceof TIRPathGlobEntityType) {
            return [true, this.emitTIRPathGlobEntityType(ttype)];
        }
        else if(ttype instanceof TIRListEntityType) {
            return [true, this.emitTIRListEntityType(ttype)];
        }
        else if(ttype instanceof TIRStackEntityType) {
            return [true, this.emitTIRStackEntityType(ttype)];
        }
        else if(ttype instanceof TIRQueueEntityType) {
            return [true, this.emitTIRQueueEntityType(ttype)];
        }
        else if(ttype instanceof TIRSetEntityType) {
            return [true, this.emitTIRSetEntityType(ttype)];
        }
        else if(ttype instanceof TIRMapEntityType) {
            return [true, this.emitTIRMapEntityType(ttype)];
        }
        else if(ttype instanceof TIRTaskType) {
            return [false, this.emitTIRTaskType(ttype)];
        }
        else if(ttype instanceof TIRConceptType) {
            return this.emitTIRConceptType(ttype);
        }
        else {
            return [false, ""];
        }
    }

    private emitInfoFmt(mfmt: TIRInfoTemplate): string {
        if(mfmt instanceof TIRInfoTemplateConst) {
            return mfmt.litexp.litstr;
        }
        else if (mfmt instanceof TIRInfoTemplateMacro) {
            return mfmt.macro;
        }
        else if (mfmt instanceof TIRInfoTemplateValue) {
            return `$${mfmt.argpos} as ${mfmt.argtype}`;
        }
        else if (mfmt instanceof TIRInfoTemplateRecord) {
            return "{" + mfmt.entries.map((ee) => `${ee.name}: ${this.emitInfoFmt(ee.value)}`).join(", ") + "}";
        }
        else {
            assert(mfmt instanceof TIRInfoTemplateTuple);

            return "[" + mfmt.entries.map((ee) => this.emitInfoFmt(ee)).join(", ") + "]";
        }
    }

    emitNamespace(nsdeps: string[]): string {
        let eexports: string[] = [];
        if(this.m_ns === "Core") {
            eexports.push("$CoreTypes", "$CoreFunctions");
        }
        else {
            eexports.push("$Types", "$Functions");
        }

        //TODO: right now we only check for exported functions

        let formats: string[] = [];
        this.m_decl.msgformats.forEach((mfd, nn) => {
            const mf = this.emitInfoFmt(mfd);
            formats.push(`const ${nn} = "${mf}";`);
        });

        this.m_decl.stringformats.forEach((sfd, nn) => {
            const sf = sfd.str;
            formats.push(`const ${nn} = "${sf}";`);
        });

        let itypes: string[] = [];
        let ktypes: string[] = [];
        this.m_decl.concepts.forEach((ttk) => {
            ttk.forEach((tk) => {
                const [isinline, ccs] = this.emitType(this.m_assembly.typeMap.get(tk) as TIRType);
                if(isinline) {
                    itypes.push(ccs);
                }
                else {
                    ktypes.push(ccs);
                }
            });
        });
    
        this.m_decl.objects.forEach((ttk) => {
            ttk.forEach((tk) => {
                const [isinline, ccs] = this.emitType(this.m_assembly.typeMap.get(tk) as TIRType);
                if(isinline) {
                    itypes.push(ccs);
                }
                else {
                    ktypes.push(ccs);
                }
            });
        });

        this.m_decl.tasks.forEach((ttk) => {
            const [isinline, ccs] = this.emitType(this.m_assembly.typeMap.get(ttk) as TIRType);
            if (isinline) {
                itypes.push(ccs);
            }
            else {
                ktypes.push(ccs);
            }
        });

        let consts: string[] = []; 
        this.m_decl.consts.forEach((cdecl) => {
            consts.push(this.emitConst(cdecl));
        });

        let ifuncs: string[] = [];
        let kfuncs: string[] = [];
        this.m_decl.functions.forEach((ffl) => {
            ffl.forEach((ff) => {
                if(ff.invoke.tbinds.size === 0 && ff.invoke.params.length === 0) {
                    const fstr = this.emitFunctionInline(ff);
                    ifuncs.push(fstr);

                    if(ff.attributes.includes("export")) {
                        eexports.push(ff.name);
                    }
                }
                else {
                    const fstr = this.emitFunctionKey(ff);
                    kfuncs.push(fstr);
                }
            });
        });

        this.m_decl.lambdas.forEach((lfd) => {
            const lf = this.emitCodePackFunction(this.m_decl.codepacks.get(lfd.pcid) as TIRCodePack);
            kfuncs.push(lf);
        });

        this.m_decl.operators.forEach((opdl) => {
            opdl.forEach((opd) => {
                const opf = this.emitOperator(opd);
                ifuncs.push(opf);
            });
        });

        const stdimps = `import * as $CoreLibs from "./corelibs.mjs"; import * as $Runtime from "./runtime.mjs";`
        const coreimps = this.m_ns !== "Core" ? `import {${[...this.m_coreImports].join(", ")}} from "./$Core";` : "";
        const depimps = nsdeps.filter((dep) => dep !== "Core").map((dep) => `import * as ${dep} from "./${dep}.mjs";`).join("\n");

        const fmts = formats.join("\n");

        const constdecls = consts.join("\n\n");

        const itypedecls = itypes.join("\n\n");
        const ktypedecls = `const $${this.m_ns === "Core" ? "Core" : ""}Types = {${ktypes.join("\n    ")}\n};\n`;

        const ifuncdecls = ifuncs.join("\n\n");
        const kfuncdecls = `const $${this.m_ns === "Core" ? "Core" : ""}Functions = {${ktypes.join("\n    ")}\n};\n`;

        const exportdecl = `export {\n    ${eexports.join(", ")}\n};`

        return ["\"use strict;\"", stdimps, coreimps, depimps, fmts, constdecls, itypedecls, ktypedecls, ifuncdecls, kfuncdecls, exportdecl].join("\n");
    }
}

class AssemblyEmitter {
    readonly assembly: TIRAssembly;
    readonly nsdeps: Map<string, string[]>;

    readonly namespacedecls: Map<string, string> = new Map<string, string>();
    readonly subtypeinfo: Map<TIRTypeKey, TIRTypeKey[]> = new Map<TIRTypeKey, TIRTypeKey[]>();
    readonly keyeqinfo: Map<TIRTypeKey, string> = new Map<TIRTypeKey, string>();
    readonly keylessinfo: Map<TIRTypeKey, string> = new Map<TIRTypeKey, string>();
    readonly vcallinfo: Map<TIRTypeKey, Map<string, TIRInvokeKey>> = new Map<TIRTypeKey, Map<string, TIRInvokeKey>>();

    private m_subtypeCache: Map<TIRTypeKey, Map<TIRTypeKey, boolean>> = new Map<TIRTypeKey, Map<TIRTypeKey, boolean>>();
    
    private isSubtype(t: TIRTypeKey, oftype: TIRTypeKey): boolean {
        if(!this.m_subtypeCache.has(oftype)) {
            this.m_subtypeCache.set(oftype, new Map<TIRTypeKey, boolean>());
        }
        let subt = this.m_subtypeCache.get(oftype) as Map<TIRTypeKey, boolean>;

        if(subt.has(t)) {
            return subt.get(t) as boolean;
        }

        let issub = false;
        const ttype = this.assembly.typeMap.get(t) as TIRType;
        if(ttype.supertypes !== undefined) {
            if(ttype.supertypes.has(oftype)) {
                issub = true;
            }
            else {
                issub = [...ttype.supertypes].some((ss) => this.isSubtype(ss, oftype));
            }
        }

        subt.set(t, issub);
        return issub;
    }

    constructor(assembly: TIRAssembly, nsdeps: Map<string, string[]>) {
        this.assembly = assembly;
        this.nsdeps = nsdeps;
    }

    private processAssembly() {
        this.assembly.namespaceMap.forEach((nsd, ns) => {
            const nsemit = new NamespaceEmitter(this.assembly, ns, nsd);
            const tirns = nsemit.emitNamespace(this.nsdeps.get(ns) as string[]);

            this.namespacedecls.set(ns, tirns);
        });

        //setup various maps
        let keyeqinfo = new Map<TIRTypeKey, string>();
        let keylessinfo = new Map<TIRTypeKey, string>();
        this.assembly.typeMap.forEach((tt) => {
            if(tt instanceof TIRConceptType) {
                const subt: TIRTypeKey[] = [];
                this.assembly.typeMap.forEach((tother) => {
                    if(this.isSubtype(tother.tkey, tt.tkey)) {
                        subt.push(tother.tkey);
                    }
                })
            }

            if(tt instanceof TIROOType && tt.iskeytype) {
                if(tt instanceof TIREnumEntityType) {
                    keyeqinfo.set(tt.tkey, "(a, b) => (a === b)");
                    keylessinfo.set(tt.tkey, "(a, b) => (a < b)");
                }
                else if(tt instanceof TIRTypedeclEntityType) {
                    keyeqinfo.set(tt.tkey, `(a, b) => $KeyEqualOps.get("${tt.representation}")(a, b)`);
                    keylessinfo.set(tt.tkey, `(a, b) => $KeyLessOps.get("${tt.representation}")(a, b)`);
                }
                else if((tt instanceof TIRStringOfEntityType) || (tt instanceof TIRASCIIStringOfEntityType)) {
                    keyeqinfo.set(tt.tkey, "(a, b) => (a === b)");
                    keylessinfo.set(tt.tkey, "(a, b) => (a < b)");
                }
                else if((tt instanceof TIRPathEntityType) || (tt instanceof TIRPathFragmentEntityType) || (tt instanceof TIRPathGlobEntityType)) {
                    keyeqinfo.set(tt.tkey, "(a, b) => (a === b)");
                    keylessinfo.set(tt.tkey, "(a, b) => (a < b)");
                }
                else {
                    assert(tt instanceof TIRPrimitiveInternalEntityType);
                    ; //should already be in the table 
                }
            }

            if(tt instanceof TIRObjectEntityType) {
                this.vcallinfo.set(tt.tkey, tt.vtable);
            }
        });
    };

    generateJSCode(corecode: string, runtimecode: string): {nsname: string, contents: string}[] {
        this.processAssembly();

        let outmodules: {nsname: string, contents: string}[] = [
            {   
                nsname: "corelibs.mjs",
                contents: corecode
                    .replace("//--GENERATED_$KeyEqualOps--", [...this.keyeqinfo].map((ke) => `$KeyEqualOps.set("${ke[0]}", ${ke[1]});`).join("\n"))
                    .replace("//--GENERATED_$KeyLessOps--", [...this.keyeqinfo].map((ke) => `$KeyLessOps.set("${ke[0]}", ${ke[1]});`).join("\n"))
            },
            {   
                nsname: "runtime.mjs",
                contents: runtimecode
                    .replace("//--GENERATED_$vtablesetup--", [...this.vcallinfo].map((vci) => `vtablemap.set("${vci[0]}", new Map(${[...vci[1]].map((vi) => "[\"" + vi[0] + "\", \"" + vi[1] + "\"]").join(", ")}));`).join("\n"))
            }
        ];

        this.namespacedecls.forEach((nsd, name) => {
            outmodules.push({nsname: `${name}.mjs`, contents: nsd});
        });

        return outmodules;
    }
}

export {
    AssemblyEmitter
};
