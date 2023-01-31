import * as path from "path";

import { TIRASCIIStringOfEntityType, TIRAssembly, TIRConceptSetType, TIRConceptType, TIRConstMemberDecl, TIREnumEntityType, TIRInfoTemplate, TIRInfoTemplateConst, TIRInfoTemplateMacro, TIRInfoTemplateRecord, TIRInfoTemplateTuple, TIRInfoTemplateValue, TIRInvoke, TIRInvokeAbstractDeclaration, TIRInvokeImplementation, TIRInvokeKey, TIRInvokePrimitive, TIRListEntityType, TIRMapEntityType, TIRMemberFieldDecl, TIRMemberMethodDecl, TIRNamespaceConstDecl, TIRNamespaceDeclaration, TIRNamespaceFunctionDecl, TIRNamespaceOperatorDecl, TIRObjectEntityType, TIROOType, TIRPathEntityType, TIRPathFragmentEntityType, TIRPathGlobEntityType, TIRPathValidatorEntityType, TIRPrimitiveInternalEntityType, TIRQueueEntityType, TIRRecordType, TIRSetEntityType, TIRStackEntityType, TIRStaticFunctionDecl, TIRStringOfEntityType, TIRTaskType, TIRTupleType, TIRType, TIRTypedeclEntityType, TIRTypeKey, TIRUnionType, TIRValidatorEntityType } from "../../../frontend/tree_ir/tir_assembly";
import { TIRCodePack, TIRLiteralValue } from "../../../frontend/tree_ir/tir_body";
import { BodyEmitter } from "./body_emitter";
import { emitBuiltinMemberFunction, emitBuiltinNamespaceFunction } from "./builtin_emitter";


function assert(cond: boolean, msg?: string) {
    if(!cond) {
        throw new Error((msg || "error")  + " -- assembly_emitter.ts");
    }
} 

class NamespaceEmitter {
    private readonly m_assembly: TIRAssembly;
    private readonly m_ns: string;
    private readonly m_decl: TIRNamespaceDeclaration;

    constructor(assembly: TIRAssembly, ns: string, nsdecl: TIRNamespaceDeclaration) {
        this.m_assembly = assembly;
        this.m_ns = ns;
        this.m_decl = nsdecl;
    }

    private emitMemberConst(ootype: TIROOType, cdecl: TIRConstMemberDecl): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(cdecl.srcFile), this.m_ns, false); 
        return `$CF_${cdecl.name}: false, $CV_${cdecl.name}: undefined, ${cdecl.name}: function() { if(!$CF_${cdecl.name}) { $CF_${cdecl.name} = true; $CV_${cdecl.name} = ${bemitter.emitExpression(cdecl.value, true)}; } return $CV_${cdecl.name}; }`;
    }

    private emitMemberFunction(ootype: TIROOType, fdecl: TIRStaticFunctionDecl, indent: string): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(fdecl.srcFile), this.m_ns, false); 

        const args = fdecl.invoke.params.map((pp) => pp.name).join(", ");

        let body: string | undefined = "[NOT SET]";
        assert(!(fdecl.invoke instanceof TIRInvokeAbstractDeclaration), "should not be doing this!!");
            
        if(fdecl.invoke instanceof TIRInvokePrimitive) {
            body = emitBuiltinMemberFunction(this.m_assembly, ootype, fdecl, bemitter);
        }
        else {
            const fimpl = fdecl.invoke as TIRInvokeImplementation;
            body = bemitter.emitBodyStatementList(fimpl.body, fimpl.preconditions, fimpl.postconditions, indent, `${fdecl.tkey}::${fdecl.name}`, false);
        }

        if(body === undefined) {
            return "";
        }
        return`function(${args}) ${body}`;
    }

    private emitMemberMethod(ootype: TIROOType, mdecl: TIRMemberMethodDecl, indent: string): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(mdecl.srcFile), this.m_ns, false); 

        const args = [(ootype instanceof TIRTaskType ? "self" : "$_this"), ...mdecl.invoke.params.map((pp) => pp.name)].join(", ");

        assert(!(mdecl.invoke instanceof TIRInvokeAbstractDeclaration) && !(mdecl.invoke instanceof TIRInvokePrimitive), "should not be doing this!!");
            
        const mimpl = mdecl.invoke as TIRInvokeImplementation;
        const body = bemitter.emitBodyStatementList(mimpl.body, mimpl.preconditions, mimpl.postconditions, indent, `${mdecl.tkey}::${mdecl.name}`, mdecl.attributes.includes("action") || mdecl.invoke.isThisRef);
        
        return `function(${args}) ${body}`;
    }

    private emitOOTypeFunctions(ootype: TIROOType): string[] {
        const finline = ootype.staticFunctions.filter((ff) => ff.invoke.tbinds.size === 0 && ff.invoke.pcodes.size === 0).map((ff) => ff.name + ": " + this.emitMemberFunction(ootype, ff, "    "));
        const fkey = ootype.staticFunctions.filter((ff) => ff.invoke.tbinds.size !== 0 || ff.invoke.pcodes.size !== 0).map((ff) => `"${ff.ikey}": ` + this.emitMemberFunction(ootype, ff, "        "));

        const finlinestr = finline.length !== 0 ? ("\n    " + finline.join(",\n    ")) : "";
        const fkeystr = fkey.length !== 0 ? (`$Functions: {\n        ${fkey.join(",\n        ")}\n    }`) : "";

        return [finlinestr, fkeystr];
    }

    private emitOOTypeMethods(ootype: TIROOType): string[] {
        const minline = ootype.memberMethods.filter((mm) => mm.invoke.tbinds.size === 0 && mm.invoke.pcodes.size === 0).map((mm) => mm.name + ": " + this.emitMemberMethod(ootype, mm, "    "));
        const mkey = ootype.memberMethods.filter((mm) => mm.invoke.tbinds.size !== 0 || mm.invoke.pcodes.size !== 0).map((mm) => `"${mm.ikey}": ` + this.emitMemberMethod(ootype, mm, "        "));

        const minlinestr = minline.length !== 0 ? ("\n    " + minline.join(",\n    ")) : "";
        const mkeystr = mkey.length !== 0 ? (`$Methods: {\n        ${mkey.join(",\n        ")}\n    }`) : "";

        return [minlinestr, mkeystr];
    }

    private static ooTypeOutputFlatten(outs: string[]): string {
        const oouts = outs.filter((oo) => oo !== "");
        return oouts.length !== 0 ? `\n    ${oouts.join(",\n    ")}\n` : " ";
    }

    private static ooTypeOutputFlattenKey(outs: string[]): string {
        const oouts = outs.filter((oo) => oo !== "");
        return oouts.length !== 0 ? `\n        ${oouts.join(",\n        ")}\n` : " ";
    }

    private emitTIREnumEntityType(ttype: TIREnumEntityType): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns, false);

        const entries = ttype.enums.map((ee) => `${ee}: ${bemitter.emitExpression((ttype.litvals.get(ee) as TIRLiteralValue).exp)}`);
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        return `const BSQ${ttype.tname.name} = {${NamespaceEmitter.ooTypeOutputFlatten([...entries, ...funcs, ...methods])}};`;
    }

    private emitTIRTypedeclEntityType(ttype: TIRTypedeclEntityType): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns, false);

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

        return `const BSQ${ttype.tname.name} = {${NamespaceEmitter.ooTypeOutputFlatten([...consts, ...funcs, ...methods, ...consfuncs])}};`;
    }

    private emitTIRObjectEntityType(ttype: TIRObjectEntityType): [boolean, string] {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns, false);

        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        const fnames = ttype.allfields.map((ff) => (this.m_assembly.fieldMap.get(ff.fkey) as TIRMemberFieldDecl).name);

        let consfuncs: string[] = [];
        consfuncs.push(`$constructorDirect: function(${fnames.join(", ")}) { return {${fnames.map((fn) => fn + ": " + fn).join(", ")}}; }`);

        if(ttype.consinvariants.length !== 0) {
            const checks = ttype.consinvariants.map((cc) => `$Runtime.raiseUserAssertIf(!${bemitter.emitExpression(cc.exp)}, "Failed invariant ${ttype.tkey} -- ${cc.exp.expstr}");`).join("\n    ") + "\n    ";
            consfuncs.push(`$constructorWithChecks_basetype: function(${fnames.map((fn) => "$" + fn).join(", ")}) {${checks}return {${fnames.map((fn) => fn + ": $" + fn).join(", ")}};\n    }`);
        }

        if(ttype.binds.size === 0) {
            return [false, `const BSQ${ttype.tname.name} = {${NamespaceEmitter.ooTypeOutputFlatten([...consts, ...funcs, ...methods, ...consfuncs])}};`];
        }
        else {
            return [true, `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlattenKey([...consts, ...funcs, ...methods, ...consfuncs])}}`];
        }
    }

    private emitTIRPrimitiveInternalEntityType(ttype: TIRPrimitiveInternalEntityType): string {
        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        return `const BSQ${ttype.tname.name} = {${NamespaceEmitter.ooTypeOutputFlatten([...consts, ...funcs, ...methods])}};`;
    }

    private emitTIRValidatorEntityType(ttype: TIRValidatorEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlattenKey([...funcs])}}`;
    }

    private emitTIRStringOfEntityType(ttype: TIRStringOfEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlattenKey([...funcs])}}`;
    }

    private emitTIRASCIIStringOfEntityType(ttype: TIRASCIIStringOfEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlattenKey([...funcs])}}`;
    }

    private emitTIRPathValidatorEntityType(ttype: TIRPathValidatorEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlattenKey([...funcs])}}`;
    }

    private emitTIRPathEntityType(ttype: TIRPathEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlattenKey([...funcs])}`;
    }

    private emitTIRPathFragmentEntityType(ttype: TIRPathFragmentEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlattenKey([...funcs])}}`;
    }

    private emitTIRPathGlobEntityType(ttype: TIRPathGlobEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlattenKey([...funcs])}}`;
    }

    private emitTIRListEntityType(ttype: TIRListEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlattenKey([...funcs, ...methods])}}`
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

        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlattenKey([...funcs, ...methods])}}`;
    }

    private emitTIRTaskType(ttype: TIRTaskType): string {
        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        const fnames = ttype.memberFields.map((ff) => (this.m_assembly.fieldMap.get(ff.fkey) as TIRMemberFieldDecl).name);

        let consfuncs: string[] = [];
        consfuncs.push(`$constructorDirect: function(${fnames.join(", ")}) { return {${fnames.map((fn) => fn + ": " + fn).join(", ")}}; }`);

        assert(false, "need to setup task mainfunc stuff here");

        //
        //TODO: onX funcs such here too!
        //

        return `const BSQ${ttype.tname.name} = {${NamespaceEmitter.ooTypeOutputFlatten([...consts, ...funcs, ...methods, ...consfuncs])}};`;
    }

    private emitTIRConceptType(ttype: TIRConceptType): [boolean, string] {
        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        if(ttype.binds.size === 0) {
            return [false, `const BSQ${ttype.tname.name} = {${NamespaceEmitter.ooTypeOutputFlatten([...consts, ...funcs, ...methods])}};`];
        }
        else {
            return [true, `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlattenKey([...consts, ...funcs, ...methods])}}`];
        }
    }

    private emitConst(nsconst: TIRNamespaceConstDecl): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(nsconst.srcFile), this.m_ns, false);
        return `let $CF_${nsconst.name} = false; let $CV_${nsconst.name} = undefined; function ${nsconst.name}() { if(!$CF_${nsconst.name}) { $CF_${nsconst.name} = true; $CV_${nsconst.name} = ${bemitter.emitExpression(nsconst.value, true)}; } return $CV_${nsconst.name}; }`;
    }

    private emitNamespaceFunction(fdecl: TIRNamespaceFunctionDecl, indent: string): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(fdecl.srcFile), this.m_ns, false); 

        const args = fdecl.invoke.params.map((pp) => pp.name).join(", ");

        let body: string | undefined = "[NOT SET]";
        assert(!(fdecl.invoke instanceof TIRInvokeAbstractDeclaration), "should not be doing this!!");
            
        if(fdecl.invoke instanceof TIRInvokePrimitive) {
            body = emitBuiltinNamespaceFunction(this.m_assembly, fdecl, bemitter);
        }
        else {
            const fimpl = fdecl.invoke as TIRInvokeImplementation;
            body = bemitter.emitBodyStatementList(fimpl.body, fimpl.preconditions, fimpl.postconditions, indent, `${fdecl.ns}::${fdecl.name}`, false);
        }

        if(body === undefined) {
            return "";
        }
        return `function(${args}) ${body}`;
    }

    private emitFunctionInline(nsfunc: TIRNamespaceFunctionDecl): string {
        return "const " + nsfunc.name + " = " + this.emitNamespaceFunction(nsfunc, "") + ";";
    }

    private emitFunctionKey(nsfunc: TIRNamespaceFunctionDecl): string {
       return `"${nsfunc.ikey}": ` + this.emitNamespaceFunction(nsfunc, "    ");
    }

    private emitOperator(nsoperator: TIRNamespaceOperatorDecl): string {
        assert(false, "NOT IMPLEMENTED -- operator");
        return "[NOT IMPLEMENTED]";
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

            return "[" + (mfmt as TIRInfoTemplateTuple).entries.map((ee) => this.emitInfoFmt(ee)).join(", ") + "]";
        }
    }

    emitNamespace(nsdeps: string[]): string {
        let eexports: string[] = [];

        let formats: string[] = [];
        this.m_decl.msgformats.forEach((mfd, nn) => {
            const mf = this.emitInfoFmt(mfd);
            formats.push(`const ${nn} = "${mf}";`);
            eexports.push(nn);
        });

        this.m_decl.stringformats.forEach((sfd, nn) => {
            const sf = sfd.str;
            formats.push(`const ${nn} = "${sf}";`);
            eexports.push(nn);
        });

        let itypes: string[] = [];
        let ktypes: string[] = [];
        this.m_decl.concepts.forEach((ttk) => {
            ttk.forEach((tk) => {
                const [iskeyed, ccs] = this.emitType(this.m_assembly.typeMap.get(tk) as TIRType);
                if(!iskeyed) {
                    itypes.push(ccs);
                    eexports.push("BSQ" + (this.m_assembly.typeMap.get(tk) as TIROOType).tname.name);
                }
                else {
                    ktypes.push(ccs);
                }
            });
        });
    
        this.m_decl.objects.forEach((ttk) => {
            ttk.forEach((tk) => {
                const [iskeyed, ccs] = this.emitType(this.m_assembly.typeMap.get(tk) as TIRType);
                if(!iskeyed) {
                    itypes.push(ccs);
                    eexports.push("BSQ" + (this.m_assembly.typeMap.get(tk) as TIROOType).tname.name);
                }
                else {
                    ktypes.push(ccs);
                }
            });
        });

        this.m_decl.tasks.forEach((ttk) => {
            const [iskeyed, ccs] = this.emitType(this.m_assembly.typeMap.get(ttk) as TIRType);
            if (!iskeyed) {
                itypes.push(ccs);
                eexports.push("BSQ" + (this.m_assembly.typeMap.get(ttk) as TIROOType).tname.name);
            }
            else {
                ktypes.push(ccs);
            }
        });

        let consts: string[] = []; 
        this.m_decl.consts.forEach((cdecl) => {
            consts.push(this.emitConst(cdecl));
            eexports.push(cdecl.name);
        });

        let ifuncs: string[] = [];
        let kfuncs: string[] = [];
        this.m_decl.functions.forEach((ffl) => {
            ffl.forEach((ff) => {
                if(ff.invoke.tbinds.size === 0 && ff.invoke.pcodes.size === 0) {
                    const fstr = this.emitFunctionInline(ff);
                    ifuncs.push(fstr);
                    eexports.push(ff.name);

                }
                else {
                    const fstr = this.emitFunctionKey(ff);
                    kfuncs.push(fstr);
                }
            });
        });

        this.m_decl.operators.forEach((opdl) => {
            opdl.forEach((opd) => {
                const opf = this.emitOperator(opd);
                ifuncs.push(opf);
            });
        });

        const stdimps = [`import * as $CoreLibs from "./corelibs.mjs";`, `import * as $Runtime from "./runtime.mjs";`];
        const depimps = nsdeps.map((dep) => `import * as ${dep} from "./${dep}.mjs";`).join("\n") + "\n";

        const fmts = formats.join("\n");

        const constdecls = consts.join("\n");

        const itypedecls = itypes.join("\n");
        const ktypedecls = ktypes.length !== 0 ? `const $Types = {\n    ${ktypes.join(",\n    ")}\n};\n` : "";

        if(ktypes.length !== 0) {
            eexports.push("$Types");
        }

        const ifuncdecls = ifuncs.join("\n\n");
        const kfuncdecls = kfuncs.length !== 0 ? `const $Functions = {\n    ${kfuncs.join(",\n    ")}\n};\n` : "";

        if(kfuncs.length !== 0) {
            eexports.push("$Functions");
        }

        const exportdecl = `export {\n    ${eexports.join(", ")}\n};`

        return ["\"use strict\";", ...stdimps, depimps, fmts, constdecls, itypedecls, ktypedecls, ifuncdecls, kfuncdecls, exportdecl]
            .filter((cmpt) => cmpt !== "")
            .join("\n");
    }
}

class AssemblyEmitter {
    readonly assembly: TIRAssembly;
    readonly nsdeps: Map<string, string[]>;

    readonly namespacedecls: Map<string, string> = new Map<string, string>();
    readonly subtypeinfo: Map<TIRTypeKey, TIRTypeKey[]> = new Map<TIRTypeKey, TIRTypeKey[]>();
    readonly vcallinfo: Map<TIRTypeKey, Map<string, TIRInvokeKey>> = new Map<TIRTypeKey, Map<string, TIRInvokeKey>>();
    readonly lambdas: Map<TIRInvokeKey, string> = new Map<TIRInvokeKey, string>();

    readonly keyeqinfo: Map<TIRTypeKey, string> = new Map<TIRTypeKey, string>();
    readonly keylessinfo: Map<TIRTypeKey, string> = new Map<TIRTypeKey, string>();

    readonly marshalinfo: Map<TIRTypeKey, {parse: string, emit: string}> = new Map<TIRTypeKey, {parse: string, emit: string}>();

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

    private emitTIREnumEntityType_ParseEmit(ttype: TIREnumEntityType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitTIRTypedeclEntityType_ParseEmit(ttype: TIRTypedeclEntityType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitTIRObjectEntityType_ParseEmit(ttype: TIRObjectEntityType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitTIRStringOfEntityType_ParseEmit(ttype: TIRStringOfEntityType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitTIRASCIIStringOfEntityType_ParseEmit(ttype: TIRASCIIStringOfEntityType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitTIRPathEntityType_ParseEmit(ttype: TIRPathEntityType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitTIRPathFragmentEntityType_ParseEmit(ttype: TIRPathFragmentEntityType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitTIRPathGlobEntityType_ParseEmit(ttype: TIRPathGlobEntityType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitTIRListEntityType_ParseEmit(ttype: TIRListEntityType): { parse: string, emit: string } {
        const parse = `{ if(!Array.isArray(jv)) {raiseRuntimeError("Failed in List<T> parse " + JSON.stringify(jv))} else { return IList(jv.map((vv) => ioMarshalMap.get("${ttype.typeT}").parse(vv))); } }`
        const emit = `nv.map((vv) => ioMarshalMap.get("${ttype.typeT}").emit(vv)).toArray()`;

        return {parse: parse, emit: emit};
    }

    private emitTIRStackEntityType_ParseEmit(ttype: TIRStackEntityType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitTIRQueueEntityType_ParseEmit(ttype: TIRQueueEntityType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitTIRSetEntityType_ParseEmit(ttype: TIRSetEntityType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitTIRMapEntityType_ParseEmit(ttype: TIRMapEntityType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitTIRConceptType_ParseEmit(ttype: TIRConceptType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitIRConceptSetType_ParseEmit(ttype: TIRConceptSetType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitTIRTupleType_ParseEmit(ttype: TIRTupleType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitTIRRecordType_ParseEmit(ttype: TIRRecordType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitTIRUnionType_ParseEmit(ttype: TIRUnionType): { parse: string, emit: string } {
        return { parse: "[NOT IMPLEMENTED]", emit: "[NOT IMPLEMENTED]" };
    }

    private emitTIRType_ParseEmit(ttype: TIRType): { parse: string, emit: string } | undefined {
        if (ttype instanceof TIREnumEntityType) {
            return this.emitTIREnumEntityType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRTypedeclEntityType) {
            return this.emitTIRTypedeclEntityType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRObjectEntityType) {
            return this.emitTIRObjectEntityType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRStringOfEntityType) {
            return this.emitTIRStringOfEntityType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRASCIIStringOfEntityType) {
            return this.emitTIRASCIIStringOfEntityType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRPathEntityType) {
            return this.emitTIRPathEntityType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRPathFragmentEntityType) {
            return this.emitTIRPathFragmentEntityType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRPathGlobEntityType) {
            return this.emitTIRPathGlobEntityType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRListEntityType) {
            return this.emitTIRListEntityType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRStackEntityType) {
            return this.emitTIRStackEntityType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRQueueEntityType) {
            return this.emitTIRQueueEntityType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRSetEntityType) {
            return this.emitTIRSetEntityType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRMapEntityType) {
            return this.emitTIRMapEntityType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRConceptType) {
            return this.emitTIRConceptType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRConceptSetType) {
            return this.emitIRConceptSetType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRTupleType) {
            return this.emitTIRTupleType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRRecordType) {
            return this.emitTIRRecordType_ParseEmit(ttype);
        }
        else if (ttype instanceof TIRUnionType) {
            return this.emitTIRUnionType_ParseEmit(ttype);
        }
        else {
            return undefined;
        }
    }

    private emitCodePackFunction(pcode: TIRCodePack): string {
        const invk = this.assembly.invokeMap.get(pcode.invk) as TIRInvoke;
        assert(invk instanceof TIRInvokeImplementation, "should not be doing this!!");

        const bemitter = new BodyEmitter(this.assembly, path.basename(invk.srcFile), "_LAMBDA_", true); 

        const args = invk.params.map((pp) => pp.name);            
        const body = bemitter.emitBodyStatementList((invk as TIRInvokeImplementation).body, [], [], "        ", pcode.codekey, false);

        if(body === undefined) {
            return "";
        }

        return `(${["$CodePack", ...args].join(", ")}) => ${body}`;
    }

    private processAssembly() {
        this.assembly.namespaceMap.forEach((nsd, ns) => {
            const nsemit = new NamespaceEmitter(this.assembly, ns, nsd);
            const tirns = nsemit.emitNamespace(this.nsdeps.get(ns) as string[]);

            nsd.lambdas.forEach((lfd) => {
                const lf = this.emitCodePackFunction(nsd.codepacks.get(lfd.pcid) as TIRCodePack);
                this.lambdas.set(lfd.ikey, lf);
            });

            this.namespacedecls.set(ns, tirns);
        });

        //setup various maps
        this.assembly.typeMap.forEach((tt) => {
            if(tt instanceof TIRConceptType) {
                const subt: TIRTypeKey[] = [];
                this.assembly.typeMap.forEach((tother) => {
                    if(this.isSubtype(tother.tkey, tt.tkey)) {
                        subt.push(tother.tkey);
                    }
                });

                this.subtypeinfo.set(tt.tkey, subt);
            }

            if(tt instanceof TIROOType && tt.iskeytype) {
                if(tt instanceof TIREnumEntityType) {
                    this.keyeqinfo.set(tt.tkey, "(a, b) => (a === b)");
                    this.keylessinfo.set(tt.tkey, "(a, b) => (a < b)");
                }
                else if(tt instanceof TIRTypedeclEntityType) {
                    this.keyeqinfo.set(tt.tkey, `(a, b) => $KeyEqualOps.get("${tt.representation}")(a, b)`);
                    this.keylessinfo.set(tt.tkey, `(a, b) => $KeyLessOps.get("${tt.representation}")(a, b)`);
                }
                else if((tt instanceof TIRStringOfEntityType) || (tt instanceof TIRASCIIStringOfEntityType)) {
                    this.keyeqinfo.set(tt.tkey, "(a, b) => (a === b)");
                    this.keylessinfo.set(tt.tkey, "(a, b) => (a < b)");
                }
                else if((tt instanceof TIRPathEntityType) || (tt instanceof TIRPathFragmentEntityType) || (tt instanceof TIRPathGlobEntityType)) {
                    this.keyeqinfo.set(tt.tkey, "(a, b) => (a === b)");
                    this.keylessinfo.set(tt.tkey, "(a, b) => (a < b)");
                }
                else {
                    assert(tt instanceof TIRPrimitiveInternalEntityType);
                    ; //should already be in the table 
                }
            }

            if(tt instanceof TIRObjectEntityType) {
                this.vcallinfo.set(tt.tkey, tt.vtable);
            }

            if(tt.isexportable && !(tt instanceof TIRPrimitiveInternalEntityType)) {
                const per = this.emitTIRType_ParseEmit(tt);
                if(per !== undefined) {
                    this.marshalinfo.set(tt.tkey, {parse: per.parse, emit: per.emit});
                } 
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
                    .replace("//--GENERATED_$subtypesetup--", [...this.subtypeinfo].map((sti) => `subtypeMap.set("${sti[0]}", new Set(${sti[1].map((st) => "\"" + st + "\"").join(", ")}));`).join("\n"))
                    .replace("//--GENERATED_$vtablesetup--", [...this.vcallinfo].map((vci) => `vtablemap.set("${vci[0]}", new Map(${[...vci[1]].map((vi) => "[\"" + vi[0] + "\", \"" + vi[1] + "\"]").join(", ")}));`).join("\n"))
                    .replace("//--GENERATED_$lambdas--", [...this.lambdas].map((li) => `lambdas.set("${li[0]}", ${li[1]})`).join("\n"))
                    .replace("//--GENERATED_$iomarshalsetup--", [...this.marshalinfo].map((mmi) => `ioMarshalMap.set("${mmi[0]}", {parse: (jv) => ${mmi[1].parse}, emit: (nv) => ${mmi[1].emit}});`).join("\n"))

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
