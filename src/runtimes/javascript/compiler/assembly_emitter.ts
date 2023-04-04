import * as path from "path";

import { TIRASCIIStringOfEntityType, TIRAssembly, TIRConceptSetType, TIRConceptType, TIRConstMemberDecl, TIREnumEntityType, TIRErrEntityType, TIRInfoTemplate, TIRInfoTemplateConst, TIRInfoTemplateMacro, TIRInfoTemplateRecord, TIRInfoTemplateTuple, TIRInfoTemplateValue, TIRInvoke, TIRInvokeAbstractDeclaration, TIRInvokeImplementation, TIRInvokeKey, TIRInvokePrimitive, TIRListEntityType, TIRMapEntityType, TIRMapEntryEntityType, TIRMemberFieldDecl, TIRMemberMethodDecl, TIRNamespaceConstDecl, TIRNamespaceDeclaration, TIRNamespaceFunctionDecl, TIRNamespaceOperatorDecl, TIRObjectEntityType, TIROkEntityType, TIROOType, TIRPathEntityType, TIRPathFragmentEntityType, TIRPathGlobEntityType, TIRPathValidatorEntityType, TIRPrimitiveInternalEntityType, TIRQueueEntityType, TIRRecordType, TIRSetEntityType, TIRSomethingEntityType, TIRStackEntityType, TIRStaticFunctionDecl, TIRStringOfEntityType, TIRTaskType, TIRTupleType, TIRType, TIRTypedeclEntityType, TIRTypeKey, TIRUnionType, TIRValidatorEntityType } from "../../../frontend/tree_ir/tir_assembly";
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
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(cdecl.srcFile), this.m_ns); 
        return `$CF_${cdecl.name}: false, $CV_${cdecl.name}: undefined, ${cdecl.name}: function() { if(!this.$CF_${cdecl.name}) { this.$CF_${cdecl.name} = true; this.$CV_${cdecl.name} = ${bemitter.emitExpression(cdecl.value, true)}; } return this.$CV_${cdecl.name}; }`;
    }

    private emitMemberFunction(ootype: TIROOType, fdecl: TIRStaticFunctionDecl, indent: string): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(fdecl.srcFile), this.m_ns); 

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
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(mdecl.srcFile), this.m_ns); 

        const args = [(ootype instanceof TIRTaskType ? "self" : "$_this"), ...mdecl.invoke.params.map((pp) => pp.name)].join(", ");

        assert(!(mdecl.invoke instanceof TIRInvokeAbstractDeclaration) && !(mdecl.invoke instanceof TIRInvokePrimitive), "should not be doing this!!");
            
        const mimpl = mdecl.invoke as TIRInvokeImplementation;
        const body = bemitter.emitBodyStatementList(mimpl.body, mimpl.preconditions, mimpl.postconditions, indent, `${mdecl.tkey}::${mdecl.name}`, mdecl.attributes.includes("action") || mdecl.invoke.isThisRef);
        
        return `function(${args}) ${body}`;
    }

    private emitOOTypeFunctions(ootype: TIROOType): string[] {
        const oofuncs = ootype.staticFunctions.filter((ff) => !ff.attributes.includes("abstract"));

        const finline = oofuncs.filter((ff) => ff.invoke.tbinds.size === 0 && ff.invoke.pcodes.size === 0).map((ff) => ff.name + ": " + this.emitMemberFunction(ootype, ff, "    "));
        const fkey = oofuncs.filter((ff) => ff.invoke.tbinds.size !== 0 || ff.invoke.pcodes.size !== 0).map((ff) => `"${ff.ikey}": ` + this.emitMemberFunction(ootype, ff, "        "));

        const finlinestr = finline.length !== 0 ? ("\n    " + finline.join(",\n    ")) : "";
        const fkeystr = fkey.length !== 0 ? (`$Functions: {\n        ${fkey.join(",\n        ")}\n    }`) : "";

        return [finlinestr, fkeystr];
    }

    private emitOOTypeMethods(ootype: TIROOType): string[] {
        const oomethods = ootype.memberMethods.filter((ff) => !ff.attributes.includes("abstract"));

        const minline = oomethods.filter((mm) => mm.invoke.tbinds.size === 0 && mm.invoke.pcodes.size === 0).map((mm) => mm.name + ": " + this.emitMemberMethod(ootype, mm, "    "));
        const mkey = oomethods.filter((mm) => mm.invoke.tbinds.size !== 0 || mm.invoke.pcodes.size !== 0).map((mm) => `"${mm.ikey}": ` + this.emitMemberMethod(ootype, mm, "        "));

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
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const entries = ttype.enums.map((ee) => `${ee}: ${bemitter.emitExpression((ttype.litvals.get(ee) as TIRLiteralValue).exp)}`);
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        return `const BSQ${ttype.tname.name} = {${NamespaceEmitter.ooTypeOutputFlatten([...entries, ...funcs, ...methods])}};`;
    }

    private emitTIRTypedeclEntityType(ttype: TIRTypedeclEntityType): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        let consfuncs: string[] = [];
        if(ttype.consinvariantsall.length !== 0) {
            const checks = ttype.consinvariantsall.map((cc) => `$Runtime.raiseUserAssertIf(!((() => { try { return ${bemitter.emitExpression(cc.exp)}; } catch (ex) { $Runtime.log("warn", "InvariantEvalFailure", "condition failure"); return true; } })()), "Failed invariant ${ttype.tkey}");`).join("\n        ") + "\n        ";
            consfuncs.push(`$constructorWithChecks_basetype: function($value) {\n        ${checks}return $value;\n    }`);
        }
        if(ttype.consinvariantsexplicit.length !== 0) {
            const checks = ttype.consinvariantsexplicit.map((cc) => `$Runtime.raiseUserAssertIf(!((() => { try { return ${bemitter.emitExpression(cc.exp)}; } catch (ex) { $Runtime.log("warn", "InvariantEvalFailure", "condition failure"); return true; } })()), "Failed invariant ${ttype.tkey}");`).join("\n        ") + "\n        ";
            consfuncs.push(`$constructorWithChecks: function($value) {\n        ${checks}return $value;\n    }`);
        }

        return `const BSQ${ttype.tname.name} = {${NamespaceEmitter.ooTypeOutputFlatten([...consts, ...funcs, ...methods, ...consfuncs])}};`;
    }

    private emitTIRObjectEntityType(ttype: TIRObjectEntityType): [boolean, string] {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        const fnames = ttype.allfields.map((ff) => (this.m_assembly.fieldMap.get(ff.fkey) as TIRMemberFieldDecl).name);

        let consfuncs: string[] = [];
        consfuncs.push(`$constructorDirect: function(${fnames.join(", ")}) { return Object.freeze({${fnames.map((fn) => fn + ": " + fn).join(", ")}}); }`);

        if(ttype.consinvariants.length !== 0) {
            const checks = ttype.consinvariants.map((cc) => `$Runtime.raiseUserAssertIf(!((() => { try { return ${bemitter.emitExpression(cc.exp)}; } catch (ex) { $Runtime.log("warn", "InvariantEvalFailure", "condition failure"); return true; } })()), "Failed invariant ${ttype.tkey}");`).join("\n        ") + "\n        ";
            consfuncs.push(`$constructorWithChecks: function(${fnames.map((fn) => "$" + fn).join(", ")}) {\n        ${checks}return Object.freeze({${fnames.map((fn) => fn + ": $" + fn).join(", ")}});\n    }`);
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

    private emitTIRMapEntryEntityType(ttype: TIRMapEntryEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlattenKey([...funcs, ...methods])}}`;
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
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(nsconst.srcFile), this.m_ns);
        return `let $CF_${nsconst.name} = false; let $CV_${nsconst.name} = undefined; function ${nsconst.name}() { if(!$CF_${nsconst.name}) { $CF_${nsconst.name} = true; $CV_${nsconst.name} = ${bemitter.emitExpression(nsconst.value, true)}; } return $CV_${nsconst.name}; }`;
    }

    private emitNamespaceFunction(fdecl: TIRNamespaceFunctionDecl, indent: string): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(fdecl.srcFile), this.m_ns); 

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
        else if(ttype instanceof TIRMapEntryEntityType) {
            return [true, this.emitTIRMapEntryEntityType(ttype)];
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
            return [true, ""];
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

    private emitCodePackFunction(pcode: TIRCodePack): string {
        const invk = this.m_assembly.invokeMap.get(pcode.invk) as TIRInvoke;
        assert(invk instanceof TIRInvokeImplementation, "should not be doing this!!");

        const bemitter = new BodyEmitter(this.m_assembly, path.basename(invk.srcFile), this.m_ns); 

        const args = invk.params.map((pp) => pp.name);            
        const body = bemitter.emitBodyStatementList((invk as TIRInvokeImplementation).body, [], [], "        ", pcode.codekey, false);

        if(body === undefined) {
            return "";
        }

        return `(${["$CodePack", ...args].join(", ")}) => ${body}`;
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

        let invdecls: string[] = [];

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
                    if(ccs !== "") {
                        ktypes.push(ccs);
                    }
                }

                const ootype = this.m_assembly.typeMap.get(tk) as TIROOType;
                ootype.memberMethods.forEach((mm) => {
                    if(mm.attributes.includes("virtual") || mm.attributes.includes("override")) {
                        const bemitter = new BodyEmitter(this.m_assembly, mm.srcFile, this.m_ns);
                        invdecls.push(`$Runtime.invmap.set("${mm.ikey}", {op: ${bemitter.resolveTypeMemberAccess(tk)}.${mm.name}, isatom: false});`);
                    }
                });
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
                    if(ccs !== "") {
                        ktypes.push(ccs);
                    }
                }

                const ootype = this.m_assembly.typeMap.get(tk) as TIROOType;
                ootype.memberMethods.forEach((mm) => {
                    if(mm.attributes.includes("override")) {
                        const bemitter = new BodyEmitter(this.m_assembly, mm.srcFile, this.m_ns);
                        invdecls.push(`$Runtime.invmap.set("${mm.ikey}", {op: ${bemitter.resolveTypeMemberAccess(tk)}.${mm.name}, isatom: true});`);
                    }
                });
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

        const lambdas = [...this.m_decl.lambdas].map((lfd) => {
            const lf = this.emitCodePackFunction(this.m_decl.codepacks.get(lfd[1].pcid) as TIRCodePack);
            return `$Runtime.lambdas.set("${lfd[0]}", ${lf});`;
        }).join("\n");
                    
        const iidm = invdecls.join("\n");

        const exportdecl = `export {\n    ${eexports.join(", ")}\n};`

        return ["\"use strict\";", ...stdimps, depimps, fmts, constdecls, itypedecls, ktypedecls, ifuncdecls, kfuncdecls, lambdas, iidm, exportdecl]
            .filter((cmpt) => cmpt !== "")
            .join("\n");
    }
}

class AssemblyEmitter {
    readonly assembly: TIRAssembly;
    readonly nsdeps: Map<string, string[]>;

    readonly namespacedecls: Map<string, string> = new Map<string, string>();
    readonly subtypeinfo: Map<TIRTypeKey, TIRTypeKey[]> = new Map<TIRTypeKey, TIRTypeKey[]>();
    readonly unionsubtypeinfo: Map<TIRTypeKey, {simpletypes: TIRTypeKey[], concepts: TIRTypeKey[]}> = new Map<TIRTypeKey, {simpletypes: TIRTypeKey[], concepts: TIRTypeKey[]}>();
    readonly vcallinfo: Map<TIRTypeKey, Map<string, TIRInvokeKey>> = new Map<TIRTypeKey, Map<string, TIRInvokeKey>>();
    
    readonly keyeqinfo: Map<TIRTypeKey, string> = new Map<TIRTypeKey, string>();
    readonly keylessinfo: Map<TIRTypeKey, string> = new Map<TIRTypeKey, string>();

    readonly marshalinfo: Map<TIRTypeKey, {parse: string, emit: string}> = new Map<TIRTypeKey, {parse: string, emit: string}>();

    private m_subtypeCache: Map<TIRTypeKey, Map<TIRTypeKey, boolean>> = new Map<TIRTypeKey, Map<TIRTypeKey, boolean>>();
    
    typeEncodedAsUnion(tt: TIRTypeKey): boolean {
        assert(this.assembly.typeMap.has(tt), `missing type name entry ${tt}`);

        const ttype = this.assembly.typeMap.get(tt) as TIRType;
        return (ttype instanceof TIRConceptType) || (ttype instanceof TIRUnionType);
    }

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
        const enumarr = "[" + ttype.enums.map((ee) => `"${ee}"`).join(", ") + "]";
        const parse = `{ if(typeof(jv) !== "string" || !jv.startsWith("${ttype.tkey + "::"}")) { $Runtime.raiseRuntimeError("Failed in enum parse " + JSON.stringify(jv)); } const ename = jv.substr("${ttype.tkey}".length + 2); const eidx = ${enumarr}.indexOf(ename); if(eidx === -1) { $Runtime.raiseRuntimeError("Failed in enum parse " + JSON.stringify(jv)); } return BigInt(eidx); }`;
        const emit = `"${ttype.tkey}::" + ${enumarr}[nv]`;

        return { parse: parse, emit: emit };
    }

    private emitTIRTypedeclEntityType_ParseEmit(ttype: TIRTypedeclEntityType): { parse: string, emit: string } {
        const rparse = `ioMarshalMap.get("${ttype.representation}").parse(jv)`;
        const remit = `ioMarshalMap.get("${ttype.representation}").emit(nv)`;

        if (ttype.apivalidates.length === 0) {
            return { parse: rparse, emit: remit };
        }
        else {
            const bemitter = new BodyEmitter(this.assembly, path.basename(ttype.srcFile), "[API TYPE PARSING]");
            const vcalls = ttype.apivalidates.map((vv) => bemitter.emitExpression(vv.exp));

            const parse = `{ const $value = ${rparse}; if(!(${vcalls.join(" && ")})) { $Runtime.raiseRuntimeError("Failed typedecl validation " + JSON.stringify(jv)); } return ${bemitter.resolveTypeMemberAccess(ttype.tkey)}.$constructorWithChecks_basetype($value); }`;

            return { parse: parse, emit: remit };
        }
    }

    private emitTIRObjectEntityType_ParseEmit(ttype: TIRObjectEntityType): { parse: string, emit: string } {
        const parseops = ttype.allfields.map((ff) => {
            const fdecl = this.assembly.fieldMap.get(ff.fkey) as TIRMemberFieldDecl;
            return `ioMarshalMap.get("${fdecl.declaredType}").parse(jv["${fdecl.name}"])`;
        });
        const props = ttype.allfields.map((ff) => {
            const fdecl = this.assembly.fieldMap.get(ff.fkey) as TIRMemberFieldDecl;
            return `"${fdecl.name}"`;
        });

        const unwrap = `if(Array.isArray(jv) && jv.length === 2 && jv[0] === "${ttype.tkey}") { jv = jv[1]; } `
        const rparse = `${unwrap} if(!checkIsObjectWithKeys(jv, [${props.join(", ")}])) { $Runtime.raiseRuntimeError("Failed in Object parse " + JSON.stringify(jv)); } `

        const emitops = ttype.allfields.map((ff) => {
            const fdecl = this.assembly.fieldMap.get(ff.fkey) as TIRMemberFieldDecl;
            return `${fdecl.name}: ioMarshalMap.get("${fdecl.declaredType}").emit(nv["${fdecl.name}"])`;
        });
        const remit = `{ return {${emitops.join(", ")}}; }`;

        const bemitter = new BodyEmitter(this.assembly, path.basename(ttype.srcFile), "[API TYPE PARSING]");
        if (ttype.apivalidates.length === 0) {
            const pcons = `${bemitter.resolveTypeMemberAccess(ttype.tkey)}.$constructorDirect(${parseops.join(", ")})`;
            return { parse: `{ ${rparse} else { return ${pcons}; } }`, emit: remit };
        }
        else {
            const vassigns = props.map((ff, ii) => `const $${ff} = ${parseops[ii]};`).join(" ");
            const vcalls = ttype.apivalidates.map((vv) => bemitter.emitExpression(vv.exp));
            const pcons = `${bemitter.resolveTypeMemberAccess(ttype.tkey)}.$constructorDirect(${props.map((ff) => `$${ff}`).join(", ")})`;

            const parse = `{ ${rparse} ${vassigns} if(!(${vcalls.join(" && ")})) { $Runtime.raiseRuntimeError("Failed typedecl validation " + JSON.stringify(jv)); } else { return ${pcons}; } }`;

            return { parse: parse, emit: remit };
        }
    }

    private emitTIRStringOfEntityType_ParseEmit(ttype: TIRStringOfEntityType): { parse: string, emit: string } {
        const jsre = ttype.revalidator.re.compileToJS()

        const parse = `{ if(typeof(jv) !== "string" || !$Runtime.acceptsString(/${jsre}/, jv)) { $Runtime.raiseRuntimeError("Failed StringOf validation " + JSON.stringify(jv)); } else { return ioMarshalMap.get("String").parse(jv); } }`;

        const emit = `ioMarshalMap.get("String").emit(nv)`;

        return { parse: parse, emit: emit };
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

    private emitTIROkEntityType_ParseEmit(ttype: TIROkEntityType): { parse: string, emit: string } {
        return { parse: `ioMarshalMap.get("${ttype.typeT}").parse(jv)`, emit: `ioMarshalMap.get("${ttype.typeT}").emit(nv)` };
    }

    private emitTIRErrEntityType_ParseEmit(ttype: TIRErrEntityType): { parse: string, emit: string } {
        return { parse: `ioMarshalMap.get("${ttype.typeE}").parse(jv)`, emit: `ioMarshalMap.get("${ttype.typeE}").emit(nv)` };
    }

    private emitTIRSomethingEntityType_ParseEmit(ttype: TIRSomethingEntityType): { parse: string, emit: string } {
        return { parse: `ioMarshalMap.get("${ttype.typeT}").parse(jv)`, emit: `ioMarshalMap.get("${ttype.typeT}").emit(nv)` };
    }

    private emitTIRMapEntryEntityType_ParseEmit(ttype: TIRMapEntryEntityType): { parse: string, emit: string } {
        const parse = `{ if(!Array.isArray(jv) || jv.length !== 2) { $Runtime.raiseRuntimeError("Failed in MapEntry<K, V> parse " + JSON.stringify(jv)); } else { return [ioMarshalMap.get("${ttype.typeK}").parse(jv[0]), ioMarshalMap.get("${ttype.typeV}").parse(jv[1])] } }`;
        const emit = `[ioMarshalMap.get("${ttype.typeK}").emit(nv[0]), ioMarshalMap.get("${ttype.typeV}").emit(nv[1])]`;

        return { parse: parse, emit: emit };
    }

    private emitTIRListEntityType_ParseEmit(ttype: TIRListEntityType): { parse: string, emit: string } {
        const parse = `{ if(!Array.isArray(jv)) { $Runtime.raiseRuntimeError("Failed in List<T> parse " + JSON.stringify(jv)); } else { return $CoreLibs.$ListOps.create(...jv.map((vv) => ioMarshalMap.get("${ttype.typeT}").parse(vv))); } }`
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
        const parse = `{ if(!Array.isArray(jv)) { $Runtime.raiseRuntimeError("Failed in Map<K, V> parse " + JSON.stringify(jv)); } else { return $CoreLibs.$MapOps.create("${ttype.typeK}", ...jv.map((vv) => { if(!Array.isArray(vv) || vv.length !== 2) { $Runtime.raiseRuntimeError("Failed in MapEntry<K, V> parse " + JSON.stringify(vv)); } else { return [ioMarshalMap.get("${ttype.typeK}").parse(vv[0]), ioMarshalMap.get("${ttype.typeV}").parse(vv[1])] } })); } }`
        
        const cmpcall = this.typeEncodedAsUnion(ttype.typeK) ? `$CoreLibs.$KeyLessGeneral` : `($CoreLibs.$KeyLessOps.get("${ttype.typeK}"))`;
        const emit = `nv.map((vv, kk) => [ioMarshalMap.get("${ttype.typeK}").emit(kk), ioMarshalMap.get("${ttype.typeV}").emit(vv)]).toArray().sort((a, b) => ${cmpcall}(a[0], b[0])).map((vv) => vv[1])`;

        return {parse: parse, emit: emit};
    }

    private emitTIRConceptType_ParseEmit(ttype: TIRConceptType): { parse: string, emit: string } {
        return { parse: "tryParseConcept(jv)", emit: "tryEmitConcept(nv)" };
    }

    private emitIRConceptSetType_ParseEmit(ttype: TIRConceptSetType): { parse: string, emit: string } {
        return { parse: "tryParseConcept(jv)", emit: "tryEmitConcept(nv)" };
    }

    private emitTIRTupleType_ParseEmit(ttype: TIRTupleType): { parse: string, emit: string } {
        const parseops = ttype.types.map((tt, ii) => `ioMarshalMap.get("${tt}").parse(jv[${ii}])`);
        const parse = `{ if(!Array.isArray(jv) || jv.length !== ${ttype.types.length}) { $Runtime.raiseRuntimeError("Failed in Tuple parse " + JSON.stringify(jv)); } else { return [ ${parseops.join(", ")} ]; } }`

        const emitops = ttype.types.map((tt, ii) => `ioMarshalMap.get("${tt}").emit(nv[${ii}])`);
        const emit = `[ ${emitops.join(", ")} ]`;

        return { parse: parse, emit: emit };
    }

    private emitTIRRecordType_ParseEmit(ttype: TIRRecordType): { parse: string, emit: string } {
        const parseops = ttype.entries.map((ee) => `${ee.pname}: ioMarshalMap.get("${ee.ptype}").parse(jv["${ee.pname}"])`);
        const props = ttype.entries.map((ee) => `"${ee.pname}"`).join(", ");
        const parse = `{ if(!checkIsObjectWithKeys(jv, [${props}])) { $Runtime.raiseRuntimeError("Failed in Record parse " + JSON.stringify(jv)); } else { return { ${parseops.join(", ")} }; } }`

        const emitops = ttype.entries.map((ee) => `${ee.pname}: ioMarshalMap.get("${ee.ptype}").emit(nv["${ee.pname}"])`);
        const emit = `{return { ${emitops.join(", ")} }; }`;

        return { parse: parse, emit: emit };
    }

    private emitTIRUnionType_ParseEmit(ttype: TIRUnionType): { parse: string, emit: string } {
        if(ttype.options.length === 2 && ttype.options.includes("None")) {
            const other = ttype.options.find((oo) => oo !== "None") as TIRTypeKey;

            const parse = `{ if(jv === null) { return $Runtime.UnionValue.create("None", null); } else { return $Runtime.UnionValue.create("${other}", ioMarshalMap.get("${other}").parse(jv)); } }`;
            const emit = `nv.tkey === "None" ? null : ioMarshalMap.get("${other}").emit(nv.value)`;

            return { parse: parse, emit: emit };
        }
        else {
            return { parse: "tryParseUnion(jv)", emit: "tryEmitUnion(nv)" };
        }
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
        else if(ttype instanceof TIROkEntityType) {
            return this.emitTIROkEntityType_ParseEmit(ttype);
        }
        else if(ttype instanceof TIRErrEntityType) {
            return this.emitTIRErrEntityType_ParseEmit(ttype);
        }
        else if(ttype instanceof TIRSomethingEntityType) {
            return this.emitTIRSomethingEntityType_ParseEmit(ttype);
        }
        else if(ttype instanceof TIRMapEntryEntityType) {
            return this.emitTIRMapEntryEntityType_ParseEmit(ttype);
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

    private processAssembly() {
        const allns = [...this.assembly.namespaceMap.keys()].sort();
        this.assembly.namespaceMap.forEach((nsd, ns) => {
            const nsemit = new NamespaceEmitter(this.assembly, ns, nsd);
            const tirns = nsemit.emitNamespace(allns); //(this.nsdeps.get(ns) as string[]);

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

            if(tt instanceof TIRUnionType) {
                const simpletypes: TIRTypeKey[] = [];
                const concepts: TIRTypeKey[] = [];
                tt.options.forEach((tother) => {
                    const ttodecl = this.assembly.typeMap.get(tother) as TIRType;
                    if(ttodecl instanceof TIRConceptType) {
                        concepts.push(tother);
                    }
                    else {
                        simpletypes.push(tother);
                    }
                });

                this.unionsubtypeinfo.set(tt.tkey, {simpletypes: simpletypes, concepts: concepts});
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

    generateJSCode(corecode: string, runtimecode: string, apicode: string): {nsname: string, contents: string}[] {
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
                    .replace("//--GENERATED_$subtypesetup--", [
                        ...[...this.subtypeinfo].map((sti) => `subtypeMap.set("${sti[0]}", {direct: new Set([${sti[1].map((st) => "\"" + st + "\"").join(", ")}]), indirect: [] });`),
                        ...[...this.unionsubtypeinfo].map((usi) => `subtypeMap.set("${usi[0]}", {direct: new Set([${usi[1].simpletypes.map((st) => "\"" + st + "\"").join(", ")}]), indirect: [${usi[1].concepts.map((st) => "\"" + st + "\"").join(", ")}] });`)
                        ].join("\n")
                    )
                    .replace("//--GENERATED_$vtablesetup--", [...this.vcallinfo].map((vci) => `vtablemap.set("${vci[0]}", new Map([${[...vci[1]].map((vi) => "[\"" + vi[0] + "\", \"" + vi[1] + "\"]").join(", ")}]));`).join("\n"))
            },
            {   
                nsname: "api.mjs",
                contents: apicode
                .replace("//--GENERATED_$usermodules--", [...this.namespacedecls].map((nsi) => `import * as ${nsi[0]} from "./${nsi[0]}.mjs";`).join("\n"))
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
