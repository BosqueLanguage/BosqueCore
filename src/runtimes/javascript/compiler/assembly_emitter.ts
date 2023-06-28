import * as path from "path";

import { TIRASCIIStringOfEntityType, TIRAssembly, TIRConceptType, TIRConstMemberDecl, TIREnumEntityType, TIRInfoTemplate, TIRInfoTemplateConst, TIRInfoTemplateMacro, TIRInfoTemplateRecord, TIRInfoTemplateTuple, TIRInfoTemplateValue, TIRInvoke, TIRInvokeAbstractDeclaration, TIRInvokeImplementation, TIRInvokePrimitive, TIRInvokeSynthesis, TIRListEntityType, TIRMapEntityType, TIRMapEntryEntityType, TIRMemberFieldDecl, TIRMemberMethodDecl, TIRNamespaceConstDecl, TIRNamespaceDeclaration, TIRNamespaceFunctionDecl, TIRNamespaceOperatorDecl, TIRObjectEntityType, TIROOType, TIRPathEntityType, TIRPathFragmentEntityType, TIRPathGlobEntityType, TIRPathValidatorEntityType, TIRPrimitiveInternalEntityType, TIRQueueEntityType, TIRSetEntityType, TIRStackEntityType, TIRStaticFunctionDecl, TIRStringOfEntityType, TIRTaskType, TIRType, TIRTypedeclEntityType, TIRTypeKey, TIRUnionType, TIRValidatorEntityType } from "../../../frontend/tree_ir/tir_assembly";
import { TIRCodePack } from "../../../frontend/tree_ir/tir_body";
import { BodyEmitter } from "./body_emitter";
import { emitBuiltinMemberFunction, emitBuiltinNamespaceFunction } from "./builtin_emitter";
import { resolveTypeMemberAccess } from "./type_emitter";

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

    private static s_indent_ns_member = "    ";
    private static s_indent_type_member = "        ";
    private static s_indent_type_member_body = "            ";

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
        else if(fdecl.invoke instanceof TIRInvokeSynthesis) {
            const ptypes = fdecl.invoke.params.map((pp) => `"${pp.type}"`);
            const rtype = `"${fdecl.invoke.resultType}"`;

            const samples = fdecl.invoke.samplesinline.map((ss) => `{args: ${ss.args}, result: ${ss.output}}`);
            body = `{\n    return processProroguedCall("${fdecl.srcFile}", ${fdecl.sourceLocation.line}, "${fdecl.name}", [${ptypes.join(", ")}], ${rtype}, ${ootype.tname.ns}, [${samples.join(", ")}], [${args}]);\n}`;
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
            
        if(mdecl.invoke instanceof TIRInvokeSynthesis) {
            const ptypes = [ootype.tkey, ...mdecl.invoke.params.map((pp) => `"${pp.type}"`)];
            const rtype = `"${mdecl.invoke.resultType}"`;

            const samples = mdecl.invoke.samplesinline.map((ss) => `{args: ${ss.args}, result: ${ss.output}}`);
            const body = `return processProroguedCall(${mdecl.srcFile}, ${mdecl.sourceLocation.line}, ${mdecl.name}, [${ptypes.join(", ")}], ${rtype}, ${ootype.tname.ns}, [${samples.join(", ")}], [${args}]);`;

            return `function(${args}) ${body}`;
        }
        else {
            const mimpl = mdecl.invoke as TIRInvokeImplementation;
            const body = bemitter.emitBodyStatementList(mimpl.body, mimpl.preconditions, mimpl.postconditions, indent, `${mdecl.tkey}::${mdecl.name}`, mdecl.attributes.includes("action") || mdecl.invoke.isThisRef);

            return `function(${args}) ${body}`;
        }
    }

    private emitOOTypeFunctions(ootype: TIROOType): string[] {
        const oofuncs = ootype.staticFunctions.filter((ff) => !ff.attributes.includes("abstract"));

        const finline = oofuncs.filter((ff) => ff.invoke.tbinds.size === 0 && ff.invoke.pcodes.size === 0).map((ff) => ff.name + ": " + this.emitMemberFunction(ootype, ff, NamespaceEmitter.s_indent_type_member));
        const fkey = oofuncs.filter((ff) => ff.invoke.tbinds.size !== 0 || ff.invoke.pcodes.size !== 0).map((ff) => `"${ff.ikey}": ` + this.emitMemberFunction(ootype, ff, NamespaceEmitter.s_indent_type_member));

        const finlinestr = finline.length !== 0 ? finline.join(",\n" + NamespaceEmitter.s_indent_type_member) : "";
        const fkeystr = fkey.length !== 0 ? fkey.join(",\n" + NamespaceEmitter.s_indent_type_member) : "";

        return [finlinestr, fkeystr];
    }

    private emitOOTypeMethods(ootype: TIROOType): string[] {
        const oomethods = ootype.memberMethods.filter((ff) => !ff.attributes.includes("abstract"));

        const minline = oomethods.filter((mm) => mm.invoke.tbinds.size === 0 && mm.invoke.pcodes.size === 0).map((mm) => mm.name + ": " + this.emitMemberMethod(ootype, mm, NamespaceEmitter.s_indent_type_member));
        const mkey = oomethods.filter((mm) => mm.invoke.tbinds.size !== 0 || mm.invoke.pcodes.size !== 0).map((mm) => `"${mm.ikey}": ` + this.emitMemberMethod(ootype, mm, NamespaceEmitter.s_indent_type_member));

        const minlinestr = minline.length !== 0 ? minline.join(",\n" + NamespaceEmitter.s_indent_type_member) : "";
        const mkeystr = mkey.length !== 0 ? mkey.join(",\n" + NamespaceEmitter.s_indent_type_member) : "";


        return [minlinestr, mkeystr];
    }

    private static ooTypeOutputFlatten(outs: string[]): string {
        const oouts = outs.filter((oo) => oo !== "");
        return oouts.length !== 0 ? `\n${NamespaceEmitter.s_indent_type_member}${oouts.join(",\n" + NamespaceEmitter.s_indent_type_member)}\n${NamespaceEmitter.s_indent_ns_member}` : "";
    }

    private emitTIREnumEntityType(ttype: TIREnumEntityType): string {
        const entries = ttype.enums.map((ee) => `${ee}: "${ttype.tkey}::${ee}"`);
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        return `${ttype.tname.name}: {${NamespaceEmitter.ooTypeOutputFlatten([...entries, ...funcs, ...methods])}}`;
    }

    private emitTIRTypedeclEntityType(ttype: TIRTypedeclEntityType): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        let consfuncs: string[] = [];
        if(ttype.consinvariantsall.length !== 0) {
            const checks = ttype.consinvariantsall.map((cc) => `$Runtime.raiseUserAssertIf(!((() => { try { return ${bemitter.emitExpression(cc.exp)}; } catch (ex) { $Runtime.log("warn", "InvariantEvalFailure", "condition failure"); return true; } })()), "Failed invariant ${ttype.tkey}");`).join("\n" + NamespaceEmitter.s_indent_type_member_body) + "\n" + NamespaceEmitter.s_indent_type_member_body;
            consfuncs.push(`$constructorWithChecks_basetype: function($value) {\n${NamespaceEmitter.s_indent_type_member_body}${checks}return $value;\n${NamespaceEmitter.s_indent_type_member}}`);
        }
        if(ttype.consinvariantsexplicit.length !== 0) {
            const checks = ttype.consinvariantsexplicit.map((cc) => `$Runtime.raiseUserAssertIf(!((() => { try { return ${bemitter.emitExpression(cc.exp)}; } catch (ex) { $Runtime.log("warn", "InvariantEvalFailure", "condition failure"); return true; } })()), "Failed invariant ${ttype.tkey}");`).join("\n" + NamespaceEmitter.s_indent_type_member_body) + "\n" + NamespaceEmitter.s_indent_type_member_body;
            consfuncs.push(`$constructorWithChecks: function($value) {\n${NamespaceEmitter.s_indent_type_member_body}${checks}return $value;\n${NamespaceEmitter.s_indent_type_member}}`);
        }

        let validatefunc: string[] = [];
        if(ttype.apivalidates.length !== 0 || ttype.consinvariantsall.length !== 0) {
            const invchecks = ttype.consinvariantsall.map((cc) => `$Runtime.raiseUserAssertIf(!((() => { try { return ${bemitter.emitExpression(cc.exp)}; } catch (ex) { $Runtime.log("warn", "InvariantEvalFailure", "condition failure"); return true; } })()), "Failed invariant ${ttype.tkey}");`);
            const validatechecks = ttype.apivalidates.map((cc) => `$Runtime.raiseUserAssertIf(!((() => { try { return ${bemitter.emitExpression(cc.exp)}; } catch (ex) { $Runtime.log("warn", "ValidateEvalFailure", "condition failure"); return true; } })()), "Failed validate ${ttype.tkey}");`);

            const vvfstr = [...invchecks, ...validatechecks].join("\n" + NamespaceEmitter.s_indent_type_member_body) + "\n" + NamespaceEmitter.s_indent_type_member_body;
            validatefunc.push(`$validate: function($value) {\n${NamespaceEmitter.s_indent_type_member_body}${vvfstr}}`);
        }

        return `${ttype.tname.name}: {${NamespaceEmitter.ooTypeOutputFlatten([...consts, ...funcs, ...methods, ...consfuncs, ...validatefunc])}}`;
    }

    private emitTIRObjectEntityType(ttype: TIRObjectEntityType): string {
        const bemitter = new BodyEmitter(this.m_assembly, path.basename(ttype.srcFile), this.m_ns);

        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        const fnames = ttype.allfields.map((ff) => (this.m_assembly.fieldMap.get(ff.fkey) as TIRMemberFieldDecl).name);

        let consfuncs: string[] = [];
        consfuncs.push(`$constructorDirect: function(${fnames.join(", ")}) { return Object.freeze({${fnames.map((fn) => fn + ": " + fn).join(", ")}}); }`);

        if(ttype.consinvariants.length !== 0) {
            const checks = ttype.consinvariants.map((cc) => `$Runtime.raiseUserAssertIf(!((() => { try { return ${bemitter.emitExpression(cc.exp)}; } catch (ex) { $Runtime.log("warn", "InvariantEvalFailure", "condition failure"); return true; } })()), "Failed invariant ${ttype.tkey}");`).join("\n" + NamespaceEmitter.s_indent_type_member_body) + "\n" + NamespaceEmitter.s_indent_type_member_body;
            consfuncs.push(`$constructorWithChecks: function(${fnames.map((fn) => "$" + fn).join(", ")}) {\n${NamespaceEmitter.s_indent_type_member_body}${checks}return Object.freeze({${fnames.map((fn) => fn + ": $" + fn).join(", ")}});\n${NamespaceEmitter.s_indent_type_member}}`);
        }

        let validatefunc: string[] = [];
        if(ttype.apivalidates.length !== 0 || ttype.consinvariants.length !== 0) {
            const invchecks = ttype.consinvariants.map((cc) => `$Runtime.raiseUserAssertIf(!((() => { try { return ${bemitter.emitExpression(cc.exp)}; } catch (ex) { $Runtime.log("warn", "InvariantEvalFailure", "condition failure"); return true; } })()), "Failed invariant ${ttype.tkey}");`);
            const validatechecks = ttype.apivalidates.map((cc) => `$Runtime.raiseUserAssertIf(!((() => { try { return ${bemitter.emitExpression(cc.exp)}; } catch (ex) { $Runtime.log("warn", "ValidateEvalFailure", "condition failure"); return true; } })()), "Failed validate ${ttype.tkey}");`);

            const vvfstr = [...invchecks, ...validatechecks].join("\n" + NamespaceEmitter.s_indent_type_member_body) + "\n" + NamespaceEmitter.s_indent_type_member;
            validatefunc.push(`$validate: function($$value) {\n${NamespaceEmitter.s_indent_type_member_body}${fnames.map((fn) => "const $" + fn + " = $$value." + fn + "; ").join(" ")}\n${NamespaceEmitter.s_indent_type_member_body}${vvfstr}}`);
        }

        if(ttype.binds.size === 0) {
            return `${ttype.tname.name}: {${NamespaceEmitter.ooTypeOutputFlatten([...consts, ...funcs, ...methods, ...consfuncs, ...validatefunc])}}`;
        }
        else {
            return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlatten([...consts, ...funcs, ...methods, ...consfuncs, ...validatefunc])}}`;
        }
    }

    private emitTIRPrimitiveInternalEntityType(ttype: TIRPrimitiveInternalEntityType): string {
        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        return `${ttype.tname.name}: {${NamespaceEmitter.ooTypeOutputFlatten([...consts, ...funcs, ...methods])}}`;
    }

    private emitTIRValidatorEntityType(ttype: TIRValidatorEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `${ttype.tname.name}: {${NamespaceEmitter.ooTypeOutputFlatten([...funcs])}}`;
    }

    private emitTIRStringOfEntityType(ttype: TIRStringOfEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlatten([...funcs])}}`;
    }

    private emitTIRASCIIStringOfEntityType(ttype: TIRASCIIStringOfEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlatten([...funcs])}}`;
    }

    private emitTIRPathValidatorEntityType(ttype: TIRPathValidatorEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `${ttype.tname.name}: {${NamespaceEmitter.ooTypeOutputFlatten([...funcs])}}`;
    }

    private emitTIRPathEntityType(ttype: TIRPathEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlatten([...funcs])}`;
    }

    private emitTIRPathFragmentEntityType(ttype: TIRPathFragmentEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlatten([...funcs])}}`;
    }

    private emitTIRPathGlobEntityType(ttype: TIRPathGlobEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype)
        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlatten([...funcs])}}`;
    }

    private emitTIRListEntityType(ttype: TIRListEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlatten([...funcs, ...methods])}}`
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

        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlatten([...funcs, ...methods])}}`;
    }

    private emitTIRMapEntityType(ttype: TIRMapEntityType): string {
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlatten([...funcs, ...methods])}}`;
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

        return `${ttype.tname.name} = {${NamespaceEmitter.ooTypeOutputFlatten([...consts, ...funcs, ...methods, ...consfuncs])}}`;
    }

    private emitTIRConceptType(ttype: TIRConceptType): string {
        const consts = ttype.constMembers.map((cm) => this.emitMemberConst(ttype, cm));
        const funcs = this.emitOOTypeFunctions(ttype);
        const methods = this.emitOOTypeMethods(ttype);

        if(ttype.binds.size === 0) {
            return `${ttype.tname.name}: {${NamespaceEmitter.ooTypeOutputFlatten([...consts, ...funcs, ...methods])}}`;
        }
        else {
            return `"${ttype.tkey}": {${NamespaceEmitter.ooTypeOutputFlatten([...consts, ...funcs, ...methods])}}`;
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
        else if(fdecl.invoke instanceof TIRInvokeSynthesis) {
            const lfs = Math.max(fdecl.srcFile.lastIndexOf("/"), fdecl.srcFile.lastIndexOf("\\"));
            const srcf = lfs !== -1 ? fdecl.srcFile.substring(lfs + 1) : fdecl.srcFile;

            const ptypes = fdecl.invoke.params.map((pp) => `"${pp.type}"`);
            const rtype = `"${fdecl.invoke.resultType}"`;

            const samples = fdecl.invoke.samplesinline.map((ss) => `{args: '${ss.args}', result: '${ss.output}'}`);
            body = `{\n    return $Prorogue.processProroguedCall("${srcf}", ${fdecl.sourceLocation.line}, "${fdecl.name}", [${ptypes.join(", ")}], ${rtype}, "${fdecl.ns}", [${samples.join(", ")}], [${args}]);\n}`;
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

    private emitType(ttype: TIRType): string {
        if(ttype instanceof TIREnumEntityType) {
            return this.emitTIREnumEntityType(ttype);
        }
        else if(ttype instanceof TIRTypedeclEntityType) {
            return this.emitTIRTypedeclEntityType(ttype);
        }
        else if(ttype instanceof TIRObjectEntityType) {
            return this.emitTIRObjectEntityType(ttype);
        }
        else if(ttype instanceof TIRPrimitiveInternalEntityType) {
            return this.emitTIRPrimitiveInternalEntityType(ttype);
        }
        else if(ttype instanceof TIRValidatorEntityType) {
            return this.emitTIRValidatorEntityType(ttype);
        }
        else if(ttype instanceof TIRStringOfEntityType) {
            return this.emitTIRStringOfEntityType(ttype);
        } 
        else if(ttype instanceof TIRASCIIStringOfEntityType) {
            return this.emitTIRASCIIStringOfEntityType(ttype);
        }
        else if(ttype instanceof TIRPathValidatorEntityType) {
            return this.emitTIRPathValidatorEntityType(ttype);
        }
        else if(ttype instanceof TIRPathEntityType) {
            return this.emitTIRPathEntityType(ttype);
        }
        else if(ttype instanceof TIRPathFragmentEntityType) {
            return this.emitTIRPathFragmentEntityType(ttype);
        }
        else if(ttype instanceof TIRPathGlobEntityType) {
            return this.emitTIRPathGlobEntityType(ttype);
        }
        else if(ttype instanceof TIRListEntityType) {
            return this.emitTIRListEntityType(ttype);
        }
        else if(ttype instanceof TIRStackEntityType) {
            return this.emitTIRStackEntityType(ttype);
        }
        else if(ttype instanceof TIRQueueEntityType) {
            return this.emitTIRQueueEntityType(ttype);
        }
        else if(ttype instanceof TIRSetEntityType) {
            return this.emitTIRSetEntityType(ttype);
        }
        else if(ttype instanceof TIRMapEntryEntityType) {
            return this.emitTIRMapEntryEntityType(ttype);
        }
        else if(ttype instanceof TIRMapEntityType) {
            return this.emitTIRMapEntityType(ttype);
        }
        else if(ttype instanceof TIRTaskType) {
            return this.emitTIRTaskType(ttype);
        }
        else if(ttype instanceof TIRConceptType) {
            return this.emitTIRConceptType(ttype);
        }
        else {
            return "";
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

    emitNamespace(nsdeps: string[], asdeno: boolean): string {
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
        let chkdecls: string[] = [];

        let dtypes: string[] = [];
        this.m_decl.concepts.forEach((ttk) => {
            ttk.forEach((tk) => {
                const ccs = this.emitType(this.m_assembly.typeMap.get(tk) as TIRType);
                if(ccs !== "") {
                    dtypes.push(ccs);
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
                const ccs = this.emitType(this.m_assembly.typeMap.get(tk) as TIRType);
                if (ccs !== "") {
                    dtypes.push(ccs);
                }

                const ootype = this.m_assembly.typeMap.get(tk) as TIROOType;
                ootype.memberMethods.forEach((mm) => {
                    if(mm.attributes.includes("override")) {
                        const bemitter = new BodyEmitter(this.m_assembly, mm.srcFile, this.m_ns);
                        invdecls.push(`$Runtime.invmap.set("${mm.ikey}", {op: ${bemitter.resolveTypeMemberAccess(tk)}.${mm.name}, isatom: true});`);
                    }
                });

                if(ootype instanceof TIRObjectEntityType && ootype.vtable.size > 0) {
                    invdecls.push(`$Runtime.vtablemap.set("${ootype.tkey}", new Map([${[...ootype.vtable].map((vi) => "[\"" + vi[0] + "\", \"" + vi[1] + "\"]").join(", ")}]));`);
                }

                if(ootype instanceof TIRObjectEntityType && (ootype.consinvariants.length !== 0 || ootype.apivalidates.length !== 0)) {
                    chkdecls.push(`$Runtime.validators.set("${ootype.tkey}", ${resolveTypeMemberAccess(this.m_assembly, ootype.tkey)}.$validate);`);
                }
                if(ootype instanceof TIRTypedeclEntityType && (ootype.consinvariantsall.length !== 0 || ootype.apivalidates.length !== 0)) {
                    chkdecls.push(`$Runtime.validators.set("${ootype.tkey}", ${resolveTypeMemberAccess(this.m_assembly, ootype.tkey)}.$validate);`);
                }
            });
        });

        this.m_decl.tasks.forEach((ttk) => {
            const ccs = this.emitType(this.m_assembly.typeMap.get(ttk) as TIRType);
            dtypes.push(ccs);
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

        const iext = asdeno ? ".ts" : "";
        const stdimps = [`import * as $Constants from "./constants${iext}";`, `import * as $TypeInfo from "./typeinfo${iext}";`, `import * as $Runtime from "./runtime${iext}";`, `import {$ASM} from "./runtime${iext}";`, `import * as $BSQONEmit from "./bsqon_emit${iext}";`, `import * as $Prorogue from "./prorogue${iext}";`];
        if(this.m_ns !== "Core") {
            stdimps.push(`import { $BSQ } from "./Core${iext}";`);
        }
        const depimps = nsdeps.map((dep) => `import * as ${dep} from "./${dep}${iext}";`).join("\n") + "\n";

        const fmts = formats.join("\n");

        const constdecls = consts.join("\n");

        let nstdecl = "";
        if(this.m_ns === "Core") {
            nstdecl = `const $BSQ = {\n${NamespaceEmitter.s_indent_ns_member}${dtypes.join(",\n" + NamespaceEmitter.s_indent_ns_member)}\n};`
        }
        else {
            if(dtypes.length === 0) {
                nstdecl = `$Runtime.$ASM.${this.m_ns.replace(/::/g, "$")} = {};`;
            }
            else {
                nstdecl = `$Runtime.$ASM.${this.m_ns.replace(/::/g, "$")} = {\n${NamespaceEmitter.s_indent_ns_member}${dtypes.join(",\n" + NamespaceEmitter.s_indent_ns_member)}\n};`;
            }
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

        if(this.m_ns === "Core") {
            eexports.push("$BSQ");
        }
        const exportdecl = `export {\n    ${eexports.join(", ")}\n};`

        return [...stdimps, depimps, fmts, nstdecl, constdecls, ifuncdecls, kfuncdecls, lambdas, ...chkdecls, iidm, exportdecl]
            .filter((cmpt) => cmpt !== "")
            .join("\n");
    }
}

class AssemblyEmitter {
    readonly assembly: TIRAssembly;
    readonly nsdeps: Map<string, string[]>;

    readonly namespacedecls: Map<string, string> = new Map<string, string>();
    
    typeEncodedAsUnion(tt: TIRTypeKey): boolean {
        assert(this.assembly.typeMap.has(tt), `missing type name entry ${tt}`);

        const ttype = this.assembly.typeMap.get(tt) as TIRType;
        return (ttype instanceof TIRConceptType) || (ttype instanceof TIRUnionType);
    }

    constructor(assembly: TIRAssembly, nsdeps: Map<string, string[]>) {
        this.assembly = assembly;
        this.nsdeps = nsdeps;
    }

    private processAssembly(asdeno: boolean) {
        this.assembly.namespaceMap.forEach((nsd, ns) => {
            const nsemit = new NamespaceEmitter(this.assembly, ns, nsd);
            const tirns = nsemit.emitNamespace(this.nsdeps.get(ns) as string[], asdeno);

            this.namespacedecls.set(ns, tirns);
        });
    };

    generateTSCode(asdeno: boolean): {nsname: string, contents: string}[] {
        this.processAssembly(asdeno);

        let outmodules: {nsname: string, contents: string}[] = [];

        this.namespacedecls.forEach((nsd, name) => {
            outmodules.push({nsname: `${name}.ts`, contents: nsd});
        });

        return outmodules;
    }
}

export {
    AssemblyEmitter
};
