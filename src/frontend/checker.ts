import assert from "node:assert";

import { APIDecl, APIErrorTypeDecl, APIFailedTypeDecl, APIRejectedTypeDecl, APIResultTypeDecl, APISuccessTypeDecl, CRegexValidatorTypeDecl, CStringOfTypeDecl, AbstractNominalTypeDecl, Assembly, ConceptTypeDecl, ConstMemberDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, EntityTypeDecl, EnumTypeDecl, EnvironmentVariableInformation, ErrTypeDecl, EventListTypeDecl, ExpandoableTypeDecl, ExplicitInvokeDecl, InternalEntityTypeDecl, InvariantDecl, InvokeExample, InvokeExampleDeclFile, InvokeExampleDeclInline, InvokeTemplateTermDecl, ListTypeDecl, MapEntryTypeDecl, MapTypeDecl, MemberFieldDecl, MethodDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, OkTypeDecl, OptionTypeDecl, PathFragmentOfTypeDecl, PathGlobOfTypeDecl, PathOfTypeDecl, PathValidatorTypeDecl, PostConditionDecl, PreConditionDecl, PrimitiveConceptTypeDecl, PrimitiveEntityTypeDecl, QueueTypeDecl, RegexValidatorTypeDecl, ResourceInformation, ResultTypeDecl, SetTypeDecl, StackTypeDecl, StringOfTypeDecl, TaskActionDecl, TaskDecl, TaskMethodDecl, TypeFunctionDecl, TypeTemplateTermDecl, TypedeclTypeDecl, ValidateDecl, WELL_KNOWN_EVENTS_VAR_NAME, WELL_KNOWN_RETURN_VAR_NAME, TemplateTermDeclExtraTag, PairTypeDecl, SomeTypeDecl, NSRegexREInfoEntry, NSRegexInfo, NSRegexNameInfo, InvokeParameterDecl, AbstractCollectionTypeDecl, ConstructableTypeDecl, MAX_SAFE_NAT, MIN_SAFE_INT, MAX_SAFE_INT } from "./assembly.js";
import { SourceInfo } from "./build_decls.js";
import { AutoTypeSignature, EListTypeSignature, ErrorTypeSignature, FullyQualifiedNamespace, LambdaTypeSignature, NominalTypeSignature, StringTemplateTypeSignature, TemplateConstraintScope, TemplateNameMapper, TemplateTypeSignature, TypeSignature, VoidTypeSignature } from "./type.js";
import { AbortStatement, AbstractBodyImplementation, AccessEnumExpression, AccessEnvValueExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, ArgumentValue, AssertStatement, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndExpression, BinLogicIFFExpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, BinderInfo, BlockStatement, BodyImplementation, BuiltinBodyImplementation, CallNamespaceFunctionExpression, CallRefSelfExpression, CallRefThisExpression, CallTaskActionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, DebugStatement, EmptyStatement, EnvironmentBracketStatement, EnvironmentUpdateStatement, Expression, ExpressionBodyImplementation, ExpressionTag, ITest, ITestErr, ITestNone, ITestOk, ITestSome, ITestType, IfElifElseStatement, IfElseStatement, IfExpression, IfStatement, InterpolateExpression, LambdaInvokeExpression, LetExpression, LiteralExpressionValue, LiteralNoneExpression, LiteralPathExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralTemplateStringExpression, LiteralTypeDeclFloatPointValueExpression, LiteralTypeDeclIntegralValueExpression, LiteralTypeDeclValueExpression, LiteralTypedStringExpression, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, MatchStatement, NamedArgumentValue, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PositionalArgumentValue, PostfixAccessFromName, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixLiteralKeyAccess, PostfixOp, PostfixOpTag, PostfixProjectFromNames, PredicateUFBodyImplementation, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, RefArgumentValue, ReturnStatement, SelfUpdateStatement, SpecialConstructorExpression, SpecialConverterExpression, SpreadArgumentValue, StandardBodyImplementation, Statement, StatementTag, SwitchStatement, SynthesisBodyImplementation, TaskAccessInfoExpression, TaskAllExpression, TaskDashExpression, TaskEventEmitStatement, TaskMultiExpression, TaskRaceExpression, TaskRunExpression, TaskStatusStatement, TaskYieldStatement, ThisUpdateStatement, ValidateStatement, VarUpdateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VariableRetypeStatement, VoidRefCallStatement } from "./body.js";
import { EListStyleTypeInferContext, SimpleTypeInferContext, TypeEnvironment, TypeInferContext, VarInfo } from "./checker_environment.js";
import { TypeCheckerRelations } from "./checker_relations.js";

import { validateStringLiteral, validateCStringLiteral, loadConstAndValidateRESystem, runNamedRegexAccepts } from "@bosque/jsbrex";

class TypeError {
    readonly file: string;
    readonly line: number;
    readonly msg: string;

    constructor(file: string, line: number, msg: string) {
        this.file = file;
        this.line = line;
        this.msg = msg;
    }
}

const CLEAR_FILENAME = "[GLOBAL]";

class TypeChecker {
    private file: string = CLEAR_FILENAME;
    private ns: FullyQualifiedNamespace = new FullyQualifiedNamespace(["NOT SET"]);
    readonly errors: TypeError[] = [];

    readonly constraints: TemplateConstraintScope;
    readonly relations: TypeCheckerRelations;

    constructor(constraints: TemplateConstraintScope, relations: TypeCheckerRelations) {
        this.constraints = constraints;
        this.relations = relations;
    }

    private reportError(sinfo: SourceInfo, msg: string) {
        this.errors.push(new TypeError(this.file, sinfo.line, msg));
    }

    private checkError(sinfo: SourceInfo, cond: boolean, msg: string): boolean {
        if (cond) {
            this.reportError(sinfo, msg);
        }

        return cond;
    }

    private static safeTypePrint(tsig: TypeSignature | undefined): string {
        return tsig === undefined ? "[undef_type]" : tsig.tkeystr;
    }

    getErrorList(): TypeError[] {
        return this.errors;
    }

    private getWellKnownType(name: string): TypeSignature {
        assert(this.relations.wellknowntypes.has(name), `Well known type ${name} not found`);
        return this.relations.wellknowntypes.get(name) as TypeSignature;
    }

    private getStringOfType(oftype: TypeSignature): TypeSignature {
        const stringofdecl = this.relations.assembly.getCoreNamespace().typedecls.find((td) => td.name === "StringOf") as StringOfTypeDecl;
        return new NominalTypeSignature(oftype.sinfo, undefined, stringofdecl, [oftype]);
    }

    private getCStringOfType(oftype: TypeSignature): TypeSignature {
        const cstringofdecl = this.relations.assembly.getCoreNamespace().typedecls.find((td) => td.name === "CStringOf") as CStringOfTypeDecl;
        return new NominalTypeSignature(oftype.sinfo, undefined, cstringofdecl, [oftype]);
    }

    private getEventListOf(oftype: TypeSignature): TypeSignature {
        const eventlistdecl = this.relations.assembly.getCoreNamespace().typedecls.find((td) => td.name === "EventList") as EventListTypeDecl;
        return new NominalTypeSignature(oftype.sinfo, undefined, eventlistdecl, [oftype]);
    }

    private isBooleanType(t: TypeSignature): boolean {
        return (t.tkeystr === "Bool");
    }

    private isVoidType(t: TypeSignature): boolean {
        return (t.tkeystr === "Void");
    }

    private processITest_None(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        //!none === some
        if(isnot) {
            const rinfo = this.relations.splitOnSome(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to some-split type ${src.tkeystr}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.overlapSomeT, bindfalse: rinfo.hasnone ? this.getWellKnownType("None") : undefined};
            }
        }
        else {
            const rinfo = this.relations.splitOnNone(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to none-split type ${src.tkeystr}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.hasnone ? this.getWellKnownType("None") : undefined, bindfalse: rinfo.remainSomeT };
            }
        }
    }

    private processITest_Some(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        //!some === none
        if(isnot) {
            const rinfo = this.relations.splitOnNone(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to none-split type ${src.tkeystr}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.hasnone ? this.getWellKnownType("None") : undefined, bindfalse: rinfo.remainSomeT};
            }
        }
        else {
            const rinfo = this.relations.splitOnSome(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to some-split type ${src.tkeystr}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.overlapSomeT, bindfalse: rinfo.hasnone ? this.getWellKnownType("None") : undefined };
            }
        }
    }

    private processITest_Ok(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        //!ok === err
        if(isnot) {
            const rinfo = this.relations.splitOnErr(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to err-split type ${src.tkeystr}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.overlapErrE, bindfalse: rinfo.remainOkT};
            }
        }
        else {
            const rinfo = this.relations.splitOnOk(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to nothing-split type ${src.tkeystr}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.overlapOkT, bindfalse: rinfo.remainErrE };
            }
        }
    }

    private processITest_Err(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        //!err === ok
        if(isnot) {
            const rinfo = this.relations.splitOnOk(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to err-split type ${src.tkeystr}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.overlapOkT, bindfalse: rinfo.remainErrE};
            }
        }
        else {
            const rinfo = this.relations.splitOnErr(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to nothing-split type ${src.tkeystr}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.overlapErrE, bindfalse: rinfo.remainOkT };
            }
        }
    }

    private processITest_Type(src: TypeSignature, oftype: TypeSignature): { ttrue: TypeSignature[], tfalse: TypeSignature[] } {
        const rinfo = this.relations.refineType(src, oftype, this.constraints);
        if(rinfo === undefined) {
            this.reportError(src.sinfo, `Unable to some-split type ${src.tkeystr}`);
            return { ttrue: [], tfalse: [] };
        }
        else {
            return { ttrue: rinfo.overlap, tfalse: rinfo.remain };
        }
    }
    
    private processITestAsBoolean(sinfo: SourceInfo, env: TypeEnvironment, src: TypeSignature, tt: ITest): { ttrue: boolean, tfalse: boolean } {
        if(tt instanceof ITestType) {
            if(!this.checkTypeSignature(tt.ttype)) {
                return { ttrue: false, tfalse: false };
            }
            else {
                const tres = this.processITest_Type(src, tt.ttype);
                if(tt.isnot) {
                    return { ttrue: tres.tfalse.length !== 0, tfalse: tres.ttrue.length !== 0 };
                }
                else {
                    return { ttrue: tres.ttrue.length !== 0, tfalse: tres.tfalse.length !== 0 };
                }
            }
        }
        else {
            if(tt instanceof ITestNone) {
                const tres = this.processITest_None(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else if(tt instanceof ITestSome) {
                const tres = this.processITest_Some(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else if(tt instanceof ITestOk) {
                const tres = this.processITest_Ok(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else {
                assert(tt instanceof ITestErr, "missing case in ITest");
                const tres = this.processITest_Err(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
        }
    }

    private processITestConvertForce(opts: TypeSignature[], converttype: TypeSignature): TypeSignature | undefined {
        if(opts.length === undefined) {
            return undefined;
        }

        return converttype;
    }

    private processITestConvertLUB(sinfo: SourceInfo, opts: TypeSignature[], lubtype: TypeSignature): TypeSignature | undefined {
        if(opts.length === undefined) {
            return undefined;
        }

        return this.relations.flowTypeLUB(sinfo, lubtype, opts, this.constraints);
    }

    private processITestAsConvert(sinfo: SourceInfo, env: TypeEnvironment, src: TypeSignature, tt: ITest): { ttrue: TypeSignature | undefined, tfalse: TypeSignature | undefined } {
        if(tt instanceof ITestType) {
            if(!this.checkTypeSignature(tt.ttype)) {
                return { ttrue: undefined, tfalse: undefined };
            }
            else {
                const tres = this.processITest_Type(src, tt.ttype);
                if(tt.isnot) {
                    const ttrue = tres.tfalse.length !== 0 ? this.processITestConvertLUB(sinfo, tres.tfalse, src) : undefined; //negate takes the remain and lubs to the src
                    const tfalse = tres.ttrue.length !== 0 ? this.processITestConvertForce(tres.ttrue, tt.ttype) : undefined; //overlap and passes as the user spec type -- does not matter now but short circuiting return will use this

                    return { ttrue: ttrue, tfalse: tfalse };
                }
                else {
                    const ttrue = tres.ttrue.length !== 0 ? this.processITestConvertForce(tres.ttrue, tt.ttype) : undefined; //always cast to what the user asked for
                    const tfalse = tres.tfalse.length !== 0 ? this.processITestConvertLUB(sinfo, tres.tfalse, src) : undefined; //cast to the LUB of the remaining types (with src as a default option)

                    return { ttrue: ttrue, tfalse: tfalse };
                }
            }
        }
        else {
            if(tt instanceof ITestNone) {
                const tres = this.processITest_None(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else if(tt instanceof ITestSome) {
                const tres = this.processITest_Some(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else if(tt instanceof ITestOk) {
                const tres = this.processITest_Ok(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else {
                assert(tt instanceof ITestErr, "missing case in ITest");
                const tres = this.processITest_Err(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
        }
    }

    private checkTemplateInstantiationIsOkWithDecls(sinfo: SourceInfo, targs: TypeSignature[], decls: TypeTemplateTermDecl[]): boolean {
        assert(targs.length === decls.length, "Template instantiation mismatch");
        
        for(let i = 0; i < targs.length; ++i) {
            const tdecl = decls[i];
            const targ = targs[i];

            if(this.checkError(sinfo, !this.relations.isSubtypeOf(targ, tdecl.tconstraint, this.constraints), `Template argument ${tdecl.name} is not a subtype of ${tdecl.tconstraint.tkeystr}`)) {
                return false;
            }

            if(tdecl.extraTags.length !== 0) {
                if(tdecl.extraTags.includes(TemplateTermDeclExtraTag.Unique)) {
                    this.checkError(sinfo, !this.relations.isUniqueType(targ, this.constraints), `Template argument ${tdecl.name} is not a unique type`);
                    return false;
                }
            }
        }

        return true;
    }

    private checkTemplateTypesOnType(sinfo: SourceInfo, terms: TypeTemplateTermDecl[]) {
        let allnames = new Set<string>();

        for(let i = 0; i < terms.length; ++i) {
            const terminfo = terms[i];

            this.checkError(sinfo, allnames.has(terminfo.name), `Template type ${terminfo.name} is already defined`);
            allnames.add(terminfo.name);

            if(this.checkTypeSignature(terminfo.tconstraint)) {
                this.checkError(sinfo, !this.relations.isValidTemplateRestrictionType(terminfo.tconstraint), `Template type ${terminfo.name} is not a valid template restriction type`);
            }
        }
    }

    private checkTemplateTypesOnInvoke(sinfo: SourceInfo, terms: InvokeTemplateTermDecl[]) {
        let allnames = new Set<string>();

        for(let i = 0; i < terms.length; ++i) {
            const terminfo = terms[i];

            this.checkError(sinfo, allnames.has(terminfo.name), `Template type ${terminfo.name} is already defined`);
            allnames.add(terminfo.name);

            if(this.checkTypeSignature(terminfo.tconstraint)) {
                this.checkError(sinfo, !this.relations.isValidTemplateRestrictionType(terminfo.tconstraint), `Template type ${terminfo.name} is not a valid template restriction type`);
            }
        }
    }

    //Given a type signature -- check that is is well formed and report any issues
    private checkTypeSignature(type: TypeSignature): boolean {
        if(type instanceof ErrorTypeSignature || type instanceof AutoTypeSignature) {
            return false;
        }
        else if(type instanceof VoidTypeSignature) {
            return true;
        }
        else if(type instanceof TemplateTypeSignature) {
            return this.constraints.resolveConstraint(type.name) !== undefined;
        }
        else if(type instanceof NominalTypeSignature) {
            const typesok = type.alltermargs.every((targ) => this.checkTypeSignature(targ));

            if(!typesok) {
                return false;
            }
            
            if(type.decl.isSpecialResultEntity()) {
                if(type.alltermargs.length !== 2) {
                    this.reportError(type.sinfo, `Type ${type.decl.name} expected ${type.decl.terms.length} terms but got ${type.alltermargs.length}`);
                    return false;
                }
            }
            else if(type.decl.isSpecialAPIResultEntity()) {
                if(type.alltermargs.length !== 1) {
                    this.reportError(type.sinfo, `Type ${type.decl.name} expected ${type.decl.terms.length} terms but got ${type.alltermargs.length}`);
                    return false;
                }
            }
            else {
                if(type.alltermargs.length !== type.decl.terms.length) {
                    this.reportError(type.sinfo, `Type ${type.decl.name} expected ${type.decl.terms.length} terms but got ${type.alltermargs.length}`);
                    return false;
                }

                return this.checkTemplateInstantiationIsOkWithDecls(type.sinfo, type.alltermargs, type.decl.terms);
            }

            return true;
        }
        else if(type instanceof EListTypeSignature) {
            return type.entries.every((entry) => this.checkTypeSignature(entry));
        }
        else if(type instanceof StringTemplateTypeSignature) {
            return type.argtypes.every((entry) => this.checkTypeSignature(entry));
        }
        else if(type instanceof LambdaTypeSignature) {
            const oksig = type.params.every((pp) => this.checkTypeSignature(pp.type)) && this.checkTypeSignature(type.resultType);
            if(!oksig) {
                return false;
            }

            let refct = 0;
            for(let i = 0; i < type.params.length; ++i) {
                const pp = type.params[i];

                refct += pp.isRefParam ? 1 : 0;
                if(pp.isRestParam && i !== type.params.length - 1) {
                    this.reportError(type.sinfo, `Rest parameter must be the last parameter in the lambda`);
                    return false;
                }
            }

            return refct <= 1;
        }
        else {
            assert(false, "Unknown TypeSignature type");
        }
    }

    private checkValueEq(lhsexp: Expression, lhs: TypeSignature, rhsexp: Expression, rhs: TypeSignature): "err" | "lhsnone" | "rhsnone" | "stricteq" | "lhskeyeqoption" | "rhskeyeqoption" {
        if(!(lhs instanceof NominalTypeSignature) || !(rhs instanceof NominalTypeSignature)) {
            return "err";
        }

        if((lhs.decl instanceof OptionTypeDecl) && (rhs.decl instanceof OptionTypeDecl)) {
            return "err";
        }
        else if(lhs.decl instanceof OptionTypeDecl) {
            if(!this.relations.isUniqueKeyType(rhs, this.constraints)) {
                return "err";
            }

            if(rhsexp.tag === ExpressionTag.LiteralNoneExpression) {
                return "rhsnone";
            }
            else {
                return this.relations.areSameTypes(rhs, lhs.alltermargs[0], this.constraints) ? "rhskeyeqoption" : "err";
            }
        }
        else if(rhs.decl instanceof OptionTypeDecl) {
            if(!this.relations.isUniqueKeyType(lhs, this.constraints)) {
                return "err";
            }

            if(lhsexp.tag === ExpressionTag.LiteralNoneExpression) {
                return "lhsnone";
            }
            else {
                return this.relations.areSameTypes(lhs, rhs.alltermargs[0], this.constraints) ? "lhskeyeqoption" : "err";
            }
        }
        else {
            if(!this.relations.isUniqueKeyType(lhs, this.constraints) && !this.relations.isUniqueKeyType(rhs, this.constraints)) {
                return "err";
            }

            return this.relations.areSameTypes(lhs, rhs, this.constraints) ? "stricteq" : "err";

        }
    }

    private checkTemplateBindingsOnInvoke(env: TypeEnvironment, targs: TypeSignature[], decl: ExplicitInvokeDecl): TemplateNameMapper | undefined {
        if(targs.length !== decl.terms.length) {
            this.reportError(decl.sinfo, `Invoke ${decl.name} expected ${decl.terms.length} terms but got ${targs.length}`);
            return undefined;
        }

        let tmap = new Map<string, TypeSignature>();
        for(let i = 0; i < targs.length; ++i) {
            const targ = targs[i];
            const tdecl = decl.terms[i];

            const trestrict = tdecl.tconstraint;
            if(!this.relations.isSubtypeOf(targ, trestrict, this.constraints)) {
                this.reportError(decl.sinfo, `Template argument ${tdecl.name} is not a subtype of ${tdecl.tconstraint.tkeystr}`);
                return undefined;
            }

            if(tdecl.extraTags.length !== 0) {
                if(tdecl.extraTags.includes(TemplateTermDeclExtraTag.Unique)) {
                    this.checkError(decl.sinfo, !this.relations.isUniqueType(targ, this.constraints), `Template argument ${tdecl.name} is not a unique type`);
                    return undefined;
                }
            }

            tmap.set(tdecl.name, targ);
        }

        return TemplateNameMapper.createInitialMapping(tmap);
    }

    private checkSingleParam(env: TypeEnvironment, arg: ArgumentValue, param: InvokeParameterDecl, imapper: TemplateNameMapper): TypeSignature {
        if(arg instanceof SpreadArgumentValue) {
            this.reportError(arg.exp.sinfo, `Spread argument cannot be used except as part of rest args`);
        }

        if(param.isRefParam) {
            this.checkError(arg.exp.sinfo, !(arg instanceof RefArgumentValue), `Parameter ${param.name} is a reference parameter and must be passed by reference`);
        }

        if(arg instanceof NamedArgumentValue) {
            this.checkError(arg.exp.sinfo, arg.name !== param.name, `Named argument ${arg.name} does not match parameter name ${param.name}`);
        }

        const ptype = param.type.remapTemplateBindings(imapper);

        const argtype = this.checkExpression(env, arg.exp, new SimpleTypeInferContext(ptype));
        this.checkError(arg.exp.sinfo, !this.relations.isSubtypeOf(argtype, ptype, this.constraints), `Argument ${param.name} expected type ${param.type.tkeystr} but got ${argtype.tkeystr}`);

        return argtype;
    }

    private checkRestParam(env: TypeEnvironment, args: ArgumentValue[], param: InvokeParameterDecl, imapper: TemplateNameMapper): [boolean, TypeSignature][] {
        const ptype = param.type.remapTemplateBindings(imapper);
        const etype = this.relations.getExpandoableOfType(ptype);
        if(etype === undefined) {
            this.reportError(args[args.length - 1].exp.sinfo, `Rest parameter ${param.name} must be of type Expandoable`);
            return [];
        }

        let rtypes: [boolean, TypeSignature][] = [];
        for(let i = 0; i < args.length; ++i) {
            const arg = args[i];

            if(arg instanceof RefArgumentValue) {
                this.reportError(arg.exp.sinfo, `Rest args cannot be passed by reference`);
            }

            if(arg instanceof PositionalArgumentValue) {
                const argtype = this.checkExpression(env, arg.exp, new SimpleTypeInferContext(etype));
                rtypes.push([false, argtype]);

                this.checkError(arg.exp.sinfo, !this.relations.isSubtypeOf(argtype, etype, this.constraints), `Rest argument ${i} expected type ${etype.tkeystr}`);
            }
            else {
                const argtype = this.checkExpression(env, arg.exp, undefined);
                rtypes.push([true, argtype]);

                const argetype = this.relations.getExpandoableOfType(argtype);
                this.checkError(arg.exp.sinfo, argetype === undefined || !this.relations.areSameTypes(argetype, etype, this.constraints), `Rest argument ${i} expected to be container of type ${etype.tkeystr}`);
            }
        }

        return rtypes;
    }

    private checkArgumentList(sinfo: SourceInfo, env: TypeEnvironment, args: ArgumentValue[], params: InvokeParameterDecl[], imapper: TemplateNameMapper): { shuffleinfo: [number, TypeSignature | undefined][], restinfo: [number, boolean, TypeSignature][] | undefined } {
        let argsuffle: (ArgumentValue | undefined)[] = [];
        let argsuffleidx: number[] = [];
        let argsuffletype: (TypeSignature | undefined)[] = [];
        for(let i = 0; i < args.length; ++i) {
            argsuffle.push(undefined);
            argsuffleidx.push(-1);
            argsuffletype.push(undefined);
        }

        //fill in all the named arguments
        for(let i = 0; i < args.length; ++i) {
            if(args[i] instanceof NamedArgumentValue) {
                const narg = args[i] as NamedArgumentValue;
                const paramidx = params.findIndex((p) => p.name === narg.name);
                if(paramidx === -1) {
                    this.reportError(narg.exp.sinfo, `Named argument ${narg.name} not found in parameter list`);
                }
                else if(params[paramidx].isRestParam) {
                    this.reportError(narg.exp.sinfo, `Named argument ${narg.name} cannot be assigned to rest parameter`);
                }
                else {
                    argsuffle[paramidx] = narg;
                    argsuffleidx[paramidx] = i;
                }
            }
        }

        const nonrestparams = params.filter((p) => !p.isRestParam);
        const restparam = params.find((p) => p.isRestParam); //is only 1 at the end (from parser)

        let ppos = argsuffle.findIndex((av) => av === undefined);
        let apos = args.findIndex((av) => !(av instanceof NamedArgumentValue));
        while(ppos !== -1 && ppos < nonrestparams.length && apos !== -1 && apos < args.length) {
            argsuffle[ppos] = args[apos];
            argsuffleidx[ppos] = apos;

            ppos = argsuffle.findIndex((av, j) => j > ppos && av === undefined);
            apos = args.findIndex((av, j) =>  j > apos && !(av instanceof NamedArgumentValue));
        }

        let restinfo: [number, boolean, TypeSignature][] | undefined = undefined;
        if(restparam === undefined) {
            if(args.length > params.length) {
                this.reportError(sinfo, `Too many arguments provided to function`);
            }

            for(let i = argsuffleidx.length; i < params.length; ++i) {
                argsuffleidx.push(-1);
            }

            for(let i = 0; i < params.length; ++i) {
                if(argsuffle[i] === undefined) {
                    this.checkError(sinfo, params[i].optDefaultValue === undefined, `Required argument ${params[i].name} not provided`);
                }
                else {
                    argsuffletype[i] = this.checkSingleParam(env, argsuffle[i] as ArgumentValue, params[i], imapper);
                }
            }
        }
        else {
            let restargs = args.slice(nonrestparams.length);
            const restypes = this.checkRestParam(env, restargs, restparam, imapper);

            restinfo = [];
            for(let i = nonrestparams.length; i < args.length; ++i) {
                const rri = restypes[i - nonrestparams.length] as [boolean, TypeSignature];
                restinfo.push([i, rri[0], rri[1]]);
            }
        }

        return { shuffleinfo: argsuffleidx.map((si, i) => [si, argsuffletype[i]]), restinfo: restinfo };
    }

    private checkConstructorArgumentList(sinfo: SourceInfo, env: TypeEnvironment, args: ArgumentValue[], bnames: {name: string, type: TypeSignature, hasdefault: boolean}[]): [number, string, TypeSignature][] {
        let argsuffle: (ArgumentValue | undefined)[] = [];
        let argsuffleidx: number[] = [];
        for(let i = 0; i < args.length; ++i) {
            argsuffle.push(undefined);
            argsuffleidx.push(-1);
        }

        //fill in all the named arguments
        for(let i = 0; i < args.length; ++i) {
            if(args[i] instanceof NamedArgumentValue) {
                const narg = args[i] as NamedArgumentValue;
                const paramidx = bnames.findIndex((p) => p.name === narg.name);
                if(paramidx === -1) {
                    this.reportError(narg.exp.sinfo, `Named argument ${narg.name} not found in parameter list`);
                }
                else {
                    argsuffle[paramidx] = narg;
                    argsuffleidx[paramidx] = i;
                }
            }
        }

        let ppos = argsuffle.findIndex((av) => av === undefined);
        let apos = args.findIndex((av) => !(av instanceof NamedArgumentValue));
        while(ppos !== -1 && ppos < bnames.length && apos !== -1 && apos < args.length) {
            argsuffle[ppos] = args[apos];
            argsuffleidx[ppos] = apos;

            ppos = argsuffle.findIndex((av, j) => j > ppos && av === undefined);
            apos = args.findIndex((av, j) =>  j > apos && !(av instanceof NamedArgumentValue));
        }

        if(args.length > bnames.length) {
            this.reportError(sinfo, `Too many arguments provided to function`);
        }

        for(let i = argsuffleidx.length; i < bnames.length; ++i) {
            argsuffleidx.push(-1);
        }

        for(let i = 0; i < bnames.length; ++i) {
            if(argsuffle[i] === undefined) {
                this.checkError(sinfo, !bnames[i].hasdefault, `Required argument ${bnames[i].name} not provided`);
            }
            else {
                const argexp = (argsuffle[i] as ArgumentValue).exp;
                const argtype = this.checkExpression(env, argexp, new SimpleTypeInferContext(bnames[i].type));
                this.checkError(argexp.sinfo, !this.relations.isSubtypeOf(argtype, bnames[i].type, this.constraints), `Argument ${bnames[i].name} expected type ${bnames[i].type.tkeystr} but got ${argtype.tkeystr}`);
            }
        }

        return argsuffleidx.map((idx, i) => [idx, bnames[i].name, bnames[i].type]);
    }

    private checkLiteralNoneExpression(env: TypeEnvironment, exp: LiteralNoneExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("None"));
    }

    private checkLiteralBoolExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkLiteralNatExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        const nval = BigInt(exp.value.slice(0, exp.value.length - 1));
        this.checkError(exp.sinfo, nval < 0n, "Nat literal cannot be negative");
        this.checkError(exp.sinfo, MAX_SAFE_NAT < nval, "Nat literal out of valid range");

        return exp.setType(this.getWellKnownType("Nat"));
    }

    private checkLiteralIntExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        const nval = BigInt(exp.value.slice(0, exp.value.length - 1));
        this.checkError(exp.sinfo, nval < MIN_SAFE_INT, "Int literal cannot be negative");
        this.checkError(exp.sinfo, MAX_SAFE_INT < nval, "Int literal out of valid range");

        return exp.setType(this.getWellKnownType("Int"));
    }

    private checkLiteralBigNatExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        const nval = BigInt(exp.value.slice(0, exp.value.length - 1));
        this.checkError(exp.sinfo, nval < 0n, "BigNat literal cannot be negative");

        return exp.setType(this.getWellKnownType("BigNat"));
    }

    private checkLiteralBigIntExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("BigInt"));
    }

    private checkLiteralRationalExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        const slpos = exp.value.indexOf("/");
        const den = BigInt(exp.value.slice(slpos + 1, -1));

        this.checkError(exp.sinfo, MAX_SAFE_NAT < den, "Rational literal denominator out of valid range");

        return exp.setType(this.getWellKnownType("Rational"));
    }

    private static isValidFloatLiteral(val: string): boolean {
        const fval = Number.parseFloat(val);
        return !Number.isNaN(fval) && Number.isFinite(fval);
    }

    private static isValidDecimalLiteral(val: string): boolean {
        //TODO: we need to do a bit more on the bounds etc. here
        return true;
    }

    private static isValidDecimalDegreeLiteral(val: string, min: number, max: number): boolean {
        const pcstr = val.slice(val.indexOf("."));
        if(pcstr.length > 8) {
            return false; //max 8 decimal places of precision
        }

        const fval = Number.parseFloat(val);
        return !Number.isNaN(fval) && Number.isFinite(fval) && min <= fval && fval <= max;
    }

    private checkLiteralFloatExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        this.checkError(exp.sinfo, !TypeChecker.isValidFloatLiteral(exp.value.slice(0, exp.value.length - 1)), "Invalid Float literal");

        return exp.setType(this.getWellKnownType("Float"));
    }

    private checkLiteralDecimalExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        this.checkError(exp.sinfo, !TypeChecker.isValidDecimalLiteral(exp.value.slice(0, exp.value.length - 1)), "Invalid Decimal literal");

        return exp.setType(this.getWellKnownType("Decimal"));
    }

    private checkLiteralDecimalDegreeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        this.checkError(exp.sinfo, !TypeChecker.isValidDecimalDegreeLiteral(exp.value.slice(0, exp.value.length - 2), -360.0, 360.0), "Invalid DecimalDegree literal");

        return exp.setType(this.getWellKnownType("DecimalDegree"));
    }

    private checkLiteralLatLongCoordinateExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        const latsplit = exp.value.indexOf("lat");
        const latval = exp.value.slice(0, latsplit);
        const longval = exp.value.slice(latsplit + 3, exp.value.length - 4);

        this.checkError(exp.sinfo, !TypeChecker.isValidDecimalDegreeLiteral(latval, -180.0, 180.0), "Invalid Latitude value");
        this.checkError(exp.sinfo, !TypeChecker.isValidDecimalDegreeLiteral(longval, -90.0, 90.0), "Invalid Longitude value");

        return exp.setType(this.getWellKnownType("LatLongCoordinate"));
    }

    private checkLiteralComplexNumberExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        let spos = exp.value.lastIndexOf("+");
        if(spos === -1) {
            spos = exp.value.lastIndexOf("-");
        }

        const realval = exp.value.slice(0, spos);
        const imagval = exp.value.slice(spos, exp.value.length - 1);

        this.checkError(exp.sinfo, !TypeChecker.isValidFloatLiteral(realval), "Invalid Complex literal real value");
        this.checkError(exp.sinfo, !TypeChecker.isValidFloatLiteral(imagval), "Invalid Complex literal imaginary value");

        return exp.setType(this.getWellKnownType("Complex"));
    }

    private checkLiteralByteBufferExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("ByteBuffer"));
    }

    private checkLiteralUUIDv4Expression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("UUIDv4"));
    }

    private checkLiteralUUIDv7Expression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("UUIDv7"));
    }

    private checkLiteralSHAContentHashExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("SHAContentHash"));
    }

    private checkLiteralDateTimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        //TODO: missing years and days in month validation here
        return exp.setType(this.getWellKnownType("DateTime"));
    }

    private checkLiteralUTCDateTimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        //TODO: missing years and days in month validation here -- also leap seconds
        return exp.setType(this.getWellKnownType("UTCDateTime"));
    }

    private checkLiteralPlainDateExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        //TODO: missing years and days in month validation here
        return exp.setType(this.getWellKnownType("PlainDate"));
    }

    private checkLiteralPlainTimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("PlainTime"));
    }

    private checkLiteralLogicalTimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("LogicalTime"));
    }

    private checkLiteralTickTimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("TickTime"));
    }

    private checkLiteralISOTimeStampExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        //TODO: missing years and days in month validation here -- also leap seconds
        return exp.setType(this.getWellKnownType("ISOTimeStamp"));
    }

    private checkLiteralDeltaDateTimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaDateTime"));
    }

    private checkLiteralDeltaPlainDateExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaPlainDate"));
    }

    private checkLiteralDeltaPlainTimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaPlainTime"));
    }

    private checkLiteralDeltaISOTimeStampExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaISOTimeStamp"));
    }

    private checkLiteralDeltaSecondsExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaSeconds"));
    }

    private checkLiteralDeltaTickExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaTick"));
    }

    private checkLiteralDeltaLogicalExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaLogical"));
    }

    private checkLiteralUnicodeRegexExpression(env: TypeEnvironment, exp: LiteralRegexExpression): TypeSignature {
        //TODO: validate regex parse is error free

        return exp.setType(this.getWellKnownType("UnicodeRegex"));
    }

    private checkLiteralCRegexExpression(env: TypeEnvironment, exp: LiteralRegexExpression): TypeSignature {
        //TODO: validate regex parse is error free

        if(exp.value.endsWith("c")) {
            return exp.setType(this.getWellKnownType("CRegex"));
        }
        else {
            return exp.setType(this.getWellKnownType("PathRegex"));
        }
    }

    private checkLiteralStringExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        try {
            const vs = validateStringLiteral(exp.value.slice(1, exp.value.length - 1));
            exp.resolvedValue = vs;
        } catch(err) {
            this.reportError(exp.sinfo, (err as Error).message);
        }
        
        return exp.setType(this.getWellKnownType("String"));
    }

    private checkLiteralCStringExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        try {
            const vs = validateCStringLiteral(exp.value.slice(1, exp.value.length - 1));
            exp.resolvedValue = vs;
        } catch(err) {
            this.reportError(exp.sinfo, (err as Error).message);
        }
        
        return exp.setType(this.getWellKnownType("CString"));
    }

    private runValidatorRegex(sinfo: SourceInfo, rename: string, litstr: string, isunicode: boolean) {
        const accepts = runNamedRegexAccepts(rename, litstr, isunicode);
        this.checkError(sinfo, !accepts, `Literal value does not match regex validator ${rename}`);
    }

    private checkLiteralTypedStringExpression(env: TypeEnvironment, exp: LiteralTypedStringExpression): TypeSignature {
        if(!this.checkTypeSignature(exp.stype)) {
            return exp.setType(new ErrorTypeSignature(exp.stype.sinfo, undefined));
        }

        const revalidator = this.relations.resolveStringRegexValidatorInfo(this.ns, exp.stype);
        if(revalidator === undefined) {
            return exp.setType(this.getStringOfType(exp.stype));
        }

        if(revalidator === undefined) {
            this.reportError(exp.sinfo, `Bad Validator type for StringOf -- could not resolve to a valid regex`);
            return exp.setType(new ErrorTypeSignature(exp.stype.sinfo, undefined));
        }

        if(!this.relations.isSubtypeOf(exp.stype, this.getWellKnownType("RegexValidator"), this.constraints)) {
            this.reportError(exp.sinfo, `Bad Validator type for StringOf -- expected a RegexValidator`);
            return exp.setType(new ErrorTypeSignature(exp.stype.sinfo, undefined));
        }

        try {
            const vs = validateStringLiteral(exp.value.slice(1, exp.value.length - 1));
            if(vs === null) {
                this.reportError(exp.sinfo, `Invalid String literal`);
                return exp.setType(new ErrorTypeSignature(exp.stype.sinfo, undefined));
            }
            else {
                this.runValidatorRegex(exp.sinfo, revalidator, vs, true); 
                exp.resolvedValue = vs;
            }
        } catch(err) {
            this.reportError(exp.sinfo, (err as Error).message);
        }

        return exp.setType(this.getStringOfType(exp.stype));
    }

    private checkLiteralTypedCStringExpression(env: TypeEnvironment, exp: LiteralTypedStringExpression): TypeSignature {
        if(!this.checkTypeSignature(exp.stype)) {
            return exp.setType(new ErrorTypeSignature(exp.stype.sinfo, undefined));
        }

        const revalidator = this.relations.resolveStringRegexValidatorInfo(this.ns, exp.stype);
        if(revalidator === undefined) {
            return exp.setType(this.getCStringOfType(exp.stype));
        }

        if(revalidator === undefined) {
            this.reportError(exp.sinfo, `Bad Validator type for CStringOf -- could not resolve to a valid regex`);
            return exp.setType(new ErrorTypeSignature(exp.stype.sinfo, undefined));
        }

        if(!this.relations.isSubtypeOf(exp.stype, this.getWellKnownType("CRegexValidator"), this.constraints)) {
            this.reportError(exp.sinfo, `Bad Validator type for CStringOf -- expected a CRegexValidator`);
            return exp.setType(new ErrorTypeSignature(exp.stype.sinfo, undefined));
        }

        try {
            const vs = validateCStringLiteral(exp.value.slice(1, exp.value.length - 1));
            if(vs === null) {
                this.reportError(exp.sinfo, `Invalid CString literal`);
                return exp.setType(new ErrorTypeSignature(exp.stype.sinfo, undefined));
            }
            else {
                this.runValidatorRegex(exp.sinfo, revalidator, vs, false); 
                exp.resolvedValue = vs;
            }
        } catch(err) {
            this.reportError(exp.sinfo, (err as Error).message);
        }

        return exp.setType(this.getCStringOfType(exp.stype));
    }

    private checkLiteralTemplateStringExpression(env: TypeEnvironment, exp: LiteralTemplateStringExpression): TypeSignature {
        //TODO: validate string encoding is correct and extract template arguments + types
        
        return exp.setType(new StringTemplateTypeSignature(exp.sinfo, "utf8", []));
    }

    private checkLiteralTemplateCStringExpression(env: TypeEnvironment, exp: LiteralTemplateStringExpression): TypeSignature {
        //TODO: validate string encoding is correct and extract template arguments + types
        
        return exp.setType(new StringTemplateTypeSignature(exp.sinfo, "chars", []));
    }

    private checkLiteralPathExpression(env: TypeEnvironment, exp: LiteralPathExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLiteralPathExpression");
    }

    private checkLiteralPathFragmentExpression(env: TypeEnvironment, exp: LiteralPathExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLiteralPathFragmentExpression");
    }

    private checkLiteralPathGlobExpression(env: TypeEnvironment, exp: LiteralPathExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLiteralPathGlobExpression");
    }

    private checkLiteralTypeDeclValueExpression(env: TypeEnvironment, exp: LiteralTypeDeclValueExpression): TypeSignature {
        if(!this.checkTypeSignature(exp.constype)) {
            return exp.setType(exp.constype);
        }

        if(!(exp.constype instanceof NominalTypeSignature) || !(exp.constype.decl instanceof TypedeclTypeDecl)) {
            this.reportError(exp.sinfo, `Invalid type for literal typedecl expression -- ${exp.constype}`);
            return exp.setType(exp.constype);
        }

        const btype = this.relations.getTypeDeclBasePrimitiveType(exp.constype);
        const bvalue = this.checkExpression(env, exp.value, btype !== undefined ? new SimpleTypeInferContext(btype) : undefined);
        this.checkError(exp.sinfo, !(bvalue instanceof ErrorTypeSignature) && btype !== undefined && !this.relations.areSameTypes(bvalue, btype, this.constraints), `Literal value is not the same type (${bvalue.tkeystr}) as the typedecl base type (${btype !== undefined ? btype.tkeystr : "[unset]"})`);

        return exp.setType(exp.constype);
    }

    private checkLiteralTypeDeclIntegralValueExpression(env: TypeEnvironment, exp: LiteralTypeDeclIntegralValueExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLiteralTypeDeclIntegralValueExpression");
    }

    private checkLiteralTypeDeclFloatPointValueExpression(env: TypeEnvironment, exp: LiteralTypeDeclFloatPointValueExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLiteralTypeDeclFloatPointValueExpression");
    }

    private checkInterpolateExpression(env: TypeEnvironment, exp: InterpolateExpression): TypeSignature {
        assert(false, "Not Implemented -- checkInterpolateExpression");
    }

    private checkHasEnvValueExpression(env: TypeEnvironment, exp: AccessEnvValueExpression): TypeSignature {
        assert(false, "Not Implemented -- checkHasEnvValueExpression");
    }
    
    private checkAccessEnvValueExpression(env: TypeEnvironment, exp: AccessEnvValueExpression): TypeSignature {
        assert(false, "Not Implemented -- checkAccessEnvValueExpression");
    }

    private checkTaskAccessInfoExpression(env: TypeEnvironment, exp: TaskAccessInfoExpression): TypeSignature {
        assert(false, "Not Implemented -- checkTaskAccessInfoExpression");
    }
    
    private checkAccessNamespaceConstantExpression(env: TypeEnvironment, exp: AccessNamespaceConstantExpression): TypeSignature {
        const cdecl = this.relations.resolveNamespaceConstant(exp.ns, exp.name);
        if(cdecl === undefined) {
            this.reportError(exp.sinfo, `Could not find namespace constant ${exp.ns}::${exp.name}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        this.checkTypeSignature(cdecl.declaredType);
        return exp.setType(cdecl.declaredType);
    }

    private checkAccessEnumExpression(env: TypeEnvironment, exp: AccessEnumExpression): TypeSignature {
        assert(false, "Not Implemented -- checkAccessEnumExpression");
    }

    private checkAccessStaticFieldExpression(env: TypeEnvironment, exp: AccessStaticFieldExpression): TypeSignature {
        assert(false, "Not Implemented -- checkAccessStaticFieldExpression");
    }

    private checkAccessVariableExpression(env: TypeEnvironment, exp: AccessVariableExpression): TypeSignature {
        const vinfo = env.resolveLocalVarInfoFromSrcName(exp.srcname);
        if(vinfo !== undefined) {
            this.checkError(exp.sinfo, !vinfo.mustDefined, `Variable ${exp.scopename} may not be defined on all control flow paths`);
            return exp.setType(vinfo.vtype);
        }
        else {
            const cinfo = env.resolveLambdaCaptureVarInfoFromSrcName(exp.srcname);
            if(cinfo === undefined) {
                this.reportError(exp.sinfo, `Variable ${exp.scopename} is not declared here`);
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            else {
                exp.isCaptured = true;
                exp.scopename = cinfo.scopename;

                this.checkError(exp.sinfo, !cinfo.mustDefined, `Variable ${exp.scopename} may not be defined on all control flow paths`);
                return exp.setType(cinfo.vtype);
            }
        }
    }

    private checkCollectionConstructor(env: TypeEnvironment, cdecl: AbstractCollectionTypeDecl, exp: ConstructorPrimaryExpression): TypeSignature {
        const etype = this.relations.getExpandoableOfType(exp.ctype) as TypeSignature;

        let shuffleinfo: [number, string, TypeSignature][] = [];
        for(let i = 0; i < exp.args.args.length; ++i) {
            shuffleinfo.push([i, "_", etype]);
            const arg = exp.args.args[i];

            if(arg instanceof PositionalArgumentValue) {
                const argtype = this.checkExpression(env, arg.exp, new SimpleTypeInferContext(etype));
                this.checkError(arg.exp.sinfo, !this.relations.isSubtypeOf(argtype, etype, this.constraints), `Argument ${i} expected type ${etype.tkeystr}`);
            }
            else {
                const argtype = this.checkExpression(env, arg.exp, undefined);
                const argetype = this.relations.getExpandoableOfType(argtype);
                this.checkError(arg.exp.sinfo, argetype === undefined || !this.relations.areSameTypes(argetype, etype, this.constraints), `Rest argument ${i} expected to be container of type ${etype.tkeystr}`);
            }
        }

        if((cdecl instanceof SetTypeDecl) || (cdecl instanceof MapTypeDecl)) {
            exp.hasChecks = true;
        }

        exp.elemtype = etype;
        exp.shuffleinfo = shuffleinfo;
        return exp.setType(exp.ctype);
    }

    private checkSpecialConstructableConstructor(env: TypeEnvironment, cdecl: ConstructableTypeDecl, exp: ConstructorPrimaryExpression): TypeSignature {
        const ctype = exp.ctype as NominalTypeSignature;

        if(cdecl instanceof OkTypeDecl) {
            if(exp.args.args.length !== 1) {
                this.reportError(exp.sinfo, `Ok constructor expects 1 argument`);
            }
            else {
                const oktype = ctype.alltermargs[0];
                exp.shuffleinfo = [[0, "value", oktype]];

                const okarg = this.checkExpression(env, exp.args.args[0].exp, new SimpleTypeInferContext(oktype));
                this.checkError(exp.sinfo, okarg instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(okarg, oktype, this.constraints), `Ok constructor argument is not a subtype of ${oktype.tkeystr}`);
            }
        }
        else if(cdecl instanceof ErrTypeDecl) {
            if(exp.args.args.length !== 1) {
                this.reportError(exp.sinfo, `Err constructor expects 1 argument`);
            }
            else {
                const errtype = ctype.alltermargs[1];
                exp.shuffleinfo = [[0, "value", errtype]];

                const errarg = this.checkExpression(env, exp.args.args[0].exp, new SimpleTypeInferContext(errtype));
                this.checkError(exp.sinfo, errarg instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(errarg, errtype, this.constraints), `Err constructor argument is not a subtype of ${errtype.tkeystr}`);
            }
        }
        else if((cdecl instanceof APIRejectedTypeDecl) || (cdecl instanceof APIFailedTypeDecl) || (cdecl instanceof APIErrorTypeDecl) || (cdecl instanceof APISuccessTypeDecl)) {
            if(exp.args.args.length !== 1) {
                this.reportError(exp.sinfo, `API result constructor expects 1 argument`);
            }
            else {
                const apitype = ctype.alltermargs[0];
                exp.shuffleinfo = [[0, "value", apitype]];

                const apiarg = this.checkExpression(env, exp.args.args[0].exp, new SimpleTypeInferContext(apitype));
                this.checkError(exp.sinfo, apiarg instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(apiarg, apitype, this.constraints), `API result constructor argument is not a subtype of ${apitype.tkeystr}`);
            }
        }
        else if(cdecl instanceof SomeTypeDecl) {
            if(exp.args.args.length !== 1) {
                this.reportError(exp.sinfo, `Some constructor expects 1 argument`);
            }
            else {
                const ttype = ctype.alltermargs[0];
                exp.shuffleinfo = [[0, "value", ttype]];

                const etype = this.checkExpression(env, exp.args.args[0].exp, new SimpleTypeInferContext(ttype));
                this.checkError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Some constructor argument is not a subtype of ${ttype.tkeystr}`);
            }
        }
        else if(cdecl instanceof PairTypeDecl) {
            if(exp.args.args.length !== 2) {
                this.reportError(exp.sinfo, `Pair constructor expects 2 arguments`);
            }
            else {
                const ttype = ctype.alltermargs[0];
                exp.shuffleinfo = [[0, "first", ttype]];
                const etype = this.checkExpression(env, exp.args.args[0].exp, new SimpleTypeInferContext(ttype));
                this.checkError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Pair constructor first argument is not a subtype of ${ttype.tkeystr}`);

                const stype = ctype.alltermargs[1];
                exp.shuffleinfo = [[1, "second", stype]];
                const setype = this.checkExpression(env, exp.args.args[1].exp, new SimpleTypeInferContext(stype));
                this.checkError(exp.sinfo, setype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(setype, stype, this.constraints), `Pair constructor second argument is not a subtype of ${stype.tkeystr}`);
            }
        }
        else if(cdecl instanceof MapEntryTypeDecl) {
            if(exp.args.args.length !== 2) {
                this.reportError(exp.sinfo, `MapEntry constructor expects 2 arguments`);
            }
            else {
                const ktype = ctype.alltermargs[0];
                exp.shuffleinfo = [[0, "key", ktype]];
                const ketype = this.checkExpression(env, exp.args.args[0].exp, new SimpleTypeInferContext(ktype));
                this.checkError(exp.sinfo, ketype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(ketype, ktype, this.constraints), `MapEntry constructor key argument is not a subtype of ${ktype.tkeystr}`);

                const vtype = ctype.alltermargs[1];
                exp.shuffleinfo = [[1, "val", vtype]];
                const vetype = this.checkExpression(env, exp.args.args[1].exp, new SimpleTypeInferContext(vtype));
                this.checkError(exp.sinfo, vetype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(vetype, vtype, this.constraints), `MapEntry constructor value argument is not a subtype of ${vtype.tkeystr}`);
            }
        }
        else {
            assert(false, "Unknown ConstructableTypeDecl type");
        }

        return exp.setType(ctype);
    }

    private checkStandardConstructor(env: TypeEnvironment, fields: MemberFieldDecl[], exp: ConstructorPrimaryExpression): TypeSignature {
        const ctype = exp.ctype as NominalTypeSignature;

        const bnames = this.relations.generateAllFieldBNamesInfoWOptInitializer(ctype, this.constraints, fields);
        const shuffleinfo = this.checkConstructorArgumentList(exp.sinfo, env, exp.args.args, bnames);

        exp.hasChecks = this.relations.hasChecksOnConstructor(ctype, this.constraints);
        exp.shuffleinfo = shuffleinfo;
        return exp.setType(ctype);
    }

    private checkConstructorPrimaryExpression(env: TypeEnvironment, exp: ConstructorPrimaryExpression): TypeSignature {
        this.checkTypeSignature(exp.ctype);

        if(!(exp.ctype instanceof NominalTypeSignature)) {
            this.reportError(exp.sinfo, `Invalid type for constructor expression -- ${exp.ctype}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const ctype = exp.ctype as NominalTypeSignature;
        const decl = ctype.decl;
        if(decl instanceof AbstractCollectionTypeDecl) {
            return this.checkCollectionConstructor(env, decl, exp);
        }
        else if(decl instanceof ConstructableTypeDecl) {
            return this.checkSpecialConstructableConstructor(env, decl, exp);
        }
        else {
            if(decl instanceof EntityTypeDecl) {
                return this.checkStandardConstructor(env, decl.fields, exp);
            }
            else if(decl instanceof DatatypeMemberEntityTypeDecl) {
                return this.checkStandardConstructor(env, decl.fields, exp);
            }
            else {
                this.reportError(exp.sinfo, `Invalid type for constructor expression -- ${exp.ctype}`);
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
        }
    }
    
    private checkConstructorEListExpression(env: TypeEnvironment, exp: ConstructorEListExpression, infertype: TypeSignature | undefined): TypeSignature {
        assert(false, "Not Implemented -- checkConstructorEListExpression");
    }

    private checkConstructorLambdaExpression(env: TypeEnvironment, exp: ConstructorLambdaExpression, infertype: TypeSignature | undefined): TypeSignature {
        assert(false, "Not Implemented -- checkConstructorLambdaExpression");
    }

    private checkLetExpression(env: TypeEnvironment, exp: LetExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLetExpression");
    }

    private checkLambdaInvokeExpression(env: TypeEnvironment, exp: LambdaInvokeExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLambdaInvokeExpression");
    }

    private checkSpecialConstructorExpressionNoInfer(env: TypeEnvironment, exp: SpecialConstructorExpression): TypeSignature {
        const corens = this.relations.assembly.getCoreNamespace();

        const etype = this.checkExpression(env, exp.arg, undefined);
        if((etype instanceof ErrorTypeSignature) || (etype instanceof EListTypeSignature)) {
            this.reportError(exp.sinfo, `Invalid type for special constructor -- got ${etype.tkeystr}`);
            return exp.setType(etype);
        }

        if(exp.rop === "some") {
            return exp.setType(new NominalTypeSignature(exp.sinfo, undefined, corens.typedecls.find((td) => td.name === "Some") as SomeTypeDecl, [etype]));
        }
        else {
            this.reportError(exp.sinfo, "Cannot infer type for special Ok/Err constructor");
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }
    }

    private checkSpecialConstructorExpression(env: TypeEnvironment, exp: SpecialConstructorExpression, infertype: TypeSignature | undefined): TypeSignature {
        if(infertype === undefined || !(infertype instanceof NominalTypeSignature)) {
            return this.checkSpecialConstructorExpressionNoInfer(env, exp);
        }
        else {
            const ninfer = infertype as NominalTypeSignature;
            if(exp.rop === "some") {
                if(ninfer.decl instanceof SomeTypeDecl) {
                    const ttype = ninfer.alltermargs[0];
                    const etype = this.checkExpression(env, exp.arg, ttype);
                    this.checkError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Some constructor argument is not a subtype of ${ttype.tkeystr}`);

                    return exp.setType(ninfer);
                }
                else if(ninfer.decl instanceof OptionTypeDecl) {
                    const ttype = ninfer.alltermargs[0];
                    const etype = this.checkExpression(env, exp.arg, ttype);
                    this.checkError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Some constructor argument is not a subtype of ${ttype.tkeystr}`);

                    return exp.setType(ninfer);
                }
                else {
                    return this.checkSpecialConstructorExpressionNoInfer(env, exp);
                }
            }
            else if(exp.rop === "ok") {
                if(ninfer.decl instanceof OkTypeDecl) {
                    const ttype = ninfer.alltermargs[0];
                    const etype = this.checkExpression(env, exp.arg, ttype);
                    this.checkError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Ok constructor argument is not a subtype of ${ttype.tkeystr}`);

                    return exp.setType(ninfer);
                }
                else if(ninfer.decl instanceof ResultTypeDecl) {
                    const ttype = ninfer.alltermargs[0];
                    const etype = this.checkExpression(env, exp.arg, ttype);
                    this.checkError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Ok constructor argument is not a subtype of ${ttype.tkeystr}`);

                    return exp.setType(ninfer);
                }
                else {
                    this.reportError(exp.sinfo, `Cannot infer type for special Ok constructor -- got ${infertype.tkeystr}`);
                    return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
                }
            }
            else {
                if(ninfer.decl instanceof ErrTypeDecl) {
                    const ttype = ninfer.alltermargs[1];
                    const etype = this.checkExpression(env, exp.arg, ttype);
                    this.checkError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Err constructor argument is not a subtype of ${ttype.tkeystr}`);

                    return exp.setType(ninfer);
                }
                else if(ninfer.decl instanceof ResultTypeDecl) {
                    const ttype = ninfer.alltermargs[1];
                    const etype = this.checkExpression(env, exp.arg, ttype);
                    this.checkError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Err constructor argument is not a subtype of ${ttype.tkeystr}`);

                    return exp.setType(ninfer);
                }
                else {
                    this.reportError(exp.sinfo, `Cannot infer type for special Err constructor -- got ${infertype.tkeystr}`);
                    return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
                }
            }
        }
    }

    private checkSpecialConverterExpression(env: TypeEnvironment, exp: SpecialConverterExpression, infertype: TypeSignature | undefined): TypeSignature {
        assert(false, "Not Implemented -- checkSpecialConverterExpression");
    }

    private checkCallNamespaceFunctionExpression(env: TypeEnvironment, exp: CallNamespaceFunctionExpression): TypeSignature {
        const fdecl = this.relations.resolveNamespaceFunction(exp.ns, exp.name);
        if(fdecl === undefined) {
            this.reportError(exp.sinfo, `Could not find namespace function ${exp.ns}::${exp.name}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const imapper = this.checkTemplateBindingsOnInvoke(env, exp.terms, fdecl); 

        if(imapper !== undefined) {
            const arginfo = this.checkArgumentList(exp.sinfo, env, exp.args.args, fdecl.params, imapper);
            exp.shuffleinfo = arginfo.shuffleinfo;
            exp.restinfo = arginfo.restinfo;
        }

        return exp.setType(fdecl.resultType);
    }

    private checkCallTypeFunctionExpression(env: TypeEnvironment, exp: CallTypeFunctionExpression): TypeSignature {
        assert(false, "Not Implemented -- checkCallTypeFunctionExpression");
    }
    
    private checkLogicActionAndExpression(env: TypeEnvironment, exp: LogicActionAndExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLogicActionAndExpression");
    }

    private checkLogicActionOrExpression(env: TypeEnvironment, exp: LogicActionOrExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLogicActionOrExpression");
    }

    private checkParseAsTypeExpression(env: TypeEnvironment, exp: ParseAsTypeExpression): TypeSignature {
        assert(false, "Not Implemented -- checkParseAsTypeExpression");
    }

    ////////
    // Postfix Expressions
    private checkPostfixAccessFromName(env: TypeEnvironment, exp: PostfixAccessFromName, rcvrtype: TypeSignature): TypeSignature {
        const finfo = this.relations.resolveTypeField(rcvrtype, exp.name, this.constraints);
        if(finfo === undefined) {
            this.reportError(exp.sinfo, `Could not find field ${exp.name} in type ${rcvrtype.tkeystr}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        return exp.setType(finfo.member.declaredType.remapTemplateBindings(finfo.typeinfo.mapping));
    }

    private checkPostfixProjectFromNames(env: TypeEnvironment, exp: PostfixProjectFromNames, rcvrtype: TypeSignature, infertype: TypeInferContext | undefined): TypeSignature {
        assert(false, "Not Implemented -- checkPostfixProjectFromNames");
    }

    private checkPostfixIsTest(env: TypeEnvironment, exp: PostfixIsTest, rcvrtype: TypeSignature): TypeSignature {
        const splits = this.processITestAsBoolean(exp.sinfo, env, rcvrtype, exp.ttest);
        this.checkError(exp.sinfo, !splits.ttrue, "Test is never true");
        this.checkError(exp.sinfo, !splits.tfalse, "Test is never false");

        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkPostfixAsConvert(env: TypeEnvironment, exp: PostfixAsConvert, rcvrtype: TypeSignature): TypeSignature {
        const splits = this.processITestAsConvert(exp.sinfo, env, rcvrtype, exp.ttest);
        this.checkError(exp.sinfo, splits.ttrue === undefined, "Convert always fails");
        //if always true then this is an upcast and OK!

        return exp.setType(splits.ttrue || new ErrorTypeSignature(exp.sinfo, undefined));
    }

    private checkPostfixAssignFields(env: TypeEnvironment, exp: PostfixAssignFields, rcvrtype: TypeSignature): TypeSignature {
        assert(false, "Not Implemented -- checkPostfixAssignFields");
    }

    private checkPostfixInvoke(env: TypeEnvironment, exp: PostfixInvoke, rcvrtype: TypeSignature): TypeSignature {
        assert(false, "Not Implemented -- checkPostfixInvoke");
    }

    private checkPostfixLiteralKeyAccess(env: TypeEnvironment, exp: PostfixLiteralKeyAccess): TypeSignature {
        assert(false, "Not Implemented -- checkPostfixLiteralKeyAccess");
    }

    private checkPostfixOp(env: TypeEnvironment, exp: PostfixOp, typeinfer: TypeInferContext | undefined): TypeSignature {
        let ctype = this.checkExpression(env, exp.rootExp, undefined);
        if(ctype instanceof ErrorTypeSignature) {
            return exp.setType(ctype);
        }

        for(let i = 0; i < exp.ops.length; ++i) {
            const op = exp.ops[i];
            const texpected = (i === exp.ops.length - 1) ? typeinfer : undefined;

            op.setRcvrType(ctype);
            switch(op.tag) {
                case PostfixOpTag.PostfixAccessFromName: {
                    ctype = this.checkPostfixAccessFromName(env, op as PostfixAccessFromName, ctype);
                    break;
                }
                case PostfixOpTag.PostfixProjectFromNames: {
                    ctype = this.checkPostfixProjectFromNames(env, op as PostfixProjectFromNames, ctype, texpected);
                    break;
                }
                case PostfixOpTag.PostfixIsTest: {
                    ctype = this.checkPostfixIsTest(env, op as PostfixIsTest, ctype);
                    break;
                }
                case PostfixOpTag.PostfixAsConvert: {
                    ctype = this.checkPostfixAsConvert(env, op as PostfixAsConvert, ctype);
                    break;
                }
                case PostfixOpTag.PostfixAssignFields: {
                    ctype = this.checkPostfixAssignFields(env, op as PostfixAssignFields, ctype);
                    break;
                }
                case PostfixOpTag.PostfixInvoke: {
                    ctype = this.checkPostfixInvoke(env, op as PostfixInvoke, ctype);
                    break;
                }
                case PostfixOpTag.PostfixLiteralKeyAccess: {
                    ctype = this.checkPostfixLiteralKeyAccess(env, op as PostfixLiteralKeyAccess);
                    break;
                }
                default: {
                    assert(op.tag === PostfixOpTag.PostfixError, "Unknown postfix op");
                    ctype = new ErrorTypeSignature(op.sinfo, undefined);
                    break;
                }
            }
            op.setType(ctype);

            if(ctype instanceof ErrorTypeSignature) {
                return exp.setType(ctype);
            }
        }

        return exp.setType(ctype);
    }

    private checkPrefixNotOpExpression(env: TypeEnvironment, exp: PrefixNotOpExpression): TypeSignature {
        const etype = this.checkExpression(env, exp.exp, undefined);
        if(etype instanceof ErrorTypeSignature) {
            return exp.setType(etype);
        }

        this.checkError(exp.sinfo, !this.isBooleanType(etype), "Prefix Not operator requires a Bool type");
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkPrefixNegateOrPlusOpExpression(env: TypeEnvironment, exp: PrefixNegateOrPlusOpExpression): TypeSignature {
        const etype = this.checkExpression(env, exp.exp, undefined);
        if(etype instanceof ErrorTypeSignature) {
            return exp.setType(etype);
        }

        if(this.checkError(exp.sinfo, !this.relations.isUniqueNumericType(etype, this.constraints), "Prefix Negate/Plus operator requires a unique numeric type")) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        exp.opertype = this.resolveUnderlyingType(etype);
        return exp.setType(etype);
    }

    private resolveUnderlyingType(ttype: TypeSignature): TypeSignature | undefined {
        if(this.relations.isPrimitiveType(ttype)) {
            return ttype;
        }
        else if(this.relations.isTypeDeclType(ttype)) {
            return this.relations.getTypeDeclBasePrimitiveType(ttype);
        }
        else {
            return undefined;
        }
    }

    private checkBinaryNumericArgs(env: TypeEnvironment, lhs: Expression, rhs: Expression): [boolean, TypeSignature, TypeSignature] {
        const tlhs = this.checkExpression(env, lhs, undefined);
        if(tlhs instanceof ErrorTypeSignature) {
            return [false, tlhs, tlhs];
        }

        const trhs = this.checkExpression(env, rhs, undefined);
        if(trhs instanceof ErrorTypeSignature) {
            return [false, tlhs, trhs];
        }

        if(this.checkError(lhs.sinfo, !this.relations.isUniqueNumericType(tlhs, this.constraints), "Binary operator requires a unique numeric type")) {
            return [false, tlhs, trhs];
        }
        if(this.checkError(rhs.sinfo, !this.relations.isUniqueNumericType(trhs, this.constraints), "Binary operator requires a unique numeric type")) {
            return [false, tlhs, trhs];
        }

        return [true, tlhs, trhs];
    }

    private checkBinAddExpression(env: TypeEnvironment, exp: BinAddExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }
        
        if(this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Addition operator requires 2 arguments of the same type")) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        exp.opertype = this.resolveUnderlyingType(tlhs);
        return exp.setType(tlhs);
    }

    private checkBinSubExpression(env: TypeEnvironment, exp: BinSubExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        if(this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Subtraction operator requires 2 arguments of the same type")) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        exp.opertype = this.resolveUnderlyingType(tlhs);
        return exp.setType(tlhs);
    }

    private checkBinMultExpression(env: TypeEnvironment, exp: BinMultExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        let res: TypeSignature;
        if(this.relations.isPrimitiveType(tlhs) && this.relations.isPrimitiveType(trhs)) {
            if(this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Multiplication operator requires 2 arguments of the same type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            res = tlhs;
        }
        else if(this.relations.isTypeDeclType(tlhs) && this.relations.isPrimitiveType(trhs)) {
            const baselhs = this.relations.getTypeDeclBasePrimitiveType(tlhs);
            if(this.checkError(exp.sinfo, baselhs === undefined || !this.relations.areSameTypes(baselhs, trhs, this.constraints), "Multiplication operator requires a unit-less argument that matches underlying unit type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            res = tlhs
        }
        else if(this.relations.isPrimitiveType(tlhs) && this.relations.isTypeDeclType(trhs)) {
            const baserhs = this.relations.getTypeDeclBasePrimitiveType(trhs);
            if(this.checkError(exp.sinfo, baserhs === undefined || !this.relations.areSameTypes(tlhs, baserhs, this.constraints), "Multiplication operator requires a unit-less argument that matches underlying unit type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            res = trhs;
        }
        else {
            this.checkError(exp.sinfo, false, "Multiplication operator not allowed on 2 unit typed values");
            res = new ErrorTypeSignature(exp.sinfo, undefined);
        }

        exp.opertype = this.resolveUnderlyingType(res);
        return exp.setType(res);
    }

    private checkBinDivExpression(env: TypeEnvironment, exp: BinDivExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        let res: TypeSignature;
        if(this.relations.isPrimitiveType(tlhs) && this.relations.isPrimitiveType(trhs)) {
            if(this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Division operator requires 2 arguments of the same type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            res = tlhs;
        }
        else if(this.relations.isTypeDeclType(tlhs) && this.relations.isPrimitiveType(trhs)) {
            const baselhs = this.relations.getTypeDeclBasePrimitiveType(tlhs);
            if(this.checkError(exp.sinfo, baselhs === undefined || !this.relations.areSameTypes(baselhs, trhs, this.constraints), "Division operator requires a unit-less divisor argument that matches the underlying unit type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            res = tlhs
        }
        else if(this.relations.isTypeDeclType(tlhs) && this.relations.isTypeDeclType(trhs)) {
            if(this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Division operator requires 2 arguments of the same type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            const basetype = this.relations.getTypeDeclBasePrimitiveType(trhs);
            if(this.checkError(exp.sinfo, basetype === undefined, "Division operator requires matching types on the arguments")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            res = basetype as TypeSignature;
        }
        else {
            this.checkError(exp.sinfo, false, "Division operator not allowed on with unit typed divisor and a type-less value");
            res = new ErrorTypeSignature(exp.sinfo, undefined);
        }

        exp.opertype = this.resolveUnderlyingType(res);
        return exp.setType(res);
    }

    private checkBinKeyEqExpression(env: TypeEnvironment, exp: BinKeyEqExpression): TypeSignature {
        const lhstype = this.checkExpression(env, exp.lhs, undefined);
        const rhstype = this.checkExpression(env, exp.rhs, undefined);

        if (lhstype instanceof ErrorTypeSignature || rhstype instanceof ErrorTypeSignature) {
            return exp.setType(this.getWellKnownType("Bool"));
        }
        
        if (!this.relations.isSubtypeOf(lhstype, rhstype, this.constraints) && !this.relations.isSubtypeOf(rhstype, lhstype, this.constraints)) {
            this.reportError(exp.sinfo, `Types ${lhstype.tkeystr} and ${rhstype.tkeystr} are not comparable -- one must be subtype of the other`);
            return exp.setType(this.getWellKnownType("Bool"));
        }

        const action = this.checkValueEq(exp.lhs, lhstype, exp.rhs, rhstype);
        if (action === "err") {
            this.reportError(exp.sinfo, `Types ${lhstype.tkeystr} and ${rhstype.tkeystr} are not comparable`);
        }
        
        exp.operkind = action;
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkBinKeyNeqExpression(env: TypeEnvironment, exp: BinKeyNeqExpression): TypeSignature {
        const lhstype = this.checkExpression(env, exp.lhs, undefined);
        const rhstype = this.checkExpression(env, exp.rhs, undefined);

        if (lhstype instanceof ErrorTypeSignature || rhstype instanceof ErrorTypeSignature) {
            return exp.setType(this.getWellKnownType("Bool"));
        }
        
        if (!this.relations.isSubtypeOf(lhstype, rhstype, this.constraints) && !this.relations.isSubtypeOf(rhstype, lhstype, this.constraints)) {
            this.reportError(exp.sinfo, `Types ${lhstype.tkeystr} and ${rhstype.tkeystr} are not comparable -- one must be subtype of the other`);
            return exp.setType(this.getWellKnownType("Bool"));
        }

        const action = this.checkValueEq(exp.lhs, lhstype, exp.rhs, rhstype);
        if (action === "err") {
            this.reportError(exp.sinfo, `Types ${lhstype.tkeystr} and ${rhstype.tkeystr} are not comparable`);
        }

        exp.operkind = action;
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkNumericEqExpression(env: TypeEnvironment, exp: NumericEqExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Operator == requires 2 arguments of the same type");
        
        exp.opertype = this.resolveUnderlyingType(tlhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkNumericNeqExpression(env: TypeEnvironment, exp: NumericNeqExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Operator != requires 2 arguments of the same type");
        
        exp.opertype = this.resolveUnderlyingType(tlhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkNumericLessExpression(env: TypeEnvironment, exp: NumericLessExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Operator < requires 2 arguments of the same type");
        
        exp.opertype = this.resolveUnderlyingType(tlhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkNumericLessEqExpression(env: TypeEnvironment, exp: NumericLessEqExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Operator <= requires 2 arguments of the same type");
        
        exp.opertype = this.resolveUnderlyingType(tlhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkNumericGreaterExpression(env: TypeEnvironment, exp: NumericGreaterExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Operator > requires 2 arguments of the same type");
        
        exp.opertype = this.resolveUnderlyingType(tlhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkNumericGreaterEqExpression(env: TypeEnvironment, exp: NumericGreaterEqExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Operator >= requires 2 arguments of the same type");
        
        exp.opertype = this.resolveUnderlyingType(tlhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkBinaryBooleanArgs(env: TypeEnvironment, lhs: Expression, rhs: Expression) {
        const tlhs = this.checkExpression(env, lhs, undefined);
        if(tlhs instanceof ErrorTypeSignature) {
            return;
        }

        const trhs = this.checkExpression(env, rhs, undefined);
        if(trhs instanceof ErrorTypeSignature) {
            return;
        }

        if(this.checkError(lhs.sinfo, !this.isBooleanType(tlhs), "Binary operator requires a Bool type")) {
            return;
        }
        if(this.checkError(rhs.sinfo, !this.isBooleanType(trhs), "Binary operator requires a Bool type")) {
            return;
        }

        return;
    }

    private checkBinLogicAndExpression(env: TypeEnvironment, exp: BinLogicAndExpression): TypeSignature {
        this.checkBinaryBooleanArgs(env, exp.lhs, exp.rhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkBinLogicOrExpression(env: TypeEnvironment, exp: BinLogicOrExpression): TypeSignature {
        this.checkBinaryBooleanArgs(env, exp.lhs, exp.rhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkBinLogicImpliesExpression(env: TypeEnvironment, exp: BinLogicImpliesExpression): TypeSignature {
        this.checkBinaryBooleanArgs(env, exp.lhs, exp.rhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkBinLogicIFFExpression(env: TypeEnvironment, exp: BinLogicIFFExpression): TypeSignature {
        this.checkBinaryBooleanArgs(env, exp.lhs, exp.rhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkMapEntryConstructorExpression(env: TypeEnvironment, exp: MapEntryConstructorExpression, infertype: TypeSignature | undefined): TypeSignature {
        assert(false, "Not Implemented -- checkMapEntryConstructorExpression");
    }

    private checkIfExpression(env: TypeEnvironment, exp: IfExpression, typeinfer: TypeInferContext | undefined): TypeSignature {
        let eetype = this.checkExpression(env, exp.test.exp, undefined);

        let ttrue: TypeSignature;
        let tfalse: TypeSignature;

        if(exp.test.itestopt === undefined) {
            if(eetype instanceof ErrorTypeSignature) {
                eetype = this.getWellKnownType("Bool");
            }

            this.checkError(exp.sinfo, !this.isBooleanType(eetype), "If test requires a Bool type");
            this.checkError(exp.sinfo, exp.binder !== undefined, "Binder is not valid here -- requires use of an ITest");

            ttrue = this.checkExpression(env, exp.trueValue, typeinfer);
            tfalse = this.checkExpression(env, exp.falseValue, typeinfer);
        }
        else {
            const splits = this.processITestAsConvert(exp.sinfo, env, eetype, exp.test.itestopt);
            this.checkError(exp.sinfo, splits.ttrue === undefined, "Test is never true -- true branch of if is unreachable");
            this.checkError(exp.sinfo, splits.tfalse === undefined, "Test is never false -- false branch of if is unreachable");

            if(exp.binder === undefined) {
                ttrue = this.checkExpression(env, exp.trueValue, typeinfer);
                tfalse = this.checkExpression(env, exp.falseValue, typeinfer);
            }
            else {
                exp.binder.scopename = env.getBindScopeName(exp.binder.srcname);

                const tenv = env.addBinder(exp.binder.srcname, exp.binder.scopename, splits.ttrue || eetype, true, true);
                ttrue = this.checkExpression(tenv, exp.trueValue, typeinfer);

                const fenv = env.addBinder(exp.binder.srcname, exp.binder.scopename, splits.tfalse || eetype, true, true);
                tfalse = this.checkExpression(fenv, exp.falseValue, typeinfer);
            }
        }
        
        if(ttrue instanceof ErrorTypeSignature || tfalse instanceof ErrorTypeSignature) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }
        else {
            const jtype = this.relations.flowTypeLUB(exp.sinfo, TypeInferContext.asSimpleType(typeinfer), [ttrue, tfalse], this.constraints);
            return exp.setType(jtype);
        }
    }

    ////////
    //statement expressions
    private checkExpression(env: TypeEnvironment, exp: Expression, typeinfer: TypeInferContext | undefined): TypeSignature {
        switch (exp.tag) {
            case ExpressionTag.LiteralNoneExpression: {
                return this.checkLiteralNoneExpression(env, exp as LiteralNoneExpression);
            }
            case ExpressionTag.LiteralBoolExpression: {
                return this.checkLiteralBoolExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralNatExpression: {
                return this.checkLiteralNatExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralIntExpression: {
                return this.checkLiteralIntExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralBigNatExpression: {
                return this.checkLiteralBigNatExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralBigIntExpression: {
                return this.checkLiteralBigIntExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralRationalExpression: {
                return this.checkLiteralRationalExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralFloatExpression: {
                return this.checkLiteralFloatExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDecimalExpression: {
                return this.checkLiteralDecimalExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDecimalDegreeExpression: {
                return this.checkLiteralDecimalDegreeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralLatLongCoordinateExpression: {
                return this.checkLiteralLatLongCoordinateExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralComplexNumberExpression: {
                return this.checkLiteralComplexNumberExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralByteBufferExpression: {
                return this.checkLiteralByteBufferExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUUIDv4Expression: {
                return this.checkLiteralUUIDv4Expression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUUIDv7Expression: {
                return this.checkLiteralUUIDv7Expression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralSHAContentHashExpression: {
                return this.checkLiteralSHAContentHashExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDateTimeExpression: {
                return this.checkLiteralDateTimeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUTCDateTimeExpression: {
                return this.checkLiteralUTCDateTimeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralPlainDateExpression: {
                return this.checkLiteralPlainDateExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralPlainTimeExpression: {
                return this.checkLiteralPlainTimeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralLogicalTimeExpression: {
                return this.checkLiteralLogicalTimeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralTickTimeExpression: {
                return this.checkLiteralTickTimeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralISOTimeStampExpression: {
                return this.checkLiteralISOTimeStampExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaDateTimeExpression: {
                return this.checkLiteralDeltaDateTimeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaPlainDateExpression: {
                return this.checkLiteralDeltaPlainDateExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaPlainTimeExpression: {
                return this.checkLiteralDeltaPlainTimeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaISOTimeStampExpression: {
                return this.checkLiteralDeltaISOTimeStampExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaSecondsExpression: {
                return this.checkLiteralDeltaSecondsExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaTickExpression: {
                return this.checkLiteralDeltaTickExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaLogicalExpression: {
                return this.checkLiteralDeltaLogicalExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUnicodeRegexExpression: {
                return this.checkLiteralUnicodeRegexExpression(env, exp as LiteralRegexExpression);
            }
            case ExpressionTag.LiteralCRegexExpression: {
                return this.checkLiteralCRegexExpression(env, exp as LiteralRegexExpression);
            }
            case ExpressionTag.LiteralStringExpression: {
                return this.checkLiteralStringExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralCStringExpression: {
                return this.checkLiteralCStringExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralTypedStringExpression: {
                return this.checkLiteralTypedStringExpression(env, exp as LiteralTypedStringExpression);
            }
            case ExpressionTag.LiteralTypedCStringExpression: {
                return this.checkLiteralTypedCStringExpression(env, exp as LiteralTypedStringExpression);
            }
            case ExpressionTag.LiteralTemplateStringExpression: {
                return this.checkLiteralTemplateStringExpression(env, exp as LiteralTemplateStringExpression);
            }
            case ExpressionTag.LiteralTemplateCStringExpression: {
                return this.checkLiteralTemplateCStringExpression(env, exp as LiteralTemplateStringExpression);
            }
            case ExpressionTag.LiteralPathExpression: {
                return this.checkLiteralPathExpression(env, exp as LiteralPathExpression);
            }
            case ExpressionTag.LiteralPathFragmentExpression: {
                return this.checkLiteralPathFragmentExpression(env, exp as LiteralPathExpression);
            }
            case ExpressionTag.LiteralPathGlobExpression: {
                return this.checkLiteralPathGlobExpression(env, exp as LiteralPathExpression);
            }
            case ExpressionTag.LiteralTypeDeclValueExpression: {
                return this.checkLiteralTypeDeclValueExpression(env, exp as LiteralTypeDeclValueExpression);
            }
            case ExpressionTag.LiteralTypeDeclIntegralValueExpression: {
                return this.checkLiteralTypeDeclIntegralValueExpression(env, exp as LiteralTypeDeclIntegralValueExpression);
            }
            case ExpressionTag.LiteralTypeDeclFloatPointValueExpression: {
                return this.checkLiteralTypeDeclFloatPointValueExpression(env, exp as LiteralTypeDeclFloatPointValueExpression);
            }
            case ExpressionTag.InterpolateExpression: {
                return this.checkInterpolateExpression(env, exp as InterpolateExpression);
            }
            case ExpressionTag.HasEnvValueExpression: {
                return this.checkHasEnvValueExpression(env, exp as AccessEnvValueExpression);
            }
            case ExpressionTag.AccessEnvValueExpression: {
                return this.checkAccessEnvValueExpression(env, exp as AccessEnvValueExpression);
            }
            case ExpressionTag.TaskAccessInfoExpression: {
                return this.checkTaskAccessInfoExpression(env, exp as TaskAccessInfoExpression);
            }
            case ExpressionTag.AccessNamespaceConstantExpression: {
                return this.checkAccessNamespaceConstantExpression(env, exp as AccessNamespaceConstantExpression);
            }
            case ExpressionTag.AccessEnumExpression: {
                return this.checkAccessEnumExpression(env, exp as AccessEnumExpression);
            }
            case ExpressionTag.AccessStaticFieldExpression: {
                return this.checkAccessStaticFieldExpression(env, exp as AccessStaticFieldExpression);
            }
            case ExpressionTag.AccessVariableExpression: {
                return this.checkAccessVariableExpression(env, exp as AccessVariableExpression);
            }
            case ExpressionTag.ConstructorPrimaryExpression: {
                return this.checkConstructorPrimaryExpression(env, exp as ConstructorPrimaryExpression);
            }
            case ExpressionTag.ConstructorEListExpression: {
                return this.checkConstructorEListExpression(env, exp as ConstructorEListExpression, TypeInferContext.asSimpleType(typeinfer));
            }
            case ExpressionTag.ConstructorLambdaExpression: {
                return this.checkConstructorLambdaExpression(env, exp as ConstructorLambdaExpression, TypeInferContext.asSimpleType(typeinfer));
            }
            case ExpressionTag.LetExpression: {
                return this.checkLetExpression(env, exp as LetExpression);
            }
            case ExpressionTag.LambdaInvokeExpression: {
                return this.checkLambdaInvokeExpression(env, exp as LambdaInvokeExpression);
            }
            case ExpressionTag.SpecialConstructorExpression: {
                return this.checkSpecialConstructorExpression(env, exp as SpecialConstructorExpression, TypeInferContext.asSimpleType(typeinfer));
            }
            case ExpressionTag.SpecialConverterExpression: {
                return this.checkSpecialConverterExpression(env, exp as SpecialConverterExpression, TypeInferContext.asSimpleType(typeinfer));
            }
            case ExpressionTag.CallNamespaceFunctionExpression: {
                return this.checkCallNamespaceFunctionExpression(env, exp as CallNamespaceFunctionExpression);
            }
            case ExpressionTag.CallTypeFunctionExpression: {
                return this.checkCallTypeFunctionExpression(env, exp as CallTypeFunctionExpression);
            }
            case ExpressionTag.LogicActionAndExpression: {
                return this.checkLogicActionAndExpression(env, exp as LogicActionAndExpression);
            }
            case ExpressionTag.LogicActionOrExpression: {
                return this.checkLogicActionOrExpression(env, exp as LogicActionOrExpression);
            }
            case ExpressionTag.ParseAsTypeExpression: {
                return this.checkParseAsTypeExpression(env, exp as ParseAsTypeExpression);
            }
            case ExpressionTag.PostfixOpExpression: {
                return this.checkPostfixOp(env, exp as PostfixOp, typeinfer);
            }
            case ExpressionTag.PrefixNotOpExpression: {
                return this.checkPrefixNotOpExpression(env, exp as PrefixNotOpExpression);
            }
            case ExpressionTag.PrefixNegateOrPlusOpExpression: {
                return this.checkPrefixNegateOrPlusOpExpression(env, exp as PrefixNegateOrPlusOpExpression);
            }
            case ExpressionTag.BinAddExpression: {
                return this.checkBinAddExpression(env, exp as BinAddExpression);
            }
            case ExpressionTag.BinSubExpression: {
                return this.checkBinSubExpression(env, exp as BinSubExpression);
            }
            case ExpressionTag.BinMultExpression: {
                return this.checkBinMultExpression(env, exp as BinMultExpression);
            }
            case ExpressionTag.BinDivExpression: {
                return this.checkBinDivExpression(env, exp as BinDivExpression);
            }
            case ExpressionTag.BinKeyEqExpression: {
                return this.checkBinKeyEqExpression(env, exp as BinKeyEqExpression);
            }
            case ExpressionTag.BinKeyNeqExpression: {
                return this.checkBinKeyNeqExpression(env, exp as BinKeyNeqExpression);
            }
            case ExpressionTag.NumericEqExpression: {
                return this.checkNumericEqExpression(env, exp as NumericEqExpression);
            }
            case ExpressionTag.NumericNeqExpression: {
                return this.checkNumericNeqExpression(env, exp as NumericNeqExpression);
            }
            case ExpressionTag.NumericLessExpression: {
                return this.checkNumericLessExpression(env, exp as NumericLessExpression);
            }
            case ExpressionTag.NumericLessEqExpression: {
                return this.checkNumericLessEqExpression(env, exp as NumericLessEqExpression);
            }
            case ExpressionTag.NumericGreaterExpression: {
                return this.checkNumericGreaterExpression(env, exp as NumericGreaterExpression);
            }
            case ExpressionTag.NumericGreaterEqExpression: {
                return this.checkNumericGreaterEqExpression(env, exp as NumericGreaterEqExpression);
            }
            case ExpressionTag.BinLogicAndExpression: {
                return this.checkBinLogicAndExpression(env, exp as BinLogicAndExpression);
            }
            case ExpressionTag.BinLogicOrExpression: {
                return this.checkBinLogicOrExpression(env, exp as BinLogicOrExpression);
            }
            case ExpressionTag.BinLogicImpliesExpression: {
                return this.checkBinLogicImpliesExpression(env, exp as BinLogicImpliesExpression);
            }
            case ExpressionTag.BinLogicIFFExpression: {
                return this.checkBinLogicIFFExpression(env, exp as BinLogicIFFExpression);
            }
            case ExpressionTag.MapEntryConstructorExpression: {
                return this.checkMapEntryConstructorExpression(env, exp as MapEntryConstructorExpression, TypeInferContext.asSimpleType(typeinfer));
            }
            case ExpressionTag.IfExpression: {
                return this.checkIfExpression(env, exp as IfExpression, typeinfer);
            }
            default: {
                assert(exp.tag === ExpressionTag.ErrorExpression, "Unknown expression kind");
                return new ErrorTypeSignature(exp.sinfo, undefined);
            }
        }
    }

    private checkCallRefThisExpression(env: TypeEnvironment, exp: CallRefThisExpression): TypeSignature {
        assert(false, "Not Implemented -- checkCallRefThisExpression");
    }

    private checkCallRefSelfExpression(env: TypeEnvironment, exp: CallRefSelfExpression): TypeSignature {
        assert(false, "Not Implemented -- checkCallRefSelfExpression");
    }

    private checkCallTaskActionExpression(env: TypeEnvironment, exp: CallTaskActionExpression): TypeSignature {
        assert(false, "Not Implemented -- checkCallTaskActionExpression");
    }

    private checkTaskRunExpression(env: TypeEnvironment, exp: TaskRunExpression): TypeSignature {
        assert(false, "Not Implemented -- checkTaskRunExpression");
    }

    private checkTaskMultiExpression(env: TypeEnvironment, exp: TaskMultiExpression): TypeSignature {
        assert(false, "Not Implemented -- checkTaskMultiExpression");
    }

    private checkTaskDashExpression(env: TypeEnvironment, exp: TaskDashExpression): TypeSignature {
        assert(false, "Not Implemented -- checkTaskDashExpression");
    }

    private checkTaskAllExpression(env: TypeEnvironment, exp: TaskAllExpression): TypeSignature {
        assert(false, "Not Implemented -- checkTaskAllExpression");
    }

    private checkTaskRaceExpression(env: TypeEnvironment, exp: TaskRaceExpression): TypeSignature {
        assert(false, "Not Implemented -- checkTaskRaceExpression");
    }

    private checkExpressionRHS(env: TypeEnvironment, exp: Expression, typeinfer: TypeInferContext | undefined): TypeSignature {
        const ttag = exp.tag;
        switch (ttag) {
            case ExpressionTag.CallRefThisExpression: {
                return this.checkCallRefThisExpression(env, exp as CallRefThisExpression);
            }
            case ExpressionTag.CallRefSelfExpression: {
                return this.checkCallRefSelfExpression(env, exp as CallRefSelfExpression);
            }
            case ExpressionTag.CallTaskActionExpression: {
                return this.checkCallTaskActionExpression(env, exp as CallTaskActionExpression);
            }
            case ExpressionTag.TaskRunExpression: {
                return this.checkTaskRunExpression(env, exp as TaskRunExpression);
            }
            case ExpressionTag.TaskMultiExpression: {
                return this.checkTaskMultiExpression(env, exp as TaskMultiExpression);
            }
            case ExpressionTag.TaskDashExpression: {
                return this.checkTaskDashExpression(env, exp as TaskDashExpression);
            }
            case ExpressionTag.TaskAllExpression: {
                return this.checkTaskAllExpression(env, exp as TaskAllExpression);
            }
            case ExpressionTag.TaskRaceExpression: {
                return this.checkTaskRaceExpression(env, exp as TaskRaceExpression);
            }
            default: {
                return this.checkExpression(env, exp, typeinfer);
            }
        }
    }

    /*
    private checkLiteralTypedPrimitiveConstructorExpression(env: ExpressionTypeEnvironment, exp: LiteralTypedPrimitiveConstructorExpression): ExpressionTypeEnvironment {
        const constype = this.normalizeTypeOnly(exp.constype, env.binds);
        const lexp = this.reduceLiteralValueToCanonicalForm(exp.value, env.binds);
        this.raiseErrorIf(exp.sinfo, lexp === undefined, "Not a literal expression");

        this.raiseErrorIf(exp.sinfo, !(constype.tryGetUniqueEntityTypeInfo() instanceof ResolvedTypedeclEntityAtomType), `${constype.typeID} is not a typedecl type`)
        const ccdecl = constype.tryGetUniqueEntityTypeInfo() as ResolvedTypedeclEntityAtomType;

        this.raiseErrorIf(exp.sinfo, ccdecl.representation.typeID !== lexp[1].typeID, `Expected type of ${ccdecl.representation.typeID} (representation type) but got ${lexp[1].typeID}`);

        const tirtypdeclkey = this.toTIRTypeKey(constype);
        const tirtypedecl = this.m_tirTypeMap.get(tirtypdeclkey) as TIRTypedeclEntityType;

        if (tirtypedecl.strvalidator !== undefined) {
            const litval = (lexp[0] as TIRLiteralValue).exp;
            let accepts = false;
            if (litval instanceof TIRLiteralStringExpression) {
                accepts = tirtypedecl.strvalidator.vre.acceptsString(extractLiteralStringValue(litval.expstr, true), this.m_assembly.m_literalRegexs);
            }
            else {
                accepts = tirtypedecl.strvalidator.vre.acceptsString(extractLiteralASCIIStringValue(litval.expstr, true), this.m_assembly.m_literalRegexs);
            }
            this.raiseErrorIf(exp.sinfo, !accepts, "literal string does not satisfy validator constraint");
        }

        if (tirtypedecl.pthvalidator !== undefined) {
            const litval = (lexp[0] as TIRLiteralValue).exp;
            let accepts = false;
            if (tirtypedecl.pthvalidator.kind === "path") {
                accepts = tirtypedecl.pthvalidator.vpth.acceptsPath(extractLiteralStringValue(litval.expstr, true));
            }
            else if (tirtypedecl.pthvalidator.kind === "pathfragment") {
                accepts = tirtypedecl.pthvalidator.vpth.acceptsPathFragment(extractLiteralStringValue(litval.expstr, true));
            }
            else {
                accepts = tirtypedecl.pthvalidator.vpth.acceptsPathGlob(extractLiteralASCIIStringValue(litval.expstr, true));
            }
            this.raiseErrorIf(exp.sinfo, !accepts, "literal string does not satisfy path validator constraint");
        }

        if (!this.typedeclTypeConstructorHasInvariants(constype, ccdecl.object)) {
            const nexp = new TIRLiteralTypedPrimitiveDirectExpression(exp.sinfo, (lexp[0] as TIRLiteralValue).exp, this.toTIRTypeKey(constype), this.toTIRTypeKey(ResolvedType.createSingle(ccdecl.representation)));
            return env.setResultExpressionInfo(nexp, constype);
        }
        else {
            const nexp = new TIRLiteralTypedPrimitiveConstructorExpression(exp.sinfo, (lexp[0] as TIRLiteralValue).exp, this.toTIRTypeKey(constype), this.toTIRTypeKey(ResolvedType.createSingle(ccdecl.representation)));
            return env.setResultExpressionInfo(nexp, constype);
        }
    }

    private checkAccessEnvValue(env: ExpressionTypeEnvironment, exp: AccessEnvValueExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk !== "write", `Can only access "environment" variables in task actions`);

        const valtype = this.normalizeTypeOnly(exp.valtype, env.binds);
        const restype = this.normalizeTypeOnly(new UnionTypeSignature(exp.sinfo, [exp.valtype, new NominalTypeSignature(exp.sinfo, "Core", ["None"])]), env.binds);

        return env.setResultExpressionInfo(new TIRAccessEnvValueExpression(exp.sinfo, exp.keyname, this.toTIRTypeKey(valtype), this.toTIRTypeKey(restype), exp.orNoneMode), restype);
    }

    private checkAccessStaticField(env: ExpressionTypeEnvironment, exp: AccessStaticFieldExpression): ExpressionTypeEnvironment {
        const oftype = this.normalizeTypeOnly(exp.stype, env.binds);
        const cmf = this.resolveMemberConst(exp.sinfo, oftype, exp.name);
        this.raiseErrorIf(exp.sinfo, cmf === undefined, `const ${exp.name} not defined on type ${oftype.typeID}`);

        const cdecl = (cmf as OOMemberLookupInfo<StaticMemberDecl>);
        this.raiseErrorIf(exp.sinfo, (cdecl.decl.value as ConstantExpressionValue).captured.size !== 0, "Expression uses unbound variables");

        const tirdecltype = this.toTIRTypeKey(cdecl.ttype);
        const rtype = this.normalizeTypeOnly(cdecl.decl.declaredType, TemplateBindScope.createBaseBindScope(cdecl.oobinds));
        
        if (cdecl.ootype.attributes.includes("__enum_type")) {
            this.m_pendingConstMemberDecls.push(cdecl);
            return env.setResultExpressionInfo(new TIRAccessConstMemberFieldExpression(exp.sinfo, tirdecltype, exp.name, this.toTIRTypeKey(rtype)), rtype);
        }
        else {
            const cexp = this.compileTimeReduceConstantExpression((cdecl.decl.value as ConstantExpressionValue).exp, env.binds);

            if (cexp !== undefined) {
                return this.emitCoerceIfNeeded(this.checkExpression(env, cexp, rtype), exp.sinfo, rtype);
            }
            else {
                this.m_pendingConstMemberDecls.push(cdecl);
                return env.setResultExpressionInfo(new TIRAccessConstMemberFieldExpression(exp.sinfo, tirdecltype, exp.name, this.toTIRTypeKey(rtype)), rtype);
            }
        }
    }

    private checkConstructorPrimary(env: ExpressionTypeEnvironment, exp: ConstructorPrimaryExpression): ExpressionTypeEnvironment {
        const oftype = this.normalizeTypeOnly(exp.ctype, env.binds).tryGetUniqueEntityTypeInfo();
        this.raiseErrorIf(exp.sinfo, oftype === undefined, "Invalid constructor type");

        if(oftype instanceof ResolvedObjectEntityAtomType) {
            const roftype = ResolvedType.createSingle(oftype);
            const tiroftype = this.toTIRTypeKey(roftype);

            const allf = [...this.getAllOOFields(roftype, oftype.object, oftype.binds)];
            this.raiseErrorIf(exp.sinfo, allf.length !== exp.args.length, `got ${exp.args.length} args for constructor but expected ${allf.length}`);
            const eargs = exp.args.map((arg, i) => {
                const itype = this.normalizeTypeOnly(allf[i][1][2].declaredType, TemplateBindScope.createBaseBindScope(allf[i][1][3]));
                const ee = this.checkExpression(env, arg, itype);

                return this.emitCoerceIfNeeded(ee, exp.sinfo, itype);
            });

            if(!this.entityTypeConstructorHasInvariants(roftype, oftype.object, oftype.binds)) {
                const econs = new TIRConstructorPrimaryDirectExpression(exp.sinfo, tiroftype, eargs.map((earg) => earg.expressionResult));
                return env.setResultExpressionInfo(econs, roftype);
            }
            else {
                const econs = new TIRConstructorPrimaryCheckExpression(exp.sinfo, tiroftype, eargs.map((earg) => earg.expressionResult));
                return env.setResultExpressionInfo(econs, roftype);
            }
        }
        else if(oftype instanceof ResolvedTypedeclEntityAtomType) {
            const roftype = ResolvedType.createSingle(oftype);

            this.raiseErrorIf(exp.sinfo, exp.args.length !== 1, `${oftype.typeID} constructor expects a single arg`);
            const cexp = this.checkExpression(env, exp.args[0], ResolvedType.createSingle(oftype.valuetype));
            const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, ResolvedType.createSingle(oftype.valuetype));

            if (!this.typedeclTypeConstructorFromValueHasInvariants(roftype, oftype.object)) {
                const nexp = new TIRTypedeclDirectExpression(exp.sinfo, this.toTIRTypeKey(roftype), ecast.expressionResult);
                return env.setResultExpressionInfo(nexp, roftype);
            }
            else {
                const nexp = new TIRTypedeclConstructorExpression(exp.sinfo, this.toTIRTypeKey(roftype), ecast.expressionResult);
                return env.setResultExpressionInfo(nexp, roftype);
            }
        }
        else if(oftype instanceof ResolvedConstructableEntityAtomType) {
            const roftype = ResolvedType.createSingle(oftype);
            const tiroftype = this.toTIRTypeKey(roftype);

            if(oftype instanceof ResolvedOkEntityAtomType) {
                this.raiseErrorIf(exp.sinfo, exp.args.length !== 1, "Result<T, E>::Ok constructor expects a single arg of type T");
                const cexp = this.checkExpression(env, exp.args[0], oftype.typeT);
                const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, oftype.typeT);

                return env.setResultExpressionInfo(new TIRResultOkConstructorExpression(exp.sinfo, tiroftype, ecast.expressionResult), roftype);
            }
            else if(oftype instanceof ResolvedErrEntityAtomType) {
                this.raiseErrorIf(exp.sinfo, exp.args.length !== 1, "Result<T, E>::Ok constructor expects a single arg of type E");
                const cexp = this.checkExpression(env, exp.args[0], oftype.typeE);
                const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, oftype.typeE);

                return env.setResultExpressionInfo(new TIRResultErrConstructorExpression(exp.sinfo, tiroftype, ecast.expressionResult), roftype);
            }
            else if(oftype instanceof ResolvedSomethingEntityAtomType) {
                this.raiseErrorIf(exp.sinfo, exp.args.length !== 1, "Something<T> constructor expects a single arg of type T");
                const cexp = this.checkExpression(env, exp.args[0], oftype.typeT);
                const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, oftype.typeT);

                return env.setResultExpressionInfo(new TIRSomethingConstructorExpression(exp.sinfo, tiroftype, ecast.expressionResult), roftype);
            }
            else if(oftype instanceof ResolvedMapEntryEntityAtomType) {
                const tirktype = this.toTIRTypeKey(oftype.typeK);
                const tirvtype = this.toTIRTypeKey(oftype.typeV);

                this.raiseErrorIf(exp.sinfo, exp.args.length !== 2, "MapEntry<K, V> constructor expects two args of type K, V");
                const kexp = this.checkExpression(env, exp.args[0], oftype.typeK);
                const vexp = this.checkExpression(env, exp.args[1], oftype.typeV);

                const kcast = this.emitCoerceIfNeeded(kexp, exp.args[0].sinfo, oftype.typeK);
                const vcast = this.emitCoerceIfNeeded(vexp, exp.args[1].sinfo, oftype.typeV);

                return env.setResultExpressionInfo(new TIRMapEntryConstructorExpression(exp.sinfo, kcast.expressionResult, vcast.expressionResult, tirktype, tirvtype, tiroftype), ResolvedType.createSingle(oftype));
            }
            else {
                this.raiseError(exp.sinfo, `Cannot use explicit constructor on type of ${oftype.typeID}`);
                return env.setResultExpressionInfo(new TIRInvalidExpression(exp.sinfo, tiroftype), roftype);
            }
        }
        else if (oftype instanceof ResolvedPrimitiveCollectionEntityAtomType) {
            const roftype = ResolvedType.createSingle(oftype);
            const tiroftype = this.toTIRTypeKey(roftype);

            if(oftype instanceof ResolvedListEntityAtomType) {
                const eargs = exp.args.map((arg) => {
                    const texp = this.checkExpression(env, arg, oftype.typeT);
                    return this.emitCoerceIfNeeded(texp, exp.sinfo, oftype.typeT);
                });

                return env.setResultExpressionInfo(new TIRConstructorListExpression(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype);
            }
            else if(oftype instanceof ResolvedStackEntityAtomType) {
                this.raiseError(exp.sinfo, "Stack<T> not fully supported yet");
                return env.setResultExpressionInfo(new TIRInvalidExpression(exp.sinfo, tiroftype), roftype);
            }
            else if(oftype instanceof ResolvedQueueEntityAtomType) {
                this.raiseError(exp.sinfo, "Queue<T> not fully supported yet");
                return env.setResultExpressionInfo(new TIRInvalidExpression(exp.sinfo, tiroftype), roftype);
            }
            else if(oftype instanceof ResolvedSetEntityAtomType) {
                this.raiseError(exp.sinfo, "Set<T> not fully supported yet");
                return env.setResultExpressionInfo(new TIRInvalidExpression(exp.sinfo, tiroftype), roftype);
            }
            else if(oftype instanceof ResolvedMapEntityAtomType) {
                const metype = this.normalizeTypeOnly(new NominalTypeSignature(exp.sinfo, "Core", ["MapEntry"], [new TemplateTypeSignature(exp.sinfo, "K"), new TemplateTypeSignature(exp.sinfo, "V")]), TemplateBindScope.createDoubleBindScope("K", oftype.typeK, "V", oftype.typeV));
                
                const eargs = exp.args.map((arg) => {
                    const texp = this.checkExpression(env, arg, metype);
                    return this.emitCoerceIfNeeded(texp, exp.sinfo, metype);
                });

                return env.setResultExpressionInfo(new TIRConstructorMapExpression(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype);
            }
            else {
                this.raiseError(exp.sinfo, `Cannot use explicit constructor on type of ${oftype.typeID}`);
                return env.setResultExpressionInfo(new TIRInvalidExpression(exp.sinfo, tiroftype), roftype);
            }
        }
        else {
            this.raiseError(exp.sinfo, `Cannot use explicit constructor on type of ${exp.ctype.getDiagnosticName()}`);
            return env.setResultExpressionInfo(new TIRInvalidExpression(exp.sinfo, "None"), ResolvedType.createInvalid());
        }
    }

    private checkPCodeInvokeExpression(env: ExpressionTypeEnvironment, exp: PCodeInvokeExpression): ExpressionTypeEnvironment {
        const pco = env.argpcodes.get(exp.pcode);
        if (pco !== undefined) {
            const pcload = new TIRAccessVariableExpression(exp.sinfo, exp.pcode, pco.pcode.codekey);
            const args = exp.args.map((arg, ii) => this.emitCoerceIfNeeded(this.checkExpression(env, arg, pco.ftype.params[ii].type as ResolvedType), arg.sinfo, pco.ftype.params[ii].type as ResolvedType).expressionResult);
            const pci = new TIRCodePackInvokeExpression(exp.sinfo, this.toTIRTypeKey(pco.ftype.resultType), pco.pcode, [pcload, ...args]);

            return env.setResultExpressionInfo(pci, pco.ftype.resultType);
        }
        else {
            const pcotry = env.capturedpcodes.get(exp.pcode);
            this.raiseErrorIf(exp.sinfo, pcotry === undefined, `missing binding for lambda invoke -- ${exp.pcode}`);
            const pco = pcotry as { pcode: TIRCodePack, ftype: ResolvedFunctionType };

            const pcload = new TIRAccessCapturedVariableExpression(exp.sinfo, exp.pcode, pco.pcode.codekey);
            const args = exp.args.map((arg, ii) => this.emitCoerceIfNeeded(this.checkExpression(env, arg, pco.ftype.params[ii].type as ResolvedType), arg.sinfo, pco.ftype.params[ii].type as ResolvedType).expressionResult);
            const pci = new TIRCodePackInvokeExpression(exp.sinfo, this.toTIRTypeKey(pco.ftype.resultType), pco.pcode, [pcload, ...args]);

            return env.setResultExpressionInfo(pci, pco.ftype.resultType);
        }
    }

    private checkCallNamespaceFunctionOrOperatorExpression(env: ExpressionTypeEnvironment, exp: CallNamespaceFunctionOrOperatorExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.hasNamespace(exp.ns), `Namespace '${exp.ns}' is not defined`);
        const nsdecl = this.m_assembly.getNamespace(exp.ns);

        if(nsdecl.ns === "Core" && exp.name === "s_safeAs") {
            const argenv = this.checkExpression(env, exp.args[0], this.normalizeTypeOnly(exp.terms[0], env.binds));
            const astype = this.normalizeTypeOnly(exp.terms[1], env.binds);

            return this.emitCoerceIfNeeded_NoCheck(argenv, exp.sinfo, astype);
        }
        else {
            if (nsdecl.operators.has(exp.name)) {
                const opsintro = (nsdecl.operators.get(exp.name) as NamespaceOperatorDecl[]).find((nso) =>  nso.invoke.attributes.includes("abstract") || nso.invoke.attributes.includes("virtual"));
                const opdecls = (nsdecl.operators.get(exp.name) as NamespaceOperatorDecl[]).filter((nso) => !nso.invoke.attributes.includes("abstract") && !nso.invoke.attributes.includes("virtual"));
                this.raiseErrorIf(exp.sinfo, opsintro !== undefined, "Operator must have exactly one abstract/virtual declaration");
                this.raiseErrorIf(exp.sinfo, opdecls.length === 0, "Operator must have at least one implementation");

                const fkey = TIRIDGenerator.generateInvokeIDForNamespaceOperatorBase(nsdecl.ns, exp.name);
                const rtype = this.normalizeTypeOnly((opsintro as NamespaceOperatorDecl).invoke.resultType, TemplateBindScope.createEmptyBindScope());
                const tirrtype = this.toTIRTypeKey(rtype);

                const [argexps, _] = this.checkArgumentList(exp.sinfo, env, exp.args, (opsintro as NamespaceOperatorDecl).invoke.params, TemplateBindScope.createEmptyBindScope());

                this.m_pendingNamespaceOperators.push({fkey: fkey, decl: opsintro as NamespaceOperatorDecl, impls: opdecls.map((opi, ii) => { return {fkey: TIRIDGenerator.generateInvokeIDForNamespaceOperatorImpl(opi.ns, opi.name, ii), decl: opi}; })});
                const tircall = new TIRCallNamespaceOperatorExpression(exp.sinfo, nsdecl.ns, exp.name, fkey, tirrtype, argexps);
                return env.setResultExpressionInfo(tircall, rtype);
            }
            else {
                this.raiseErrorIf(exp.sinfo, !nsdecl.functions.has(exp.name), `Function named '${exp.name}' is not defined`);
                const fdecl = nsdecl.functions.get(exp.name) as NamespaceFunctionDecl;

                this.raiseErrorIf(exp.sinfo, fdecl.invoke.terms.length !== exp.terms.length, "missing template types");
                let binds = new Map<string, ResolvedType>();
                for(let i = 0; i < fdecl.invoke.terms.length; ++i) {
                    binds.set(fdecl.invoke.terms[i].name, this.normalizeTypeOnly(exp.terms[i], env.binds));
                }
                this.checkTemplateTypesOnInvoke(exp.sinfo, fdecl.invoke.terms, TemplateBindScope.createEmptyBindScope(), binds, fdecl.invoke.termRestrictions);

                const rtype = this.normalizeTypeOnly(fdecl.invoke.resultType, TemplateBindScope.createBaseBindScope(binds));
                const tirrtype = this.toTIRTypeKey(rtype);

                const [argexps, fargs, pcl] = this.checkArgumentList(exp.sinfo, env, exp.args, fdecl.invoke.params, TemplateBindScope.createBaseBindScope(binds));
                const fkey = TIRIDGenerator.generateInvokeIDForNamespaceFunction(nsdecl.ns, exp.name, fdecl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)), pcl);

                let pcodes = new Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>();
                fargs.forEach((ee) => {
                    pcodes.set(ee[0], {iscapture: false, pcode: ee[2], ftype: ee[1]});
                });
                this.m_pendingNamespaceFunctions.push({fkey: fkey, decl: fdecl, binds: binds, pcodes: pcodes});

                const tircall = new TIRCallNamespaceFunctionExpression(exp.sinfo, nsdecl.ns, exp.name, fkey, tirrtype, argexps);
                return env.setResultExpressionInfo(tircall, rtype);
            }
        }
    }

    private checkCallStaticFunctionExpression(env: ExpressionTypeEnvironment, exp: CallStaticFunctionExpression): ExpressionTypeEnvironment {
        const oftype = this.normalizeTypeOnly(exp.ttype, env.binds);

        const fdecltry = this.resolveMemberFunction(exp.sinfo, oftype, exp.name);
        this.raiseErrorIf(exp.sinfo, (fdecltry === undefined), `Static function/operator not defined for type ${oftype.typeID}`);

        const fdecl = fdecltry as OOMemberLookupInfo<StaticFunctionDecl>;
        this.raiseErrorIf(exp.sinfo, fdecl.decl.invoke.terms.length !== exp.terms.length, "missing template types");
        let binds = new Map<string, ResolvedType>();
        for(let i = 0; i < fdecl.decl.invoke.terms.length; ++i) {
            binds.set(fdecl.decl.invoke.terms[i].name, this.normalizeTypeOnly(exp.terms[i], env.binds));
        }
        this.checkTemplateTypesOnInvoke(exp.sinfo, fdecl.decl.invoke.terms, TemplateBindScope.createBaseBindScope(fdecl.oobinds), binds, fdecl.decl.invoke.termRestrictions);

        const fdeclscope = TemplateBindScope.createBaseBindScope(fdecl.oobinds).pushScope(binds);
        const rtype = this.normalizeTypeOnly(fdecl.decl.invoke.resultType, fdeclscope);
        const tirrtype = this.toTIRTypeKey(rtype);

        if(oftype.typeID === "KeyType" && (exp.name === "less" || exp.name === "equal")) {
            const ktype = binds.get("K") as ResolvedType;
            this.raiseErrorIf(exp.sinfo, !this.subtypeOf(ktype, this.getSpecialKeyTypeConceptType()) || !ResolvedType.isGroundedType(ktype.options), "Invalid Key type argument");

            this.raiseErrorIf(exp.sinfo, exp.args.length !== 2, "expected 2 arguments");
            const lhsenv = this.checkExpression(env, exp.args[0], ktype);
            this.raiseErrorIf(exp.sinfo, !this.subtypeOf(lhsenv.trepr, ktype), `expected arg of type ${ktype.typeID} but got ${lhsenv.trepr.typeID}`);
            const rhsenv = this.checkExpression(env, exp.args[1], ktype);
            this.raiseErrorIf(exp.sinfo, !this.subtypeOf(rhsenv.trepr, ktype), `expected arg of type ${ktype.typeID} but got ${rhsenv.trepr.typeID}`);

            const tlhs = this.emitCoerceIfNeeded_NoCheck(lhsenv, exp.sinfo, ktype);
            const trhs = this.emitCoerceIfNeeded_NoCheck(rhsenv, exp.sinfo, ktype);

            if (exp.name === "equal") {
                if(ResolvedType.isUniqueType(ktype)) {
                    return env.setResultExpressionInfo(new TIRBinKeyEqBothUniqueExpression(exp.sinfo, tlhs.expressionResult, trhs.expressionResult, this.toTIRTypeKey(ktype)), this.getSpecialBoolType());
                }
                else {
                    return env.setResultExpressionInfo(new TIRBinKeyEqGeneralExpression(exp.sinfo, this.toTIRTypeKey(ktype), tlhs.expressionResult, this.toTIRTypeKey(ktype), trhs.expressionResult), this.getSpecialBoolType());
                }
            }
            else {
                if(ResolvedType.isUniqueType(ktype)) {
                    return env.setResultExpressionInfo(new TIRBinKeyUniqueLessExpression(exp.sinfo, tlhs.expressionResult, trhs.expressionResult, this.toTIRTypeKey(ktype)), this.getSpecialBoolType());
                }
                else {
                    return env.setResultExpressionInfo(new TIRBinKeyGeneralLessExpression(exp.sinfo, tlhs.expressionResult, trhs.expressionResult, this.toTIRTypeKey(ktype)), this.getSpecialBoolType());
                }
            }
        }
        else if ((oftype.typeID === "String" || oftype.typeID === "ASCIIString") && exp.name === "interpolate") {
            this.raiseError(exp.sinfo, "interpolate is not implemented yet");
            return env.setResultExpressionInfo(new TIRInvalidExpression(exp.sinfo, tirrtype), rtype);
        }
        else {
            const [argexps, fargs, pcl] = this.checkArgumentList(exp.sinfo, env, exp.args, fdecl.decl.invoke.params, fdeclscope);

            if (fdecl.decl.invoke.body !== undefined && fdecl.decl.invoke.body.body === "special_inject") {
                return env.setResultExpressionInfo(new TIRInjectExpression(exp.sinfo, argexps[0], tirrtype), rtype);
            }
            else {
                const fkey = TIRIDGenerator.generateInvokeForMemberFunction(this.toTIRTypeKey(fdecl.ttype), exp.name, fdecl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)), pcl);
            
                let pcodes = new Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>();
                fargs.forEach((ee) => {
                    pcodes.set(ee[0], {iscapture: false, pcode: ee[2], ftype: ee[1]});
                });
                this.m_pendingFunctionMemberDecls.push({fkey: fkey, decl: fdecl, binds: binds, pcodes: pcodes});

                const tircall = new TIRCallStaticFunctionExpression(exp.sinfo, this.toTIRTypeKey(fdecl.ttype), exp.name, fkey, tirrtype, argexps);
                return env.setResultExpressionInfo(tircall, rtype);
            }
        }
    }

    private checkAccessFromIndex(env: ExpressionTypeEnvironment, op: PostfixAccessFromIndex): ExpressionTypeEnvironment {
        this.raiseErrorIf(op.sinfo, env.trepr.options.some((atom) => !(atom instanceof ResolvedTupleAtomType)), "Base of index expression must be of Tuple type");
        this.raiseErrorIf(op.sinfo, op.index < 0, "Index cannot be negative");
        this.raiseErrorIf(op.sinfo, env.trepr.options.some((atom) => (atom as ResolvedTupleAtomType).types.length <= op.index), "Index may not be defined for tuple");

        this.raiseErrorIf(op.sinfo, env.trepr.options.length !== 1, "only a single tuple is permitted -- todo: later want to generalize this")
        const tiroftype = this.toTIRTypeKey(env.trepr);

        const idxtype = (env.trepr.options[0] as ResolvedTupleAtomType).types[op.index];
        const tiridxtype = this.toTIRTypeKey(idxtype);

        return env.setResultExpressionInfo(new TIRLoadIndexExpression(op.sinfo, env.expressionResult, tiroftype, op.index, tiridxtype), idxtype);
    }

    private checkAccessFromName(env: ExpressionTypeEnvironment, op: PostfixAccessFromName): ExpressionTypeEnvironment {
        const isrecord = env.trepr.options.every((atom) => atom instanceof ResolvedRecordAtomType);
        const isobj = env.trepr.options.every((atom) => atom instanceof ResolvedEntityAtomType || atom instanceof ResolvedConceptAtomType);

        this.raiseErrorIf(op.sinfo, !isrecord && !isobj, `Cannot load the named location ${op.name} from type ${env.trepr.typeID}`);
        const tiroftype = this.toTIRTypeKey(env.trepr);

        if (isrecord) {
            this.raiseErrorIf(op.sinfo, env.trepr.options.some((atom) => (atom as ResolvedRecordAtomType).entries.find((entry) => entry.pname === op.name) === undefined), `Property "${op.name}" not be defined for record`);

            const rtype = ((env.trepr.options[0] as ResolvedRecordAtomType).entries.find((entry) => entry.pname === op.name) as {pname: string, ptype: ResolvedType}).ptype;
            const tirrtype = this.toTIRTypeKey(rtype);

            this.raiseErrorIf(op.sinfo, env.trepr.options.length === 0, "only non-virtual property loads are supported for now");
            return env.setResultExpressionInfo(new TIRLoadPropertyExpression(op.sinfo, env.expressionResult, tiroftype, op.name, tirrtype), rtype);
        }
        else {
            const fftry = this.resolveMemberField(op.sinfo, env.trepr, op.name);
            this.raiseErrorIf(op.sinfo, fftry === undefined, `Could not resolve field "${op.name}" on type ${env.trepr.typeID}`);
            const ff = fftry as OOMemberLookupInfo<MemberFieldDecl>;

            const fftype = this.normalizeTypeOnly(ff.decl.declaredType, TemplateBindScope.createBaseBindScope(ff.oobinds));
            const tirfftype = this.toTIRTypeKey(fftype);

            const fkey = TIRIDGenerator.generateMemberFieldID(this.toTIRTypeKey(ff.ttype), op.name);

            if(ff.ootype instanceof EntityTypeDecl) {
                return env.setResultExpressionInfo(new TIRLoadFieldExpression(op.sinfo, tiroftype, env.expressionResult, fkey, tirfftype), fftype);
            }
            else {
                return env.setResultExpressionInfo(new TIRLoadFieldVirtualExpression(op.sinfo, tirfftype, env.expressionResult, fkey, tirfftype), fftype);
            }
        }
    }

    private checkInvoke(env: ExpressionTypeEnvironment, op: PostfixInvoke, refvar: string | undefined): ExpressionTypeEnvironment {
        const resolvefrom = op.specificResolve !== undefined ? this.normalizeTypeOnly(op.specificResolve, env.binds) : env.trepr;
        const mresolvetry = this.resolveMemberMethod(op.sinfo, resolvefrom, op.name);

        this.raiseErrorIf(op.sinfo, op.isRefThis && refvar === undefined, "Cannot call a ref function in this expression position (top-level only)");

        this.raiseErrorIf(op.sinfo, mresolvetry === undefined, `Could not resolve method name "${op.name}" from type ${resolvefrom.typeID}`);
        const mresolve = mresolvetry as OOMemberResolution<MemberMethodDecl>;

        this.raiseErrorIf(op.sinfo, mresolve.decl.decl.invoke.terms.length !== op.terms.length, "missing template types");
        let binds = new Map<string, ResolvedType>();
        for (let i = 0; i < mresolve.decl.decl.invoke.terms.length; ++i) {
            binds.set(mresolve.decl.decl.invoke.terms[i].name, this.normalizeTypeOnly(op.terms[i], env.binds));
        }
        this.checkTemplateTypesOnInvoke(op.sinfo, mresolve.decl.decl.invoke.terms, TemplateBindScope.createBaseBindScope(mresolve.decl.oobinds), binds, mresolve.decl.decl.invoke.termRestrictions);

        const fdeclscope = TemplateBindScope.createBaseBindScope(mresolve.decl.oobinds).pushScope(binds);
        const rtype = this.normalizeTypeOnly(mresolve.decl.decl.invoke.resultType, fdeclscope);
        const tirrtype = this.toTIRTypeKey(rtype);

        const tirdecltype = this.toTIRTypeKey(mresolve.decl.ttype);

        const [argexps, fargs, pcl] = this.checkArgumentList(op.sinfo, env.createFreshEnvExpressionFrom(), op.args, mresolve.decl.decl.invoke.params, fdeclscope);

        let pcodes = new Map<string, { iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType }>();
        fargs.forEach((ee) => {
                pcodes.set(ee[0], { iscapture: false, pcode: ee[2], ftype: ee[1]});
        });

        if((!mresolve.decl.decl.attributes.includes("abstract") && !mresolve.decl.decl.attributes.includes("virtual"))) {
            this.raiseErrorIf(op.sinfo, mresolve.impl.length !== 1, `Could not resolve implementation for non-virtual method ${op.name} from ${resolvefrom.typeID}`);
            const knownimpl = mresolve.impl[0];

            const tkey = this.toTIRTypeKey(mresolve.impl[0].ttype);
            if (knownimpl.decl.invoke.body !== undefined && (typeof (knownimpl.decl.invoke.body.body) === "string") && (knownimpl.decl.invoke.body.body as string) === "special_extract") {
                this.raiseErrorIf(op.sinfo, op.args.length !== 0, "No arguments permitted on this method");

                return env.setResultExpressionInfo(new TIRExtractExpression(op.sinfo, env.expressionResult, tirrtype), rtype);
            }
            else {
                const knowntype = this.toTIRTypeKey(knownimpl.ttype);
                const knownkey = TIRIDGenerator.generateInvokeForMemberMethod(knowntype, op.name, knownimpl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)), pcl);
                
                const fkey = TIRIDGenerator.generateInvokeForMemberMethod(tirdecltype, op.name, mresolve.decl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)), pcl);
                this.m_pendingMethodMemberDecls.push({fkey: knownkey, decl: knownimpl, declaredecl: mresolve.decl, binds: binds, pcodes: pcodes}, {fkey: fkey, decl: mresolve.decl, declaredecl: mresolve.decl, binds: binds, pcodes: pcodes});

                const rcvrexp = this.emitCoerceIfNeeded(env, op.sinfo, mresolve.impl[0].ttype);
                this.raiseErrorIf(op.sinfo, mresolve.decl.decl.invoke.isThisRef && !(mresolve.impl[0].ootype instanceof EntityTypeDecl), `self call with ref can only be done on non-virtual methods defined on entities but got ${mresolve.impl[0].ttype.typeID}`);

                if (mresolve.decl.decl.invoke.isThisRef) {
                    return env.setResultExpressionInfo(new TIRCallMemberFunctionSelfRefExpression(op.sinfo, this.m_scratchCtr++, tkey, op.name, fkey, tirdecltype, tirrtype, refvar as string, rcvrexp.expressionResult, argexps), rtype);
                }
                else {
                    return env.setResultExpressionInfo(new TIRCallMemberFunctionExpression(op.sinfo, tkey, op.name, fkey, tirdecltype, tirrtype, rcvrexp.expressionResult, argexps), rtype);
                }
            }
        }
        else {
            this.raiseErrorIf(op.sinfo, mresolve.decl.decl.invoke.isThisRef, "cannot use ref on virtual method call -- variance on updated this ref type");
            const tkey = this.toTIRTypeKey(mresolve.decl.ttype);
            const declkey = TIRIDGenerator.generateInvokeForMemberMethod(tirdecltype, op.name, mresolve.decl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)), pcl);
            this.m_pendingMethodMemberDecls.push({fkey: declkey, decl: mresolve.decl, declaredecl: mresolve.decl, binds: binds, pcodes: pcodes});

            if(resolvefrom.options.length === 1 && ResolvedType.isUniqueType(resolvefrom.options[0])) {
                const inferfimpltype = this.toTIRTypeKey(mresolve.impl[0].ttype);
                const inferfkey = TIRIDGenerator.generateInvokeForMemberMethod(inferfimpltype, op.name, mresolve.decl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)), pcl);
                this.m_pendingMethodMemberDecls.push({fkey: inferfkey, decl: mresolve.impl[0], declaredecl: mresolve.decl, binds: binds, pcodes: pcodes});

                const rcvrexp = this.emitCoerceIfNeeded(env, op.sinfo, mresolve.impl[0].ttype);
                return env.setResultExpressionInfo(new TIRCallMemberFunctionExpression(op.sinfo, inferfimpltype, op.name, inferfkey, inferfimpltype, tirrtype, rcvrexp.expressionResult, argexps), rtype);
            }
            else {
                const rcvrexp = this.emitCoerceIfNeeded(env, op.sinfo, mresolve.decl.ttype);
                return env.setResultExpressionInfo(new TIRCallMemberFunctionDynamicExpression(op.sinfo, tkey, op.name, declkey, tirdecltype, tirrtype, rcvrexp.expressionResult, argexps), rtype);
            }
        }
    }

    private checkTaskSelfAction(env: ExpressionTypeEnvironment, exp: TaskSelfActionExpression, refop: boolean): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk !== "write", "This code does not permit task operations (not a task method/action)");
        const tsk = this.m_taskType as {taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType>};
        const tasktype = ResolvedType.createSingle(ResolvedTaskAtomType.create(tsk.taskdecl, tsk.taskbinds));

        const mresolvetry = tsk.taskdecl.memberMethods.find((mm) => mm.name === exp.name);
        this.raiseErrorIf(exp.sinfo, mresolvetry === undefined, `Could not resolve method name "${exp.name}" from type ${tasktype.typeID}`);
        const mresolve = mresolvetry as MemberMethodDecl;

        this.raiseErrorIf(exp.sinfo, refop !== mresolve.invoke.isThisRef, "Cannot call a action/ref function in this expression position");

        this.raiseErrorIf(exp.sinfo, mresolve.invoke.terms.length !== exp.terms.length, "missing template types");
        let binds = new Map<string, ResolvedType>();
        for (let i = 0; i < mresolve.invoke.terms.length; ++i) {
            binds.set(mresolve.invoke.terms[i].name, this.normalizeTypeOnly(exp.terms[i], env.binds));
        }
        this.checkTemplateTypesOnInvoke(exp.sinfo, mresolve.invoke.terms, TemplateBindScope.createBaseBindScope(tsk.taskbinds), binds, mresolve.invoke.termRestrictions);

        const fdeclscope = TemplateBindScope.createBaseBindScope(tsk.taskbinds).pushScope(binds);
        const rtype = this.normalizeTypeOnly(mresolve.invoke.resultType, fdeclscope);
        const tirrtype = this.toTIRTypeKey(rtype);

        const tirdecltype = this.toTIRTypeKey(tasktype);

        const [argexps, fargs, pcl] = this.checkArgumentList(exp.sinfo, env.createFreshEnvExpressionFrom(), exp.args, mresolve.invoke.params, fdeclscope);
        let pcodes = new Map<string, { iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType }>();
        fargs.forEach((ee) => {
            pcodes.set(ee[0], { iscapture: false, pcode: ee[2], ftype: ee[1] });
        });

        const fkey = TIRIDGenerator.generateInvokeForMemberMethod(tirdecltype, exp.name, mresolve.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)), pcl);
        const mldecl = new OOMemberLookupInfo<MemberMethodDecl>(tasktype, tsk.taskdecl, tsk.taskbinds, mresolve);
        this.m_pendingMethodMemberDecls.push({fkey: fkey, decl: mldecl, declaredecl: mldecl, binds: binds, pcodes: pcodes});

        this.raiseErrorIf(exp.sinfo, exp.isSelfRef !== mresolve.hasAttribute("ref"), `mismatch on self/this ref at callsite ${mresolve.name}`);

        if(mresolve.invoke.attributes.includes("task_action")) {
            return env.setResultExpressionInfo(new TIRCallMemberActionExpression(exp.sinfo, this.m_scratchCtr++, exp.name, fkey, tirrtype, this.toTIRTypeKey(tasktype), argexps), rtype);
        }
        else if (mresolve.invoke.isThisRef) {
            return env.setResultExpressionInfo(new TIRCallMemberFunctionTaskSelfRefExpression(exp.sinfo, this.m_scratchCtr++, exp.name, fkey, tirrtype, this.toTIRTypeKey(tasktype), argexps), rtype);
        }
        else {
            return env.setResultExpressionInfo(new TIRCallMemberFunctionTaskExpression(exp.sinfo, exp.name, fkey, tirrtype, this.toTIRTypeKey(tasktype), argexps), rtype);
        }
    }

    private checkTaskGetIDExpression(env: ExpressionTypeEnvironment, exp: TaskGetIDExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk === "no", "This code does not permit task operations");
        const tsk = this.m_taskType as {taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType>};
        const tasktype = ResolvedType.createSingle(ResolvedTaskAtomType.create(tsk.taskdecl, tsk.taskbinds));

        return env.setResultExpressionInfo(new TIRTaskGetIDExpression(exp.sinfo, this.toTIRTypeKey(tasktype),  this.toTIRTypeKey(this.getSpecialTaskIDType())), this.getSpecialTaskIDType());
    }
    */

    private checkEmptyStatement(env: TypeEnvironment, stmt: EmptyStatement): TypeEnvironment {
        return env;
    }

    private checkVariableDeclarationStatement(env: TypeEnvironment, stmt: VariableDeclarationStatement): TypeEnvironment {
        this.checkTypeSignature(stmt.vtype);
        
        return env.addLocalVar(stmt.name, stmt.vtype, false, false);
    }
    
    private checkVariableMultiDeclarationStatement(env: TypeEnvironment, stmt: VariableMultiDeclarationStatement): TypeEnvironment {
        for(let i = 0; i < stmt.decls.length; ++i) {
            this.checkTypeSignature(stmt.decls[i].vtype);
            env = env.addLocalVar(stmt.decls[i].name, stmt.decls[i].vtype, false, false);
        }
        return env;
    }

    private checkVariableInitializationStatement(env: TypeEnvironment, stmt: VariableInitializationStatement): TypeEnvironment {
        this.checkTypeSignature(stmt.vtype);

        const itype = !(stmt.vtype instanceof AutoTypeSignature) ? stmt.vtype : undefined;
        const rhs = this.checkExpressionRHS(env, stmt.exp, itype !== undefined ? new SimpleTypeInferContext(itype) : undefined);
        
        //TODO: do we need to update any other type env info here based on RHS actions???

        this.checkError(stmt.sinfo, itype !== undefined && !(rhs instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(rhs, itype, this.constraints), `Expression of type ${TypeChecker.safeTypePrint(rhs)} cannot be assigned to variable of type ${TypeChecker.safeTypePrint(itype)}`);
        return stmt.name !== "_" ? env.addLocalVar(stmt.name, itype || rhs, stmt.isConst, true) : env; //try to recover a bit
    }

    private checkVariableMultiInitializationStatement(env: TypeEnvironment, stmt: VariableMultiInitializationStatement): TypeEnvironment {
        for(let i = 0; i < stmt.decls.length; ++i) {
            this.checkTypeSignature(stmt.decls[i].vtype);
        }

        const iopts = stmt.decls.map((decl) => !(decl.vtype instanceof AutoTypeSignature) ? decl.vtype : undefined);
        let evals: TypeSignature[] = [];
        if(Array.isArray(stmt.exp)) {
            for(let i = 0; i < stmt.exp.length; ++i) {
                const etype = this.checkExpression(env, stmt.exp[i], i < iopts.length && iopts[i] !== undefined ? new SimpleTypeInferContext(iopts[i] as TypeSignature) : undefined); 
                evals.push(etype);
            }
        }
        else {
            const iinfer = new EListStyleTypeInferContext(iopts);
            const etype = this.checkExpressionRHS(env, stmt.exp, iinfer);
            if(etype instanceof EListTypeSignature) {
                evals.push(...etype.entries);
            }
            else {
                this.reportError(stmt.sinfo, "Expected a EList for multi-variable initialization");
            }
        }

        this.checkError(stmt.sinfo, iopts.length !== evals.length, "Mismatch in number of variables and expressions in multi-variable initialization");
        for(let i = evals.length; i < iopts.length; ++i) {
            evals.push(new ErrorTypeSignature(stmt.sinfo, undefined)); //try to recover a bit
        }

        for(let i = 0; i < stmt.decls.length; ++i) {
            const decl = stmt.decls[i];
            const itype = iopts[i];
            const etype = evals[i];

            //TODO: do we need to update any other type env info here based on RHS actions???

            this.checkError(stmt.sinfo, itype !== undefined && !(etype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(etype, itype, this.constraints), `Expression of type ${TypeChecker.safeTypePrint(etype)} cannot be assigned to variable of type ${TypeChecker.safeTypePrint(itype)}`);
            env = decl.name !== "_" ? env.addLocalVar(decl.name, itype || etype, stmt.isConst, true) : env; //try to recover a bit
        }

        return env;
    }

    private checkVariableAssignmentStatement(env: TypeEnvironment, stmt: VariableAssignmentStatement): TypeEnvironment {
        const vinfo = env.resolveLocalVarInfoFromSrcName(stmt.name);
        if(vinfo === undefined && stmt.name !== "_") {
            this.reportError(stmt.sinfo, `Variable ${stmt.name} is not declared`);
            return env;
        }

        let decltype: TypeSignature | undefined = undefined;
        if(vinfo !== undefined) {
            this.checkError(stmt.sinfo, vinfo.isConst, `Variable ${stmt.name} is declared as const and cannot be assigned`);
            decltype = vinfo.vtype;
        }

        const rhs = this.checkExpressionRHS(env, stmt.exp, decltype !== undefined ? new SimpleTypeInferContext(decltype) : undefined);

        //TODO: do we need to update any other type env info here based on RHS actions???

        this.checkError(stmt.sinfo, decltype !== undefined && !this.relations.isSubtypeOf(rhs, decltype, this.constraints), `Expression of type ${TypeChecker.safeTypePrint(rhs)} cannot be assigned to variable of type ${TypeChecker.safeTypePrint(decltype)}`);
        return stmt.name !== "_" ? env.assignLocalVariable(stmt.name) : env;
    }

    private checkVariableMultiAssignmentStatement(env: TypeEnvironment, stmt: VariableMultiAssignmentStatement): TypeEnvironment {
        const opts = stmt.names.map((vname) => env.resolveLocalVarInfoFromSrcName(vname));
        let iopts: (TypeSignature | undefined)[] = [];
        for(let i = 0; i < opts.length; ++i) {
            if(opts[i] !== undefined) {
                this.checkError(stmt.sinfo, (opts[i] as VarInfo).isConst, `Variable ${stmt.names[i]} is declared as const and cannot be assigned`);
                iopts.push((opts[i] as VarInfo).vtype);
            }
            else {
                if(stmt.names[i] !== "_") {
                    this.reportError(stmt.sinfo, `Variable ${stmt.names[i]} is not declared`);
                }
                iopts.push(undefined);
            }
        }

        let evals: TypeSignature[] = [];
        if(Array.isArray(stmt.exp)) {
            for(let i = 0; i < stmt.exp.length; ++i) {
                const etype = this.checkExpression(env, stmt.exp[i], i < iopts.length && iopts[i] !== undefined ? new SimpleTypeInferContext(iopts[i] as TypeSignature) : undefined); 
                evals.push(etype);
            }
        }
        else {
            const iinfer = new EListStyleTypeInferContext(iopts);
            const etype = this.checkExpressionRHS(env, stmt.exp, iinfer);
            if(etype instanceof EListTypeSignature) {
                evals.push(...etype.entries);
            }
            else {
                this.reportError(stmt.sinfo, "Expected a EList for multi-variable initialization");
            }
        }

        this.checkError(stmt.sinfo, opts.length !== evals.length, "Mismatch in number of variables and expressions in multi-variable initialization");
        for(let i = evals.length; i < opts.length; ++i) {
            evals.push(new ErrorTypeSignature(stmt.sinfo, undefined)); //try to recover a bit
        }

        for(let i = 0; i < stmt.names.length; ++i) {
            const name = stmt.names[i];
            const itype = i < iopts.length && iopts[i] !== undefined ? (iopts[i] as TypeSignature) : undefined;
            const etype = evals[i];

            //TODO: do we need to update any other type env info here based on RHS actions???

            this.checkError(stmt.sinfo, itype !== undefined && !(etype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(etype, itype, this.constraints), `Expression of type ${TypeChecker.safeTypePrint(etype)} cannot be assigned to variable of type ${TypeChecker.safeTypePrint(itype)}`);
            env = name !== "_" ? env.assignLocalVariable(name) : env; 
        }

        return env;
    }

    private checkVariableRetypeStatement(env: TypeEnvironment, stmt: VariableRetypeStatement): TypeEnvironment {
        const vinfo = env.resolveLocalVarInfoFromSrcName(stmt.name);
        if(vinfo === undefined) {
            this.reportError(stmt.sinfo, `Variable ${stmt.name} is not declared`);
            return env;
        }
        if(vinfo.isConst) {
            this.reportError(stmt.sinfo, `Variable ${stmt.name} is declared as const and cannot be re-typed`);
            return env;
        }
        if(!vinfo.mustDefined) {
            this.reportError(stmt.sinfo, `Variable ${stmt.name} is not defined`);
            return env;
        }

        const splits = this.processITestAsConvert(stmt.sinfo, env, vinfo.vtype, stmt.ttest);
        this.checkError(stmt.sinfo, splits.ttrue === undefined, `retype will always fail`);

        stmt.vtype = vinfo.vtype;
        stmt.newvtype = splits.ttrue || vinfo.vtype;
        return env.retypeLocalVariable(stmt.name, splits.ttrue || vinfo.vtype);
    }

    private checkReturnStatement(env: TypeEnvironment, stmt: ReturnStatement): TypeEnvironment {
        if(stmt.value === undefined) {
            this.checkError(stmt.sinfo, !this.isVoidType(env.declReturnType), `Expected a return value of type ${env.declReturnType.tkeystr}`);
        }
        else if(!Array.isArray(stmt.value)) {
            const rtype = this.checkExpressionRHS(env, stmt.value, env.inferReturn);
            this.checkError(stmt.sinfo, !(rtype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(rtype, env.declReturnType, this.constraints), `Expected a return value of type ${env.declReturnType.tkeystr} but got ${rtype.tkeystr}`);
        }
        else {
            if(this.checkError(stmt.sinfo, !(env.inferReturn instanceof EListStyleTypeInferContext), `Multiple return requires an Elist type but got ${env.declReturnType.tkeystr}`)) {
                return env.setReturnFlow();
            }

            const rtypes = TypeInferContext.asEListOptions(env.inferReturn) as (TypeSignature | undefined)[];
            this.checkError(stmt.sinfo, rtypes.length !== stmt.value.length, `Mismatch in number of return values and expected return types`);

            for(let i = 0; i < stmt.value.length; ++i) {
                const rtype = i < rtypes.length ? rtypes[i] : undefined;
                const etype = this.checkExpression(env, stmt.value[i], rtype);

                const rtname = rtype !== undefined ? rtype.tkeystr : "skip";
                this.checkError(stmt.sinfo, rtype !== undefined && !(etype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(etype, rtype, this.constraints), `Expected a return value of type ${rtname} but got ${etype.tkeystr}`);
            }

            return env.setReturnFlow();
        }

        return env.setReturnFlow();
    }

    private checkFlowRebinder(sinfo: SourceInfo, binfo: BinderInfo | undefined, env: TypeEnvironment) {
        if(binfo === undefined || !binfo.refineonfollow) {
            return;
        }

        const vinfo = env.resolveLocalVarInfoFromScopeName(binfo.scopename);
        if(vinfo === undefined) {
            this.reportError(sinfo, `Variable ${binfo.srcname} is not declared`);
            return
        }
        if(vinfo.isConst) {
            this.reportError(sinfo, `Variable ${binfo.srcname} is declared as const and cannot be re-typed`);
            return;
        }
        if(!vinfo.mustDefined) {
            this.reportError(sinfo, `Variable ${binfo.srcname} is not defined`);
            return;
        }
    }

    private checkIfStatement(env: TypeEnvironment, stmt: IfStatement): TypeEnvironment {
        let eetype = this.checkExpression(env, stmt.cond.exp, undefined);
        
        if(stmt.cond.itestopt === undefined) {
            if(eetype instanceof ErrorTypeSignature) {
                eetype = this.getWellKnownType("Bool");
            }

            this.checkError(stmt.sinfo, !this.isBooleanType(eetype), "If test requires a Bool type");
            this.checkError(stmt.sinfo, stmt.binder !== undefined, "Binder is not valid here -- requires use of an ITest");

            const ttrue = this.checkBlockStatement(env, stmt.trueBlock);
            return TypeEnvironment.mergeEnvironmentsSimple(env, ttrue);
        }
        else {
            const splits = this.processITestAsConvert(stmt.sinfo, env, eetype, stmt.cond.itestopt);
            this.checkError(stmt.sinfo, splits.ttrue === undefined, "Test is never true -- true branch of if is unreachable");
            this.checkError(stmt.sinfo, splits.tfalse === undefined, "Test is never false -- false branch of if is unreachable");

            if(stmt.binder === undefined) {
                const ttrue = this.checkBlockStatement(env, stmt.trueBlock);
                return TypeEnvironment.mergeEnvironmentsSimple(env, ttrue);
            }
            else {
                stmt.binder.scopename = env.getBindScopeName(stmt.binder.srcname);
                const nenv = env.pushNewLocalBinderScope(stmt.binder.srcname, stmt.binder.scopename, splits.ttrue || eetype);
                const ttrue = this.checkStatement(nenv, stmt.trueBlock).popLocalScope();

                const lubtype = ttrue.normalflow ? eetype : splits.tfalse;
                this.checkFlowRebinder(stmt.sinfo, stmt.binder, env);
                return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, lubtype, env, ttrue);
            }
        }
    }

    private checkIfElseStatement(env: TypeEnvironment, stmt: IfElseStatement): TypeEnvironment {
        let eetype = this.checkExpression(env, stmt.cond.exp, undefined);

        if(stmt.cond.itestopt === undefined) {
            if(eetype instanceof ErrorTypeSignature) {
                eetype = this.getWellKnownType("Bool");
            }

            this.checkError(stmt.sinfo, !this.isBooleanType(eetype), "If test requires a Bool type");
            this.checkError(stmt.sinfo, stmt.binder !== undefined, "Binder is not valid here -- requires use of an ITest");

            const ttrue = this.checkBlockStatement(env, stmt.trueBlock);
            const tfalse = this.checkBlockStatement(env, stmt.falseBlock);
            return TypeEnvironment.mergeEnvironmentsSimple(ttrue, tfalse);
        }
        else {
            const splits = this.processITestAsConvert(stmt.sinfo, env, eetype, stmt.cond.itestopt);
            this.checkError(stmt.sinfo, splits.ttrue === undefined, "Test is never true -- true branch of if is unreachable");
            this.checkError(stmt.sinfo, splits.tfalse === undefined, "Test is never false -- false branch of if is unreachable");

            if(stmt.binder === undefined) {
                const ttrue = this.checkBlockStatement(env, stmt.trueBlock);
                const tfalse = this.checkBlockStatement(env, stmt.falseBlock);
                return TypeEnvironment.mergeEnvironmentsSimple(ttrue, tfalse);
            }
            else {
                stmt.binder.scopename = env.getBindScopeName(stmt.binder.srcname);

                const tenv = env.pushNewLocalBinderScope(stmt.binder.srcname, stmt.binder.scopename, splits.ttrue || eetype);
                const ttrue = this.checkStatement(tenv, stmt.trueBlock).popLocalScope();

                const fenv = env.pushNewLocalBinderScope(stmt.binder.srcname, stmt.binder.scopename, splits.tfalse || eetype);
                const tfalse = this.checkStatement(fenv, stmt.falseBlock).popLocalScope();

                this.checkFlowRebinder(stmt.sinfo, stmt.binder, env);
                if(ttrue.normalflow && tfalse.normalflow) {
                    return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, eetype, ttrue, tfalse);
                }
                else if(ttrue.normalflow) {
                    return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, splits.ttrue as TypeSignature, ttrue, tfalse);
                }
                else if(tfalse.normalflow) {
                    return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, splits.tfalse as TypeSignature, ttrue, tfalse);
                }
                else {
                    return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, eetype, ttrue, tfalse);
                }
            }
        }
    }

    private checkIfElifElseStatement(env: TypeEnvironment, stmt: IfElifElseStatement): TypeEnvironment {
        let branchflows: TypeEnvironment[] = [];

        for(let i = 0; i < stmt.condflow.length; ++i) {
            let etype = this.checkExpression(env, stmt.condflow[i].cond, undefined);
            if(etype instanceof ErrorTypeSignature) {
                etype = this.getWellKnownType("Bool");
            }

            this.checkError(stmt.condflow[i].cond.sinfo, !this.isBooleanType(etype), `Expected a boolean expression but got ${etype.tkeystr}`);
            
            const resenv = this.checkBlockStatement(env, stmt.condflow[i].block);
            branchflows.push(resenv);
        }

        const elseflow = this.checkBlockStatement(env, stmt.elseflow);

        return TypeEnvironment.mergeEnvironmentsSimple(env, ...branchflows, elseflow);
    }

    private checkSwitchStatement(env: TypeEnvironment, stmt: SwitchStatement): TypeEnvironment {
        let ctype = this.checkExpression(env, stmt.sval, undefined);
        
        let exhaustive = false;
        let results: TypeEnvironment[] = [];

        this.checkError(stmt.sinfo, stmt.switchflow.length < 2, "Switch statement must have 2 or more choices");

        for (let i = 0; i < stmt.switchflow.length && !exhaustive; ++i) {
            //it is a wildcard match
            if(stmt.switchflow[i].lval === undefined) {
                this.checkError(stmt.sinfo, i !== stmt.switchflow.length - 1, `wildcard should be last option in switch expression but there were ${stmt.switchflow.length - (i + 1)} more that are unreachable`);
                exhaustive = true;

                const cenv = this.checkBlockStatement(env, stmt.switchflow[i].value);
                results.push(cenv);
            }
            else {
                const slitexp = (stmt.switchflow[i].lval as LiteralExpressionValue).exp;
                const littype = this.checkExpression(env, slitexp, undefined);
                if(!this.relations.isUniqueKeyType(littype, this.constraints)) {
                    this.reportError(slitexp.sinfo, `Switch statement requires a unique key type but got ${littype.tkeystr}`);
                }
                else {
                    const cmpok = this.checkValueEq(stmt.sval, ctype, slitexp, littype);
                    this.checkError(slitexp.sinfo, cmpok === "err", `Cannot compare arguments in switch statement ${littype.tkeystr}`);
                }

                const cenv = this.checkBlockStatement(env, stmt.switchflow[i].value);
                results.push(cenv);
            }
        }
        this.checkError(stmt.sinfo, !exhaustive, "Switch statement must be exhaustive or have a wildcard match at the end");
        
        return TypeEnvironment.mergeEnvironmentsSimple(env, ...results);
    }

    private checkMatchStatement(env: TypeEnvironment, stmt: MatchStatement): TypeEnvironment {
        const eetype = this.checkExpression(env, stmt.sval[0], undefined);
        let ctype = this.relations.decomposeType(eetype, this.constraints) || [];
        if(ctype.length === 0) {
            this.reportError(stmt.sval[0].sinfo, `Match statement requires a decomposable type but got ${eetype.tkeystr}`);
            return env;
        }
        
        let exhaustive = false;
        let results: TypeEnvironment[] = [];

        if(stmt.sval[1] !== undefined) {
            stmt.sval[1].scopename = env.getBindScopeName(stmt.sval[1].srcname);
        }

        this.checkError(stmt.sinfo, stmt.matchflow.length < 2, "Switch statement must have 2 or more choices");

        for (let i = 0; i < stmt.matchflow.length && !exhaustive; ++i) {
            //it is a wildcard match
            if(stmt.matchflow[i].mtype === undefined) {
                this.checkError(stmt.sinfo, i !== stmt.matchflow.length - 1, `wildcard should be last option in switch expression but there were ${stmt.matchflow.length - (i + 1)} more that are unreachable`);
                exhaustive = true;

                let cenv = env;
                if(stmt.sval[1] !== undefined) {
                    cenv = env.pushNewLocalBinderScope(stmt.sval[1].srcname, stmt.sval[1].scopename, this.relations.flowTypeLUB(stmt.matchflow[i].value.sinfo, eetype, ctype, this.constraints))
                }
                cenv = this.checkBlockStatement(env, stmt.matchflow[i].value);

                if(stmt.sval[1] !== undefined) {
                    cenv = cenv.popLocalScope();
                }
                results.push(cenv);
            }
            else {
                const mtype = stmt.matchflow[i].mtype as TypeSignature;
                this.checkTypeSignature(mtype);

                const splits = this.relations.refineMatchType(ctype, mtype, this.constraints);
                if(splits === undefined) {
                    this.reportError(stmt.sinfo, `Match statement requires a type that is a subtype of the decomposed type but got ${mtype.tkeystr}`);
                    return env;
                }
                else {
                    this.checkError(stmt.sinfo, splits.overlap.length === 0, "Test is never true -- true branch of if is unreachable");

                    exhaustive = splits.remain.length === 0;
                    this.checkError(stmt.sinfo, exhaustive && i !== stmt.matchflow.length - 1, `Test is never false -- but there were ${stmt.matchflow.length - (i + 1)} more that are unreachable`);

                    let cenv = env;
                    if(stmt.sval[1] !== undefined) {
                        cenv = env.pushNewLocalBinderScope(stmt.sval[1].srcname, stmt.sval[1].scopename, mtype);
                    }
                    cenv = this.checkBlockStatement(env, stmt.matchflow[i].value);

                    if(stmt.sval[1] !== undefined) {
                        cenv = cenv.popLocalScope();
                    }
                    ctype = splits.remain || ctype;
                    results.push(cenv);
                }
            }
        }
        this.checkError(stmt.sinfo, !exhaustive, "Match statement must be exhaustive or have a wildcard match at the end");
        
        return TypeEnvironment.mergeEnvironmentsSimple(env, ...results);
    }

    private checkAbortStatement(env: TypeEnvironment, stmt: AbortStatement): TypeEnvironment {
        return env.setDeadFlow();
    }

    private checkAssertStatement(env: TypeEnvironment, stmt: AssertStatement): TypeEnvironment {
        const etype = this.checkExpression(env, stmt.cond, undefined);
        if(etype instanceof ErrorTypeSignature) {
            return env;
        }

        this.checkError(stmt.sinfo, !this.isBooleanType(etype), `Expected a boolean type for assert condition but got ${etype.tkeystr}`);
        return env;
    }

    private checkValidateStatement(env: TypeEnvironment, stmt: ValidateStatement): TypeEnvironment {
        const etype = this.checkExpression(env, stmt.cond, undefined);
        if(etype instanceof ErrorTypeSignature) {
            return env;
        }

        this.checkError(stmt.sinfo, !this.isBooleanType(etype), `Expected a boolean type for validate condition but got ${etype.tkeystr}`);
        return env;
    }

    private checkDebugStatement(env: TypeEnvironment, stmt: DebugStatement): TypeEnvironment {
        this.checkExpression(env, stmt.value, undefined);

        return env;
    }

    private checkVoidRefCallStatement(env: TypeEnvironment, stmt: VoidRefCallStatement): TypeEnvironment {
        assert(false, "Not implemented -- VoidRefCallStatement");
    }

    private checkVarUpdateStatement(env: TypeEnvironment, stmt: VarUpdateStatement): TypeEnvironment {
        assert(false, "Not implemented -- VarUpdateStatement");
    }

    private checkThisUpdateStatement(env: TypeEnvironment, stmt: ThisUpdateStatement): TypeEnvironment {
        assert(false, "Not implemented -- ThisUpdateStatement");
    }

    private checkSelfUpdateStatement(env: TypeEnvironment, stmt: SelfUpdateStatement): TypeEnvironment {
        assert(false, "Not implemented -- SelfUpdateStatement");
    }

    private checkEnvironmentUpdateStatement(env: TypeEnvironment, stmt: EnvironmentUpdateStatement): TypeEnvironment {
        assert(false, "Not implemented -- EnvironmentUpdateStatement");
    }

    private checkEnvironmentBracketStatement(env: TypeEnvironment, stmt: EnvironmentBracketStatement): TypeEnvironment {
        assert(false, "Not implemented -- EnvironmentBracketStatement");
    }

    private checkTaskStatusStatement(env: TypeEnvironment, stmt: TaskStatusStatement): TypeEnvironment {
        assert(false, "Not implemented -- TaskStatusStatement");
    }

    private checkTaskEventEmitStatement(env: TypeEnvironment, stmt: TaskEventEmitStatement): TypeEnvironment {
        assert(false, "Not implemented -- TaskEventEmitStatement");
    }

    private checkTaskYieldStatement(env: TypeEnvironment, stmt: TaskYieldStatement): TypeEnvironment {
        assert(false, "Not implemented -- TaskYieldStatement");
    }

    private checkBlockStatement(env: TypeEnvironment, stmt: BlockStatement): TypeEnvironment {
        env = env.pushNewLocalScope();
        for (let i = 0; i < stmt.statements.length; ++i) {
            env = this.checkStatement(env, stmt.statements[i]);
        }
        env = env.popLocalScope();

        return env;
    }

    /*
    private checkEnvironmentFreshStatement(env: StatementTypeEnvironment, stmt: EnvironmentFreshStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const assigns = stmt.assigns.map((asgn) => {
            this.raiseErrorIf(stmt.sinfo, asgn.valexp === undefined, "cannot clear key in fresh environment creation");

            const etype = this.normalizeTypeOnly((asgn.valexp as [TypeSignature, Expression])[0], env.binds);
            const easgn = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), (asgn.valexp as [TypeSignature, Expression])[1], etype), (asgn.valexp as [TypeSignature, Expression])[1].sinfo, etype);

            return {keyname: asgn.keyname, valexp: [this.toTIRTypeKey(etype), easgn.expressionResult] as [TIRTypeKey, TIRExpression]};
        });

        return [env, [new TIREnvironmentFreshStatement(stmt.sinfo, assigns)]];
    }

    private checkEnvironmentSetStatement(env: StatementTypeEnvironment, stmt: EnvironmentSetStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const assigns = stmt.assigns.map<{keyname: string, valexp: [TIRTypeKey, TIRExpression] | undefined}>((asgn) => {
            this.raiseErrorIf(stmt.sinfo, asgn.valexp === undefined, "cannot clear key in fresh environment creation");

            if(asgn.valexp === undefined) {
                return { keyname: asgn.keyname, valexp: undefined };
            }
            else {
                const etype = this.normalizeTypeOnly((asgn.valexp as [TypeSignature, Expression])[0], env.binds);
                const easgn = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), (asgn.valexp as [TypeSignature, Expression])[1], etype), (asgn.valexp as [TypeSignature, Expression])[1].sinfo, etype);

                return { keyname: asgn.keyname, valexp: [this.toTIRTypeKey(etype), easgn.expressionResult] as [TIRTypeKey, TIRExpression] };
            }
        });

        return [env, [new TIREnvironmentSetStatement(stmt.sinfo, assigns)]];
    }

    private checkEnvironmentSetStatementBracket(env: StatementTypeEnvironment, stmt: EnvironmentSetStatementBracket): [StatementTypeEnvironment, TIRStatement[]] {
        const assigns = stmt.assigns.map<{keyname: string, valexp: [TIRTypeKey, TIRExpression] | undefined}>((asgn) => {
            this.raiseErrorIf(stmt.sinfo, asgn.valexp === undefined, "cannot clear key in fresh environment creation");

            if(asgn.valexp === undefined) {
                return { keyname: asgn.keyname, valexp: undefined };
            }
            else {
                const etype = this.normalizeTypeOnly((asgn.valexp as [TypeSignature, Expression])[0], env.binds);
                const easgn = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), (asgn.valexp as [TypeSignature, Expression])[1], etype), (asgn.valexp as [TypeSignature, Expression])[1].sinfo, etype);

                return { keyname: asgn.keyname, valexp: [this.toTIRTypeKey(etype), easgn.expressionResult] as [TIRTypeKey, TIRExpression] };
            }
        });

        const benv = this.checkScopedBlockStatement(env, stmt.block);
        return [benv[0], [new TIREnvironmentSetStatementBracket(stmt.sinfo, assigns, benv[1], stmt.isFresh)]];
    }

    private checkTaskRunStatement(env: StatementTypeEnvironment, stmt: TaskRunStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk === "no", "This code does not permit task operations (not a task method/action)");

        const [rtask, tirtask, taskdecl] = this.extractTaskInfo(env, stmt.task);
        const execargs = this.checkTaskDeclExecArgs(stmt.sinfo, env, taskdecl, TemplateBindScope.createBaseBindScope(rtask.binds), stmt.taskargs);

        this.raiseErrorIf(stmt.sinfo, stmt.args.length - 1 !== taskdecl.memberFields.length, `expected a field initializer + args`);

        const tfieldsrecord = this.getTaskFieldsInitRecord(rtask);
        const fieldarg = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.args[0], tfieldsrecord), stmt.sinfo, tfieldsrecord);

        this.raiseErrorIf(stmt.sinfo, stmt.args.length - 1 !== taskdecl.mainfunc.invoke.params.length, `expected ${taskdecl.mainfunc.invoke.params.length} arguments for task but got ${stmt.args.length - 1}`);
        const fargs = stmt.args.slice(1).map((arg, ii) => {
            const ptype = this.normalizeTypeOnly(taskdecl.mainfunc.invoke.params[ii].type, TemplateBindScope.createBaseBindScope(rtask.binds));
            return this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), arg, ptype), arg.sinfo, ptype).expressionResult
        });

        const [eenv, vtrgt] = this.checkVTargetOption(stmt.sinfo, env, rtask, stmt.isdefine, stmt.isconst, stmt.vtrgt);
        const trun = new TIRTaskRunStatement(stmt.sinfo, stmt.isdefine, stmt.isconst, vtrgt, tirtask, execargs, {rarg: fieldarg.expressionResult, rtype: this.toTIRTypeKey(tfieldsrecord)}, fargs);
        
        return [eenv, [trun]];
    }

    private checkTaskMultiStatement(env: StatementTypeEnvironment, stmt: TaskMultiStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk === "no", "This code does not permit task operations (not a task method/action)");

        let cenv = env;
        let vtrgts: {name: string, vtype: TIRTypeKey}[] = [];
        let tasks: {task: TIRTypeKey, targs: {argn: string, argv: TIRExpression}[], argtype: TIRTypeKey, consargtype: TIRTypeKey, argexp: TIRExpression}[] = [];

        this.raiseErrorIf(stmt.sinfo, stmt.tasks.length !== stmt.args.length, `expected same number of tasks and argpacks but got ${stmt.tasks.length} and ${stmt.args.length}`);
        for (let i = 0; i < stmt.tasks.length; ++i) {
            const [rtask, tirtask, taskdecl] = this.extractTaskInfo(env, stmt.tasks[i]);
            const execargs = this.checkTaskDeclExecArgs(stmt.sinfo, env, taskdecl, TemplateBindScope.createBaseBindScope(rtask.binds), stmt.taskargs);

            const tfieldsrecord = this.getTaskFieldsInitRecord(rtask);
            const fargtuple = this.getTaskArgsTuple(rtask);
            const aargtype = ResolvedType.createSingle(ResolvedTupleAtomType.create([tfieldsrecord, ...(fargtuple.options[0] as ResolvedTupleAtomType).types]));
            
            const argexp = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.args[i], aargtype), stmt.args[i].sinfo, aargtype);
            const [eenv, vtrgt] = this.checkVTargetOption(stmt.sinfo, env, rtask, stmt.isdefine, stmt.isconst, stmt.vtrgts[i]);

            cenv = eenv;
            vtrgts.push(vtrgt);
            tasks.push({task: tirtask, targs: execargs, argtype: this.toTIRTypeKey(aargtype), consargtype: this.toTIRTypeKey(tfieldsrecord), argexp: argexp.expressionResult});
        }

        const trun = new TIRTaskMultiStatement(stmt.sinfo, stmt.isdefine, stmt.isconst, vtrgts, tasks);
        return [cenv, [trun]];
    }

    private checkTaskDashStatement(env: StatementTypeEnvironment, stmt: TaskDashStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk === "no", "This code does not permit task operations (not a task method/action)");

        let cenv = env;
        let vtrgts: {name: string, vtype: TIRTypeKey, restype: TIRTypeKey}[] = [];
        let tasks: {task: TIRTypeKey, targs: {argn: string, argv: TIRExpression}[], argtype: TIRTypeKey, consargtype: TIRTypeKey, argexp: TIRExpression}[] = [];

        this.raiseErrorIf(stmt.sinfo, stmt.tasks.length !== stmt.args.length, `expected same number of tasks and argpacks but got ${stmt.tasks.length} and ${stmt.args.length}`);
        for (let i = 0; i < stmt.tasks.length; ++i) {
            const [rtask, tirtask, taskdecl] = this.extractTaskInfo(env, stmt.tasks[i]);
            const execargs = this.checkTaskDeclExecArgs(stmt.sinfo, env, taskdecl, TemplateBindScope.createBaseBindScope(rtask.binds), stmt.taskargs);

            const tfieldsrecord = this.getTaskFieldsInitRecord(rtask);
            const fargtuple = this.getTaskArgsTuple(rtask);
            const aargtype = ResolvedType.createSingle(ResolvedTupleAtomType.create([tfieldsrecord, ...(fargtuple.options[0] as ResolvedTupleAtomType).types]));
            
            const argexp = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.args[i], aargtype), stmt.args[i].sinfo, aargtype);
            const [eenv, vtrgt] = this.checkVTargetOptionWithNone(stmt.sinfo, env, rtask, stmt.isdefine, stmt.isconst, stmt.vtrgts[i]);

            cenv = eenv;
            vtrgts.push(vtrgt);
            tasks.push({task: tirtask, targs: execargs, argtype: this.toTIRTypeKey(aargtype), consargtype: this.toTIRTypeKey(tfieldsrecord), argexp: argexp.expressionResult});
        }

        const trun = new TIRTaskDashStatement(stmt.sinfo, stmt.isdefine, stmt.isconst, vtrgts, tasks);
        return [cenv, [trun]];
    }

    private checkTaskAllStatement(env: StatementTypeEnvironment, stmt: TaskAllStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk === "no", "This code does not permit task operations (not a task method/action)");

        const [rtask, tirtask, taskdecl] = this.extractTaskInfo(env, stmt.task);
        const execargs = this.checkTaskDeclExecArgs(stmt.sinfo, env, taskdecl, TemplateBindScope.createBaseBindScope(rtask.binds), stmt.taskargs);

        const tfieldsrecord = this.getTaskFieldsInitRecord(rtask);
        const fargtuple = this.getTaskArgsTuple(rtask);
        const aargtype = ResolvedType.createSingle(ResolvedTupleAtomType.create([tfieldsrecord, ...(fargtuple.options[0] as ResolvedTupleAtomType).types]));
        const aarglist = ResolvedType.createSingle(ResolvedListEntityAtomType.create(this.m_assembly.tryGetObjectTypeForFullyResolvedName("List") as EntityTypeDecl, aargtype));

        const larg = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.arg, aarglist), stmt.arg.sinfo, aarglist);

        const [eenv, vtrgt] = this.checkVTargetOptionWithList(stmt.sinfo, env, rtask, stmt.isdefine, stmt.isconst, stmt.vtrgt);
        const trun = new TIRTaskAllStatement(stmt.sinfo, stmt.isdefine, stmt.isconst, vtrgt, tirtask, execargs, larg.expressionResult, this.toTIRTypeKey(aarglist), this.toTIRTypeKey(aargtype));
        
        return [eenv, [trun]];
    }

    private checkTaskRaceStatement(env: StatementTypeEnvironment, stmt: TaskRaceStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk === "no", "This code does not permit task operations (not a task method/action)");

        const [rtask, tirtask, taskdecl] = this.extractTaskInfo(env, stmt.task);
        const execargs = this.checkTaskDeclExecArgs(stmt.sinfo, env, taskdecl, TemplateBindScope.createBaseBindScope(rtask.binds), stmt.taskargs);

        const tfieldsrecord = this.getTaskFieldsInitRecord(rtask);
        const fargtuple = this.getTaskArgsTuple(rtask);
        const aargtype = ResolvedType.createSingle(ResolvedTupleAtomType.create([tfieldsrecord, ...(fargtuple.options[0] as ResolvedTupleAtomType).types]));
        const aarglist = ResolvedType.createSingle(ResolvedListEntityAtomType.create(this.m_assembly.tryGetObjectTypeForFullyResolvedName("List") as EntityTypeDecl, aargtype));

        const larg = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.arg, aarglist), stmt.arg.sinfo, aarglist);

        const [eenv, vtrgt] = this.checkVTargetOptionWithIndex(stmt.sinfo, env, rtask, stmt.isdefine, stmt.isconst, stmt.vtrgt);
        const trun = new TIRTaskRaceStatement(stmt.sinfo, stmt.isdefine, stmt.isconst, vtrgt, tirtask, execargs, larg.expressionResult, this.toTIRTypeKey(aarglist), this.toTIRTypeKey(aargtype));
        
        return [eenv, [trun]];
    }

    private checkTaskCallWithStatement(env: StatementTypeEnvironment, stmt: TaskCallWithStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return TYPECHECKER_NOT_IMPLEMENTED<[StatementTypeEnvironment, TIRStatement[]]>("TaskCallWithStatement");
    }

    private checkTaskResultWithStatement(env: StatementTypeEnvironment, stmt: TaskResultWithStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return TYPECHECKER_NOT_IMPLEMENTED<[StatementTypeEnvironment, TIRStatement[]]>("TaskResultWithStatement");
    }

    private checkTaskSetStatusStatement(env: StatementTypeEnvironment, stmt: TaskSetStatusStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return TYPECHECKER_NOT_IMPLEMENTED<[StatementTypeEnvironment, TIRStatement[]]>("TaskSetStatusStatement");
    }

    private checkTaskSetSelfFieldStatement(env: StatementTypeEnvironment, stmt: TaskSetSelfFieldStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk !== "write", "This code does not permit task operations (not a task method/action)");
        const tsk = this.m_taskType as {taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType>};
        const tasktype = ResolvedType.createSingle(ResolvedTaskAtomType.create(tsk.taskdecl, tsk.taskbinds));

        const fftry = tsk.taskdecl.memberFields.find((f) => f.name === stmt.fname);
        this.raiseErrorIf(stmt.sinfo, fftry === undefined, `field ${stmt.fname} is not defined on task ${tsk.taskdecl.name}`);
        const ff = fftry as MemberFieldDecl;

        const fftype = this.normalizeTypeOnly(ff.declaredType, TemplateBindScope.createBaseBindScope(tsk.taskbinds));
        const fkey = TIRIDGenerator.generateMemberFieldID(this.toTIRTypeKey(tasktype), stmt.fname);

        const value = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.value, fftype), stmt.value.sinfo, fftype);
        const tset = new TIRTaskSetSelfFieldStatement(stmt.sinfo, this.toTIRTypeKey(tasktype), fkey, stmt.fname, value.expressionResult);

        return [env, [tset]];
    }

    private checkTaskEventEmitStatement(env: StatementTypeEnvironment, stmt: TaskEventEmitStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return TYPECHECKER_NOT_IMPLEMENTED<[StatementTypeEnvironment, TIRStatement[]]>("TaskEventEmitStatement");
    }
*/

    private checkStatement(env: TypeEnvironment, stmt: Statement): TypeEnvironment {
        if(!env.normalflow) {
            this.reportError(stmt.sinfo, "Unreachable code");
            return env;
        }

        switch(stmt.tag) {
            case StatementTag.EmptyStatement: {
                return this.checkEmptyStatement(env, stmt as EmptyStatement);
            }
            case StatementTag.VariableDeclarationStatement: {
                return this.checkVariableDeclarationStatement(env, stmt as VariableDeclarationStatement);
            }
            case StatementTag.VariableMultiDeclarationStatement: {
                return this.checkVariableMultiDeclarationStatement(env, stmt as VariableMultiDeclarationStatement);
            }
            case StatementTag.VariableInitializationStatement: {
                return this.checkVariableInitializationStatement(env, stmt as VariableInitializationStatement);
            }
            case StatementTag.VariableMultiInitializationStatement: {
                return this.checkVariableMultiInitializationStatement(env, stmt as VariableMultiInitializationStatement);
            }
            case StatementTag.VariableAssignmentStatement: {
                return this.checkVariableAssignmentStatement(env, stmt as VariableAssignmentStatement);
            }
            case StatementTag.VariableMultiAssignmentStatement: {
                return this.checkVariableMultiAssignmentStatement(env, stmt as VariableMultiAssignmentStatement);
            }
            case StatementTag.VariableRetypeStatement: {
                return this.checkVariableRetypeStatement(env, stmt as VariableRetypeStatement);
            }
            case StatementTag.ReturnStatement: {
                return this.checkReturnStatement(env, stmt as ReturnStatement);
            }
            case StatementTag.IfStatement: {
                return this.checkIfStatement(env, stmt as IfStatement);
            }
            case StatementTag.IfElseStatement: {
                return this.checkIfElseStatement(env, stmt as IfElseStatement);
            }
            case StatementTag.IfElifElseStatement: {
                return this.checkIfElifElseStatement(env, stmt as IfElifElseStatement);
            }
            case StatementTag.SwitchStatement: {
                return this.checkSwitchStatement(env, stmt as SwitchStatement);
            }
            case StatementTag.MatchStatement: {
                return this.checkMatchStatement(env, stmt as MatchStatement);
            }
            case StatementTag.AbortStatement: {
                return this.checkAbortStatement(env, stmt as AbortStatement);
            }
            case StatementTag.AssertStatement: {
                return this.checkAssertStatement(env, stmt as AssertStatement);
            }
            case StatementTag.ValidateStatement: {
                return this.checkValidateStatement(env, stmt as ValidateStatement);
            }
            case StatementTag.DebugStatement: {
                return this.checkDebugStatement(env, stmt as DebugStatement);
            }
            case StatementTag.VoidRefCallStatement: {
                return this.checkVoidRefCallStatement(env, stmt as VoidRefCallStatement);
            }
            case StatementTag.VarUpdateStatement: {
                return this.checkVarUpdateStatement(env, stmt as VarUpdateStatement);
            }
            case StatementTag.ThisUpdateStatement: {
                return this.checkThisUpdateStatement(env, stmt as ThisUpdateStatement);
            }
            case StatementTag.SelfUpdateStatement: {
                return this.checkSelfUpdateStatement(env, stmt as SelfUpdateStatement);
            }
            case StatementTag.EnvironmentUpdateStatement: {
                return this.checkEnvironmentUpdateStatement(env, stmt as EnvironmentUpdateStatement);
            }
            case StatementTag.EnvironmentBracketStatement: {
                return this.checkEnvironmentBracketStatement(env, stmt as EnvironmentBracketStatement);
            }
            case StatementTag.TaskStatusStatement: {
                return this.checkTaskStatusStatement(env, stmt as TaskStatusStatement);
            }
            case StatementTag.TaskEventEmitStatement: {
                return this.checkTaskEventEmitStatement(env, stmt as TaskEventEmitStatement);
            }
            case StatementTag.TaskYieldStatement: {
                return this.checkTaskYieldStatement(env, stmt as TaskYieldStatement);
            }
            case StatementTag.BlockStatement: {
                return this.checkBlockStatement(env, stmt as BlockStatement);
            }
            default: {
                assert(stmt.tag === StatementTag.ErrorStatement, `Unknown statement kind -- ${stmt.tag}`);

                return env;
            }
        }
    }

    private checkBodyImplementation(env: TypeEnvironment, body: BodyImplementation) {
        if(body instanceof AbstractBodyImplementation || body instanceof PredicateUFBodyImplementation || body instanceof BuiltinBodyImplementation || body instanceof SynthesisBodyImplementation) {
            return;
        }

        if(body instanceof ExpressionBodyImplementation) {
            const etype = this.checkExpression(env, body.exp, env.inferReturn);
            this.checkError(body.sinfo, !this.relations.isSubtypeOf(etype, env.declReturnType, this.constraints), `Expression body does not match expected return type -- expected ${env.declReturnType.tkeystr} but got ${etype.tkeystr}`);
        }
        else {
            assert(body instanceof StandardBodyImplementation);
            

            for(let i = 0; i < body.statements.length; ++i) {
                env = this.checkStatement(env, body.statements[i]);
            }

            this.checkError(body.sinfo, !this.isVoidType(env.declReturnType) && env.normalflow, "Function does not have a return statement in all code paths");
        }
    }

    private checkRequires(env: TypeEnvironment, requires: PreConditionDecl[]) {
        for(let i = 0; i < requires.length; ++i) {
            const precond = requires[i];
            const etype = this.checkExpression(env, precond.exp, undefined);
            this.checkError(precond.sinfo, !this.isBooleanType(etype), `Requires expression does not have a boolean type -- got ${etype.tkeystr}`);
        }
    }

    private checkEnsures(env: TypeEnvironment, refvars: string[], eventtype: TypeSignature | undefined, ensures: PostConditionDecl[]) {
        let eev = env.pushNewLocalScope();
        
        eev = eev.addLocalVar(WELL_KNOWN_RETURN_VAR_NAME, env.declReturnType, true, true);
        if(eventtype !== undefined) {
            const eventlisttype = this.getEventListOf(eventtype);
            eev = eev.addLocalVar(WELL_KNOWN_EVENTS_VAR_NAME, eventlisttype, true, true);
        }

        for(let i = 0; i < refvars.length; ++i) {
            const v = refvars[i];
            eev = eev.addBinder("$" + v, "$" + v, (env.resolveLocalVarInfoFromSrcName(v) as VarInfo).vtype, true, true);
        }

        for(let i = 0; i < ensures.length; ++i) {
            const postcond = ensures[i];
            const etype = this.checkExpression(eev, postcond.exp, undefined);
            this.checkError(postcond.sinfo, !this.isBooleanType(etype), `Ensures expression does not have a boolean type -- got ${etype.tkeystr}`);
        }
    }

    private checkInvariants(bnames: {name: string, type: TypeSignature}[], invariants: InvariantDecl[]) {
        const env = TypeEnvironment.createInitialStdEnv(bnames.map((bn) => new VarInfo("$" + bn.name, "$" + bn.name, bn.type, true, true)), this.getWellKnownType("Bool"), new SimpleTypeInferContext(this.getWellKnownType("Bool")));

        for(let i = 0; i < invariants.length; ++i) {
            const inv = invariants[i];
            const etype = this.checkExpression(env, inv.exp.exp, undefined);
            this.checkError(invariants[i].sinfo, !this.isBooleanType(etype), `Invariant expression does not have a boolean type -- got ${etype.tkeystr}`);
        }
    }

    private checkValidates(bnames: {name: string, type: TypeSignature}[], validates: ValidateDecl[]) {
        const env = TypeEnvironment.createInitialStdEnv(bnames.map((bn) => new VarInfo("$" + bn.name, "$" + bn.name, bn.type, true, true)), this.getWellKnownType("Bool"), new SimpleTypeInferContext(this.getWellKnownType("Bool")));

        for(let i = 0; i < validates.length; ++i) {
            const etype = this.checkExpression(env, validates[i].exp.exp, undefined);
            this.checkError(validates[i].sinfo, !this.isBooleanType(etype), `Validate expression does not have a boolean type -- got ${etype.tkeystr}`);
        }
    }

    private checkExamplesInline(sinfo: SourceInfo, args: TypeSignature[], resulttype: TypeSignature, example: InvokeExampleDeclInline) {
        assert(false, "This should be checked as a BSQON value"); //maybe in a secondary pass
    }

    private checkExamplesFiles(sinfo: SourceInfo, args: TypeSignature[], resulttype: TypeSignature, example: InvokeExampleDeclFile) {
        assert(false, "Not implemented -- checkExamplesFiles"); //We probably don't want to load the contents here -- but maybe as a separate pass????
    }

    private checkExamples(sinfo: SourceInfo, args: TypeSignature[], resulttype: TypeSignature, examples: InvokeExample[]) {
        for(let i = 0; i < examples.length; ++i) {
            const ex = examples[i];
            if(ex instanceof InvokeExampleDeclInline) {
                this.checkExamplesInline(sinfo, args, resulttype, ex);
            }
            else {
                assert(ex instanceof InvokeExampleDeclFile);
                this.checkExamplesFiles(sinfo, args, resulttype, ex);
            }
        }
    }

    private checkExplicitInvokeDeclTermInfo(idecl: ExplicitInvokeDecl) {
        this.checkTemplateTypesOnInvoke(idecl.sinfo, idecl.terms);

        if(idecl.termRestriction !== undefined) {
            assert(false, "Not implemented -- checkExplicitInvokeDeclTermInfo"); //make sure it is well formed
        }
    }

    private checkExplicitInvokeDeclSignature(idecl: ExplicitInvokeDecl, specialvinfo: VarInfo[]) {
        let argnames = new Set<string>();
        const fullvinfo = [...specialvinfo, ...idecl.params.map((p) => new VarInfo(p.name, p.name, p.type, !p.isRefParam, true))];
        for(let i = 0; i < idecl.params.length; ++i) {
            const p = idecl.params[i];
            this.checkError(idecl.sinfo, argnames.has(p.name), `Duplicate parameter name ${p.name}`);
            argnames.add(p.name);

            const tok = this.checkTypeSignature(p.type);
            if(tok && p.optDefaultValue !== undefined) {
                const env = TypeEnvironment.createInitialStdEnv(fullvinfo, idecl.resultType, new SimpleTypeInferContext(idecl.resultType));
                const etype = this.checkExpression(env, p.optDefaultValue.exp, p.type);

                this.checkError(idecl.sinfo, !(etype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(etype, p.type, this.constraints), `Default value does not match declared type -- expected ${p.type.tkeystr} but got ${etype.tkeystr}`);
            }
        }

        this.checkTypeSignature(idecl.resultType);
    }

    private checkExplicitInvokeDeclMetaData(idecl: ExplicitInvokeDecl, specialvinfo: VarInfo[], specialrefvars: string[], eventtype: TypeSignature | undefined) {
        const fullvinfo = [...specialvinfo, ...idecl.params.map((p) => new VarInfo(p.name, p.name, p.type, !p.isRefParam, true))];
        const fullrefvars = [...specialrefvars, ...idecl.params.filter((p) => p.isRefParam).map((p) => p.name)];

        const ienv = TypeEnvironment.createInitialStdEnv(fullvinfo, this.getWellKnownType("Bool"), new SimpleTypeInferContext(this.getWellKnownType("Bool")));
        this.checkRequires(ienv, idecl.preconditions);
        this.checkEnsures(ienv, fullrefvars, eventtype, idecl.postconditions);

        this.checkExamples(idecl.sinfo, idecl.params.map((p) => p.type), idecl.resultType, idecl.examples);
    }

    private checkNamespaceFunctionDecls(fdecls: NamespaceFunctionDecl[]) {
        for(let i = 0; i < fdecls.length; ++i) {
            const fdecl = fdecls[i];
    
            this.file = fdecl.file;
            this.checkExplicitInvokeDeclTermInfo(fdecl);

            if(fdecl.terms.length !== 0) {
                this.constraints.pushConstraintScope(fdecl.terms);
            }

            this.checkExplicitInvokeDeclSignature(fdecl, []);
            this.checkExplicitInvokeDeclMetaData(fdecl, [], [], undefined);

            const infertype = this.relations.convertTypeSignatureToTypeInferCtx(fdecl.resultType, this.constraints);
            const env = TypeEnvironment.createInitialStdEnv(fdecl.params.map((p) => new VarInfo(p.name, p.name, p.type, !p.isRefParam, true)), fdecl.resultType, infertype);
            this.checkBodyImplementation(env, fdecl.body);

            if(fdecl.terms.length !== 0) {
                this.constraints.popConstraintScope();
            }

            this.file = CLEAR_FILENAME;
        }
    }

    private checkTypeFunctionDecls(tdecl: AbstractNominalTypeDecl, fdecls: TypeFunctionDecl[]) {
        for(let i = 0; i < fdecls.length; ++i) {
            const fdecl = fdecls[i];
    
            this.checkExplicitInvokeDeclTermInfo(fdecl);

            if(fdecl.terms.length !== 0) {
                this.constraints.pushConstraintScope(fdecl.terms);
            }

            this.checkExplicitInvokeDeclSignature(fdecl, []);
            this.checkExplicitInvokeDeclMetaData(fdecl, [], [], undefined);

            const infertype = this.relations.convertTypeSignatureToTypeInferCtx(fdecl.resultType, this.constraints);
            const env = TypeEnvironment.createInitialStdEnv(fdecl.params.map((p) => new VarInfo(p.name, p.name, p.type, !p.isRefParam, true)), fdecl.resultType, infertype);
            this.checkBodyImplementation(env, fdecl.body);

            if(fdecl.terms.length !== 0) {
                this.constraints.popConstraintScope();
            }
        }
    }

    private checkMethodDecls(tdecl: AbstractNominalTypeDecl, rcvr: TypeSignature, mdecls: MethodDecl[]) {
        for(let i = 0; i < mdecls.length; ++i) {   
            assert(false, "Not implemented -- checkMethodDecl");
        }
    }

    private checkTaskMethodDecls(tdecl: AbstractNominalTypeDecl, rcvr: TypeSignature, mdecls: TaskMethodDecl[]) {
        for(let i = 0; i < mdecls.length; ++i) {
            assert(false, "Not implemented -- checkTaskMethodDecl");
        }
    }

    private checkTaskActionDecls(tdecl: AbstractNominalTypeDecl, rcvr: TypeSignature, mdecls: TaskActionDecl[]) {
        for(let i = 0; i < mdecls.length; ++i) {
            assert(false, "Not implemented -- checkTaskActionDecl");
        }
    }

    private checkConstMemberDecls(tdecl: AbstractNominalTypeDecl, mdecls: ConstMemberDecl[]) {
        for(let i = 0; i < mdecls.length; ++i) {
            const m = mdecls[i];

            if(this.checkTypeSignature(m.declaredType)) {
                const infertype = this.relations.convertTypeSignatureToTypeInferCtx(m.declaredType, this.constraints);
                const env = TypeEnvironment.createInitialStdEnv([], m.declaredType, infertype);

                const decltype = this.checkExpression(env, m.value.exp, new SimpleTypeInferContext(m.declaredType));
                this.checkError(m.sinfo, !this.relations.isSubtypeOf(decltype, m.declaredType, this.constraints), `Const initializer does not match declared type -- expected ${m.declaredType.tkeystr} but got ${decltype.tkeystr}`);
            }
        }
    }

    private checkMemberFieldDecls(bnames: {name: string, type: TypeSignature}[], fdecls: MemberFieldDecl[]) {
        for(let i = 0; i < fdecls.length; ++i) {
            const f = fdecls[i];
            
            if(this.checkTypeSignature(f.declaredType)) {
                if(f.defaultValue !== undefined) {
                    const infertype = this.relations.convertTypeSignatureToTypeInferCtx(f.declaredType, this.constraints);
                    const env = TypeEnvironment.createInitialStdEnv(bnames.map((bn) => new VarInfo("$" + bn.name, "$" + bn.name, bn.type, true, true)), f.declaredType, infertype);

                    const decltype = this.checkExpression(env, f.defaultValue.exp, new SimpleTypeInferContext(f.declaredType));
                    this.checkError(f.sinfo, !this.relations.isSubtypeOf(decltype, f.declaredType, this.constraints), `Field initializer does not match declared type -- expected ${f.declaredType.tkeystr} but got ${decltype.tkeystr}`);
                }
            }
        }
    }

    private checkProvides(provides: TypeSignature[]) {
        for(let i = 0; i < provides.length; ++i) {
            const p = provides[i];
            this.checkTypeSignature(p);

            if(!this.relations.isValidProvidesType(p)) {
                this.reportError(p.sinfo, `Invalid provides type -- ${p.tkeystr}`);
            }
        }
    }

    private checkAbstractNominalTypeDeclVCallAndInheritance(tdecl: AbstractNominalTypeDecl, optfdecls: MemberFieldDecl[] | undefined, isentity: boolean) {
        ////
        //TODO: Check that there are no name collisions on inhertied members and members in this
        //TODO: Check that all of the vcall resolves are unique .... and all of the vcall decls are implemented (depending on isentity)
        ////
    }

    private checkAbstractNominalTypeDeclHelper(bnames: {name: string, type: TypeSignature}[], rcvr: TypeSignature, tdecl: AbstractNominalTypeDecl, optfdecls: MemberFieldDecl[] | undefined, isentity: boolean) {
        this.file = tdecl.file;
        this.checkTemplateTypesOnType(tdecl.sinfo, tdecl.terms);

        if(tdecl.terms.length !== 0) {
            this.constraints.pushConstraintScope(tdecl.terms);
        }

        this.checkProvides(tdecl.provides);

        //make sure all of the invariants on this typecheck
        this.checkInvariants(bnames, tdecl.invariants);
        this.checkValidates(bnames, tdecl.validates);
        
        this.checkConstMemberDecls(tdecl, tdecl.consts);
        this.checkTypeFunctionDecls(tdecl, tdecl.functions);
        this.checkMethodDecls(tdecl, rcvr, tdecl.methods);

        if(optfdecls !== undefined) {
            this.checkMemberFieldDecls(bnames, optfdecls);
        }

        this.checkAbstractNominalTypeDeclVCallAndInheritance(tdecl, optfdecls, isentity);

        if(tdecl.terms.length !== 0) {
            this.constraints.popConstraintScope();
        }
        this.file = CLEAR_FILENAME;
    }

    private checkEnumTypeDecl(ns: NamespaceDeclaration, tdecl: EnumTypeDecl) {
        this.file = tdecl.file;
        this.checkError(tdecl.sinfo, tdecl.terms.length !== 0, "Enums cannot have template terms");
        
        this.checkProvides(tdecl.provides);
 
        //Make sure that any provides types are not adding on fields, consts, or functions
        const etype = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        const providesdecls = this.relations.resolveTransitiveProvidesDecls(etype, this.constraints);
        for(let i = 0; i < providesdecls.length; ++i) {
            const pdecl = providesdecls[i];
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).fields.length !== 0, `Provides type cannot have member fields -- ${pdecl.tsig.decl.name}`);
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).invariants.length !== 0 || (pdecl.tsig.decl as ConceptTypeDecl).validates.length !== 0, `Provides type cannot have invariants -- ${pdecl.tsig.decl.name}`);
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).consts.length !== 0, `Provides type cannot have consts -- ${pdecl.tsig.decl.name}`);
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).functions.length !== 0, `Provides type cannot have functions -- ${pdecl.tsig.decl.name}`);
        }

        this.checkError(tdecl.sinfo, tdecl.invariants.length !== 0 || tdecl.validates.length !== 0, "Enums cannot have invariants");

        this.checkError(tdecl.sinfo, tdecl.consts.length !== 0, "Enums cannot have consts");
        this.checkError(tdecl.sinfo, tdecl.functions.length !== 0, "Enums cannot have functions");

        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        this.checkMethodDecls(tdecl, rcvr, tdecl.methods);

        this.checkAbstractNominalTypeDeclVCallAndInheritance(tdecl, [], true);

        let opts = new Set<string>();
        for(let i = 0; i < tdecl.members.length; ++i) {
            this.checkError(tdecl.sinfo, opts.has(tdecl.members[i]), `Duplicate enum option ${tdecl.members[i]}`);
            opts.add(tdecl.members[i]);
        }
        this.file = CLEAR_FILENAME;
    }

    private checkTypedeclTypeDecl(ns: NamespaceDeclaration, tdecl: TypedeclTypeDecl, isentity: boolean) {
        this.file = tdecl.file;
        this.checkTemplateTypesOnType(tdecl.sinfo, tdecl.terms);

        if(tdecl.terms.length !== 0) {
            this.constraints.pushConstraintScope(tdecl.terms);
        }

        this.checkProvides(tdecl.provides);

        //Make sure that any provides types are not adding on fields!
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const providesdecls = this.relations.resolveTransitiveProvidesDecls(rcvr, this.constraints);
        for(let i = 0; i < providesdecls.length; ++i) {
            const pdecl = providesdecls[i];
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).fields.length !== 0, `Provides type cannot have member fields -- ${pdecl.tsig.decl.name}`);
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).invariants.length !== 0 || (pdecl.tsig.decl as ConceptTypeDecl).validates.length !== 0, `Provides type cannot have invariants -- ${pdecl.tsig.decl.name}`);
        }

        if(this.checkTypeSignature(tdecl.valuetype)) {
            //make sure the base type is typedeclable
            this.checkError(tdecl.sinfo, this.relations.isTypedeclableType(tdecl.valuetype), `Base type is not typedeclable -- ${tdecl.valuetype.tkeystr}`);

            //make sure all of the invariants on this typecheck
            this.checkInvariants([{name: "value", type: tdecl.valuetype}], tdecl.invariants);
            this.checkValidates([{name: "value", type: tdecl.valuetype}], tdecl.validates);
        }
        
        this.checkConstMemberDecls(tdecl, tdecl.consts);
        this.checkTypeFunctionDecls(tdecl, tdecl.functions);

        this.checkMethodDecls(tdecl, rcvr, tdecl.methods);
        this.checkAbstractNominalTypeDeclVCallAndInheritance(tdecl, [], isentity);

        if(tdecl.terms.length !== 0) {
            this.constraints.popConstraintScope();
        }
        this.file = CLEAR_FILENAME;
    }

    private checkInteralSimpleTypeDeclHelper(ns: NamespaceDeclaration, tdecl: InternalEntityTypeDecl, isentity: boolean) {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        this.checkAbstractNominalTypeDeclHelper([], rcvr, tdecl, undefined, isentity);
    }

    private checkPrimitiveEntityTypeDecl(ns: NamespaceDeclaration, tdecl: PrimitiveEntityTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkRegexValidatorTypeDecl(ns: NamespaceDeclaration, tdecl: RegexValidatorTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkCRegexValidatorTypeDecl(ns: NamespaceDeclaration, tdecl: CRegexValidatorTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkPathValidatorTypeDecl(ns: NamespaceDeclaration, tdecl: PathValidatorTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);

        assert(false, "Not implemented -- checkPathValidatorTypeDecl");
    }

    private checkStringOfTypeDecl(ns: NamespaceDeclaration, tdecl: StringOfTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkCStringOfTypeDecl(ns: NamespaceDeclaration, tdecl: CStringOfTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkPathOfTypeDecl(ns: NamespaceDeclaration, tdecl: PathOfTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkPathFragmentOfTypeDecl(ns: NamespaceDeclaration, tdecl: PathFragmentOfTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkPathGlobOfTypeDecl(ns: NamespaceDeclaration, tdecl: PathGlobOfTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkOkTypeDecl(ns: NamespaceDeclaration, tdecl: OkTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true)
    }

    private checkErrTypeDecl(ns: NamespaceDeclaration, tdecl: ErrTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkAPIRejectedTypeDecl(ns: NamespaceDeclaration, tdecl: APIRejectedTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkAPIFailedTypeDecl(ns: NamespaceDeclaration, tdecl: APIFailedTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkAPIErrorTypeDecl(ns: NamespaceDeclaration, tdecl: APIErrorTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkAPISuccessTypeDecl(ns: NamespaceDeclaration, tdecl: APISuccessTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkSomeTypeDecl(ns: NamespaceDeclaration, tdecl: SomeTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkPairTypeDecl(ns: NamespaceDeclaration, tdecl: MapEntryTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkMapEntryTypeDecl(ns: NamespaceDeclaration, tdecl: MapEntryTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkListTypeDecl(ns: NamespaceDeclaration, tdecl: ListTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkStackTypeDecl(ns: NamespaceDeclaration, tdecl: StackTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkQueueTypeDecl(ns: NamespaceDeclaration, tdecl: QueueTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkSetTypeDecl(ns: NamespaceDeclaration, tdecl: SetTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkMapTypeDecl(ns: NamespaceDeclaration, tdecl: MapTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkEventListTypeDecl(ns: NamespaceDeclaration, tdecl: EventListTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkEntityTypeDecl(ns: NamespaceDeclaration, tdecl: EntityTypeDecl) {
        this.file = tdecl.file;
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = this.relations.generateAllFieldBNamesInfo(rcvr, this.constraints, tdecl.fields);

        this.checkAbstractNominalTypeDeclHelper(bnames, rcvr, tdecl, tdecl.fields, true);
        this.file = CLEAR_FILENAME;
    }

    private checkPrimitiveConceptTypeDecl(ns: NamespaceDeclaration, tdecl: PrimitiveConceptTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, false);
    }

    private checkOptionTypeDecl(ns: NamespaceDeclaration, tdecl: OptionTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, false);
    }

    private checkResultTypeDecl(ns: NamespaceDeclaration, tdecl: ResultTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, false);

        this.constraints.pushConstraintScope(tdecl.terms);
        for(let i = 0; i < tdecl.nestedEntityDecls.length; ++i) {
            const ned = tdecl.nestedEntityDecls[i];
            if(ned instanceof OkTypeDecl) {
                this.checkOkTypeDecl(ns, ned);
            }
            else {
                this.checkErrTypeDecl(ns, ned as ErrTypeDecl);
            }
        }
        this.constraints.popConstraintScope();
    }

    private checkAPIResultTypeDecl(ns: NamespaceDeclaration, tdecl: APIResultTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, false);

        this.constraints.pushConstraintScope(tdecl.terms);
        for(let i = 0; i < tdecl.nestedEntityDecls.length; ++i) {
            const ned = tdecl.nestedEntityDecls[i];
            if(ned instanceof APIRejectedTypeDecl) {
                this.checkAPIRejectedTypeDecl(ns, ned);
            }
            else if(ned instanceof APIFailedTypeDecl) {
                this.checkAPIFailedTypeDecl(ns, ned);
            }
            else if(ned instanceof APIErrorTypeDecl) {
                this.checkAPIErrorTypeDecl(ns, ned);
            }
            else {
                this.checkAPISuccessTypeDecl(ns, ned as APISuccessTypeDecl);
            }
        }
        this.constraints.popConstraintScope();
    }

    private checkExpandoableTypeDecl(ns: NamespaceDeclaration, tdecl: ExpandoableTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, false);
    }

    private checkConceptTypeDecl(ns: NamespaceDeclaration, tdecl: ConceptTypeDecl) {
        this.file = tdecl.file;
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = this.relations.generateAllFieldBNamesInfo(rcvr, this.constraints, tdecl.fields);

        this.checkAbstractNominalTypeDeclHelper(bnames, rcvr, tdecl, tdecl.fields, false);
        this.file = CLEAR_FILENAME;
    }

    private checkDatatypeMemberEntityTypeDecl(ns: NamespaceDeclaration, parent: DatatypeTypeDecl, tdecl: DatatypeMemberEntityTypeDecl) {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = this.relations.generateAllFieldBNamesInfo(rcvr, this.constraints, tdecl.fields);

        this.checkAbstractNominalTypeDeclHelper(bnames, rcvr, tdecl, tdecl.fields, true);
    }

    private checkDatatypeTypeDecl(ns: NamespaceDeclaration, tdecl: DatatypeTypeDecl) {
        this.file = tdecl.file;
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = this.relations.generateAllFieldBNamesInfo(rcvr, this.constraints, tdecl.fields);

        this.checkAbstractNominalTypeDeclHelper(bnames, rcvr, tdecl, tdecl.fields, true);

        for(let i = 0; i < tdecl.associatedMemberEntityDecls.length; ++i) {
            this.checkDatatypeMemberEntityTypeDecl(ns, tdecl, tdecl.associatedMemberEntityDecls[i]);
        }
        this.file = CLEAR_FILENAME;
    }

    private checkEventInfo(einfo: TypeSignature) {
        const oksig = this.checkTypeSignature(einfo);
        if(oksig) {
            this.checkError(einfo.sinfo, !this.relations.isEventDataType(einfo), `Event type is not a valid event type -- ${einfo.tkeystr}`);
        }
    }

    private checkStatusInfo(sinfo: TypeSignature[]) {
        for(let i = 0; i < sinfo.length; ++i) {
            const oksig = this.checkTypeSignature(sinfo[i]);
            if(oksig) {
                this.checkError(sinfo[i].sinfo, !this.relations.isStatusDataType(sinfo[i]), `Event type is not a valid status type -- ${sinfo[i].tkeystr}`);
            }
        }
    }

    private checkEnvironmentVariableInformation(env: EnvironmentVariableInformation[]) {
        for(let i = 0; i < env.length; ++i) {
            assert(false, "Not implemented -- checkEnvironmentVariableInformation");
        }
    }

    private checkResourceInformation(res: ResourceInformation[] | "**" | "{}" | "?") {
        if(res === "**" || res === "{}" || res === "?") {
            return;
        }

        for(let i = 0; i < res.length; ++i) {
            assert(false, "Not implemented -- checkResourceInformation");
        }
    }

    private checkAPIDecl(adecl: APIDecl) {
        assert(false, "Not implemented -- checkAPIDecl");
    }

    private checkTaskDecl(ns: NamespaceDeclaration, tdecl: TaskDecl) {
        this.file = tdecl.file;
        this.checkTemplateTypesOnType(tdecl.sinfo, tdecl.terms);

        if(tdecl.terms.length !== 0) {
            this.constraints.pushConstraintScope(tdecl.terms);
        }

        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = tdecl.fields.map((f) => { return {name: f.name, type: f.declaredType}; });

        //make sure all of the invariants on this typecheck
        this.checkInvariants(bnames, tdecl.invariants);
        this.checkValidates(bnames, tdecl.validates);
        
        this.checkConstMemberDecls(tdecl, tdecl.consts);
        this.checkTypeFunctionDecls(tdecl, tdecl.functions);
        this.checkTaskMethodDecls(tdecl, rcvr, tdecl.selfmethods);
        this.checkTaskActionDecls(tdecl, rcvr, tdecl.actions);

        this.checkMemberFieldDecls(bnames, tdecl.fields);

        if(tdecl.implementsapi !== undefined) {
            assert(false, "Not implemented -- checkTaskDecl implementsapi");
        }
        else {
            if(tdecl.eventsInfo !== undefined) {
                this.checkEventInfo(tdecl.eventsInfo as TypeSignature);
            }
            if(tdecl.statusInfo !== undefined) {
                this.checkStatusInfo(tdecl.statusInfo as TypeSignature[]);
            }
            if(tdecl.envVarRequirementInfo !== undefined) {
                this.checkEnvironmentVariableInformation(tdecl.envVarRequirementInfo as EnvironmentVariableInformation[]);
            }
            if(tdecl.resourceImpactInfo !== undefined) {
                this.checkResourceInformation(tdecl.resourceImpactInfo as ResourceInformation[] | "**" | "{}" | "?");
            }
        }

        if(tdecl.terms.length !== 0) {
            this.constraints.popConstraintScope();
        }
        this.file = CLEAR_FILENAME;
    }

    private checkNamespaceConstDecls(cdecls: NamespaceConstDecl[]) {
        for(let i = 0; i < cdecls.length; ++i) {
            const m = cdecls[i];

            this.file = m.file;
            if(this.checkTypeSignature(m.declaredType)) {
                const infertype = this.relations.convertTypeSignatureToTypeInferCtx(m.declaredType, this.constraints);
                const decltype = this.checkExpression(TypeEnvironment.createInitialStdEnv([], m.declaredType, infertype), m.value.exp, m.declaredType);

                this.checkError(m.sinfo, !this.relations.isSubtypeOf(decltype, m.declaredType, this.constraints), `Const initializer does not match declared type -- expected ${m.declaredType.tkeystr} but got ${decltype.tkeystr}`);
            }
            this.file = CLEAR_FILENAME;
        }
    }

    private checkNamespaceTypeDecls(ns: NamespaceDeclaration, tdecl: AbstractNominalTypeDecl[]) {
        for(let i = 0; i < tdecl.length; ++i) {
            const tt = tdecl[i];

            if(tt instanceof EnumTypeDecl) {
                this.checkEnumTypeDecl(ns, tt);
            }
            else if(tt instanceof TypedeclTypeDecl) {
                this.checkTypedeclTypeDecl(ns, tt, true);
            }
            else if(tt instanceof PrimitiveEntityTypeDecl) {
                this.checkPrimitiveEntityTypeDecl(ns, tt);
            }
            else if(tt instanceof RegexValidatorTypeDecl) {
                this.checkRegexValidatorTypeDecl(ns, tt);
            }
            else if(tt instanceof CRegexValidatorTypeDecl) {
                this.checkCRegexValidatorTypeDecl(ns, tt);
            }
            else if(tt instanceof PathValidatorTypeDecl) {
                this.checkPathValidatorTypeDecl(ns, tt);
            }
            else if(tt instanceof StringOfTypeDecl) {
                this.checkStringOfTypeDecl(ns, tt);
            }
            else if(tt instanceof CStringOfTypeDecl) {
                this.checkCStringOfTypeDecl(ns, tt);
            }
            else if(tt instanceof PathOfTypeDecl) {
                this.checkPathOfTypeDecl(ns, tt);
            }
            else if(tt instanceof PathFragmentOfTypeDecl) {
                this.checkPathFragmentOfTypeDecl(ns, tt);
            }
            else if(tt instanceof PathGlobOfTypeDecl) {
                this.checkPathGlobOfTypeDecl(ns, tt);
            }
            else if(tt instanceof OkTypeDecl) {
                this.checkOkTypeDecl(ns, tt);
            }
            else if(tt instanceof ErrTypeDecl) {
                this.checkErrTypeDecl(ns, tt);
            }
            else if(tt instanceof APIRejectedTypeDecl) {
                this.checkAPIRejectedTypeDecl(ns, tt);
            }
            else if(tt instanceof APIFailedTypeDecl) {
                this.checkAPIFailedTypeDecl(ns, tt);
            }
            else if(tt instanceof APIErrorTypeDecl) {
                this.checkAPIErrorTypeDecl(ns, tt);
            }
            else if(tt instanceof APISuccessTypeDecl) {
                this.checkAPISuccessTypeDecl(ns, tt);
            }
            else if(tt instanceof SomeTypeDecl) {
                this.checkSomeTypeDecl(ns, tt);
            }
            else if(tt instanceof PairTypeDecl) {
                this.checkPairTypeDecl(ns, tt);
            }
            else if(tt instanceof MapEntryTypeDecl) {
                this.checkMapEntryTypeDecl(ns, tt);
            }
            else if(tt instanceof ListTypeDecl) {
                this.checkListTypeDecl(ns, tt);
            }
            else if(tt instanceof StackTypeDecl) {
                this.checkStackTypeDecl(ns, tt);
            }
            else if(tt instanceof QueueTypeDecl) {
                this.checkQueueTypeDecl(ns, tt);
            }
            else if(tt instanceof SetTypeDecl) {
                this.checkSetTypeDecl(ns, tt);
            }
            else if(tt instanceof MapTypeDecl) {
                this.checkMapTypeDecl(ns, tt);
            }
            else if(tt instanceof EventListTypeDecl) {
                this.checkEventListTypeDecl(ns, tt);
            }
            else if(tt instanceof EntityTypeDecl) {
                this.checkEntityTypeDecl(ns, tt);
            }
            else if(tt instanceof PrimitiveConceptTypeDecl) {
                this.checkPrimitiveConceptTypeDecl(ns, tt);
            }
            else if(tt instanceof OptionTypeDecl) {
                this.checkOptionTypeDecl(ns, tt);
            }
            else if(tt instanceof ResultTypeDecl) {
                this.checkResultTypeDecl(ns, tt);
            }
            else if(tt instanceof APIResultTypeDecl) {
                this.checkAPIResultTypeDecl(ns, tt);
            }
            else if(tt instanceof ExpandoableTypeDecl) {
                this.checkExpandoableTypeDecl(ns, tt);
            }
            else if(tt instanceof ConceptTypeDecl) {
                this.checkConceptTypeDecl(ns, tt);
            }
            else if(tt instanceof DatatypeTypeDecl) {
                this.checkDatatypeTypeDecl(ns, tt);
            }
            else {
                assert(false, "Unknown type decl kind");
            }
        }
    }

    private checkNamespaceDeclaration(decl: NamespaceDeclaration) {
        //all usings should be resolved and valid so nothing to do there

        this.ns = decl.fullnamespace;

        this.checkNamespaceConstDecls(decl.consts);
        this.checkNamespaceFunctionDecls(decl.functions);
        this.checkNamespaceTypeDecls(decl, decl.typedecls);

        for(let i = 0; i < decl.apis.length; ++i) {
            this.checkAPIDecl(decl.apis[i]);
        }

        for(let i = 0; i < decl.tasks.length; ++i) {
            this.checkTaskDecl(decl, decl.tasks[i]);
        }

        for(let i = 0; i < decl.subns.length; ++i) {
            this.checkNamespaceDeclaration(decl.subns[i]);
        }
    }

    private tryReduceConstantExpressionToRE(exp: Expression): LiteralRegexExpression | undefined {
        if(exp instanceof LiteralRegexExpression) {
            return exp;
        }
        else if (exp instanceof AccessNamespaceConstantExpression) {
            const nsresl = this.relations.resolveNamespaceConstant(exp.ns, exp.name);
            if(nsresl === undefined) {
                return undefined;
            }

            return this.tryReduceConstantExpressionToRE(nsresl.value.exp);
        }
        else {
            return undefined;
        }
    }

    private loadConstantsAndValidatorREs(nsdecl: NamespaceDeclaration): NSRegexInfo[] {
        const inns = nsdecl.fullnamespace.ns.join("::");
        const nsmappings = nsdecl.usings.filter((u) => u.asns !== undefined).map((u) => [u.fromns.emit(), u.asns as string] as [string, string]);
        const nsinfo: NSRegexNameInfo = {inns: inns, nsmappings: nsmappings};

        const reinfos: NSRegexREInfoEntry[] = [];
        nsdecl.typedecls.forEach((td) => {
            if(td instanceof RegexValidatorTypeDecl) {
                reinfos.push({name: td.name, restr: td.regex});
            }
            if(td instanceof CRegexValidatorTypeDecl) {
                reinfos.push({name: td.name, restr: td.regex});
            }
        });
        nsdecl.consts.forEach((c) => {
            const re = this.tryReduceConstantExpressionToRE(c.value.exp);
            if(re !== undefined) {
                reinfos.push({name: c.name, restr: re.value});
            }
        });

        const subnsinfo = nsdecl.subns.flatMap((ns) => this.loadConstantsAndValidatorREs(ns));

        return [{nsinfo: nsinfo, reinfos:  reinfos}, ...subnsinfo];
    }

    private processConstsAndValidatorREs(assembly: Assembly) {
        const asmreinfo = assembly.toplevelNamespaces.flatMap((ns) => this.loadConstantsAndValidatorREs(ns));

        //Now process the regexs
        loadConstAndValidateRESystem(asmreinfo);
    }

    private static loadWellKnownType(assembly: Assembly, name: string, wellknownTypes: Map<string, TypeSignature>) {
        const ccore = assembly.getCoreNamespace();

        const tdecl = ccore.typedecls.find((td) => td.name === name);
        assert(tdecl !== undefined, "Failed to find well known type");

        wellknownTypes.set(name, new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []));
    }

    static checkAssembly(assembly: Assembly): TypeError[] {
        let wellknownTypes: Map<string, TypeSignature> = new Map<string, TypeSignature>();
        wellknownTypes.set("Void", new VoidTypeSignature(SourceInfo.implicitSourceInfo()));

        TypeChecker.loadWellKnownType(assembly, "Any", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "KeyType", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Comparable", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "LinearArithmetic", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Numeric", wellknownTypes);

        TypeChecker.loadWellKnownType(assembly, "None", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Some", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Bool", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Int", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Nat", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "BigInt", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "BigNat", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Rational", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Float", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Decimal", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "DecimalDegree", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "LatLongCoordinate", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Complex", wellknownTypes);

        TypeChecker.loadWellKnownType(assembly, "TemplateString", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "TemplateCString", wellknownTypes);

        TypeChecker.loadWellKnownType(assembly, "RegexValidator", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "CRegexValidator", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "PathValidator", wellknownTypes);

        TypeChecker.loadWellKnownType(assembly, "String", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "CString", wellknownTypes);

        const checker = new TypeChecker(new TemplateConstraintScope(), new TypeCheckerRelations(assembly, wellknownTypes));

        //Gather all the const and validator regexs, make sure they are valid and generate the compiled versions
        checker.processConstsAndValidatorREs(assembly);

        //Type-check each of the assemblies
        for(let i = 0; i < assembly.toplevelNamespaces.length; ++i) {
            checker.checkNamespaceDeclaration(assembly.toplevelNamespaces[i]);
        }

        return checker.errors;
    }
}

export { TypeError, TypeChecker };
