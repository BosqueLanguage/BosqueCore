import assert from "node:assert";

import { APIDecl, APIErrorTypeDecl, APIRejectedTypeDecl, APIResultTypeDecl, APISuccessTypeDecl, AbstractNominalTypeDecl, Assembly, ConceptTypeDecl, ConstMemberDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, EntityTypeDecl, EnumTypeDecl, EnvironmentVariableInformation, FailTypeDecl, EventListTypeDecl, ExplicitInvokeDecl, InternalEntityTypeDecl, InvariantDecl, InvokeTemplateTermDecl, ListTypeDecl, MapEntryTypeDecl, MapTypeDecl, MemberFieldDecl, MethodDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, OkTypeDecl, OptionTypeDecl, PostConditionDecl, PreConditionDecl, PrimitiveEntityTypeDecl, QueueTypeDecl, ResourceInformation, ResultTypeDecl, SetTypeDecl, StackTypeDecl, TaskActionDecl, TaskDecl, TaskMethodDecl, TypeFunctionDecl, TypeTemplateTermDecl, TypedeclTypeDecl, ValidateDecl, WELL_KNOWN_EVENTS_VAR_NAME, WELL_KNOWN_RETURN_VAR_NAME, TemplateTermDeclExtraTag, SomeTypeDecl, InvokeParameterDecl, MAX_SAFE_NAT, MIN_SAFE_INT, MAX_SAFE_INT, InvokeTemplateTypeRestrictionClause, MAX_SAFE_CHK_NAT, MIN_SAFE_CHK_INT, MAX_SAFE_CHK_INT } from "./assembly.js";
import { CodeFormatter, SourceInfo } from "./build_decls.js";
import { AutoTypeSignature, EListTypeSignature, ErrorTypeSignature, FormatStringTypeSignature, LambdaParameterSignature, LambdaTypeSignature, NominalTypeSignature, TemplateConstraintScope, TemplateNameMapper, TemplateTypeSignature, TypeSignature, VoidTypeSignature } from "./type.js";
import { AbortStatement, AbstractBodyImplementation, AccessEnumExpression, AccessEnvValueExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, ArgumentValue, AssertStatement, BaseRValueExpression, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinMultExpression, BinSubExpression, BinderInfo, BlockStatement, BodyImplementation, BuiltinBodyImplementation, CallNamespaceFunctionExpression, CallRefInvokeExpression, CallRefSelfExpression, CallRefThisExpression, CallRefVariableExpression, CallTaskActionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, DebugStatement, EmptyStatement, Expression, ExpressionBodyImplementation, ExpressionTag, FormatStringArgComponent, FormatStringComponent, FormatStringTextComponent, HoleBodyImplementation, ITest, ITestDenied, ITestError, ITestFail, ITestFlagged, ITestNone, ITestOk, ITestRejected, ITestSome, ITestSuccess, ITestType, IfElifElseStatement, IfElseStatement, IfStatement, KeyCompareEqExpression, KeyCompareLessExpression, LambdaInvokeExpression, LiteralCStringExpression, LiteralFormatCStringExpression, LiteralFormatStringExpression, LiteralNoneExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralStringExpression, LiteralTypeDeclValueExpression, LiteralTypedCStringExpression, LiteralTypedFormatCStringExpression, LiteralTypedFormatStringExpression, LiteralTypedStringExpression, LogicAndExpression, LogicOrExpression, MapEntryConstructorExpression, MatchStatement, NamedArgumentValue, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PositionalArgumentValue, PostfixAccessFromIndex, PostfixAccessFromName, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixOp, PostfixOpTag, PostfixProjectFromNames, PredicateUFBodyImplementation, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, RValueExpression, RValueExpressionTag, ReturnMultiStatement, ReturnSingleStatement, ReturnVoidStatement, SelfUpdateStatement, SpecialConstructorExpression, SpreadArgumentValue, StandardBodyImplementation, Statement, StatementTag, SwitchStatement, TaskAccessInfoExpression, TaskAllExpression, TaskDashExpression, TaskMultiExpression, TaskRaceExpression, TaskRunExpression, TaskStatusStatement, TaskYieldStatement, ThisUpdateStatement, UpdateStatement, ValidateStatement, VarUpdateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VoidRefCallStatement } from "./body.js";
import { SimpleTypeInferContext, TypeEnvironment, TypeInferContext, VarInfo } from "./checker_environment.js";
import { TypeCheckerRelations } from "./checker_relations.js";

import { validateStringLiteral, validateCStringLiteral, loadConstAndValidateRESystem, accepts } from "@bosque/jsbrex";

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
    readonly errors: TypeError[] = [];

    readonly constraints: TemplateConstraintScope;
    readonly relations: TypeCheckerRelations;

    isTaskScope: boolean = false;
    envDecl: EnvironmentVariableInformation[] = [];

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

    private doRegexValidation(sinfo: SourceInfo, ofexp: LiteralRegexExpression | AccessNamespaceConstantExpression, inns: string, input: string, literalstring: string): void {
        try {
            const [pattern, pns] = this.relations.assembly.resolveConstantRegexExpressionValue(ofexp, inns);
            if(pattern === undefined) {
                this.reportError(sinfo, `Unable to resolve regex pattern -- ${ofexp.emit(true, new CodeFormatter())}`);
            }
            else {
                const isok = accepts(pattern, input, pns);
                this.checkError(sinfo, !isok, `Literal value "${literalstring}" does not match regex -- ${pattern}`);
            }
        }
        catch(e) {
            this.reportError(sinfo, `Invalid regex pattern -- ${(e as TypeError).msg}`);
        }
    }

    /*
    private doGlobValidation(sinfo: SourceInfo, ofexp: LiteralPathItemExpression | AccessNamespaceConstantExpression, inns: string, input: string, literalstring: string): void {
        return; //TODO: implement glob validation
    }
    */

    private static safeTypePrint(tsig: TypeSignature | undefined): string {
        return tsig === undefined ? "[undef_type]" : tsig.emit();
    }

    getErrorList(): TypeError[] {
        return this.errors;
    }

    private getWellKnownType(name: string): TypeSignature {
        assert(this.relations.wellknowntypes.has(name), `Well known type ${name} not found`);
        return this.relations.wellknowntypes.get(name) as TypeSignature;
    }

    private isVoidType(t: TypeSignature): boolean {
        return (t.tkeystr === "Void");
    }

    private checkTypeDeclOfStringRestrictions(sinfo: SourceInfo, tdecl: TypedeclTypeDecl, value: string): string | undefined {
        const vs = validateStringLiteral(value.slice(1, -1));
        this.checkError(sinfo, vs === null, `Invalid string literal value ${value}`);

        if(vs !== null && tdecl.optofexp !== undefined) {
            const vexp = this.relations.assembly.resolveValidatorLiteral(tdecl.optofexp);

            if(vexp === undefined || vexp.tag !== ExpressionTag.LiteralUnicodeRegexExpression) {
                this.reportError(sinfo, `Unable to resolve regex validator`);
            }
            else {
                if(!(vexp instanceof LiteralRegexExpression) && !(vexp instanceof AccessNamespaceConstantExpression)) {
                    this.reportError(sinfo, `Invalid regex validator -- expected literal or namespace constant`);
                }
                else {
                    this.doRegexValidation(sinfo, vexp, tdecl.ns.ns.join("::"), vs, value.slice(1, -1));
                }
            }
        }

        return vs !== null ? vs : undefined;
    }

    private checkTypeDeclOfCStringRestrictions(sinfo: SourceInfo, tdecl: TypedeclTypeDecl, value: string): string | undefined {
        const vs = validateCStringLiteral(value.slice(1, -1));
        this.checkError(sinfo, vs === null, `Invalid cstring literal value ${value}`);

        if(vs !== null && tdecl.optofexp !== undefined) {
            const vexp = this.relations.assembly.resolveValidatorLiteral(tdecl.optofexp);
            if(vexp === undefined || vexp.tag !== ExpressionTag.LiteralCRegexExpression) {
                this.reportError(sinfo, `Unable to resolve cregex validator`);
            }
            else {
                if(!(vexp instanceof LiteralRegexExpression) && !(vexp instanceof AccessNamespaceConstantExpression)) {
                    this.reportError(sinfo, `Invalid regex validator -- expected literal or namespace constant`);
                }
                else {
                    this.doRegexValidation(sinfo, vexp, tdecl.ns.ns.join("::"), vs, value.slice(1, -1));
                }
            }
        }

        return vs !== null ? vs : undefined;
    }

    /*
    private checkTypeDeclOfPathRestrictions(sinfo: SourceInfo, tdecl: TypedeclTypeDecl, value: string): string | undefined {
        //TODO: should validate with glob here!!!
        const vs = value;
                
        if(vs !== null && tdecl.optofexp !== undefined) {
            const vexp = this.relations.assembly.resolveValidatorLiteral(tdecl.optofexp);
            if(vexp === undefined || vexp.tag !== ExpressionTag.LiteralGlobExpression) {
                this.reportError(sinfo, `Unable to resolve glob validator`);
            }
            else {
                if(!(vexp instanceof LiteralPathItemExpression) && !(vexp instanceof AccessNamespaceConstantExpression)) {
                    this.reportError(sinfo, `Invalid glob validator -- expected literal or namespace constant`);
                }
                else {
                    this.doGlobValidation(sinfo, vexp, tdecl.ns.ns.join("::"), vs, value.slice(1, -1));
                }
            }
        }

        return vs !== null ? vs : undefined;
    }
    */

    private processITest_None(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        //!none === some
        if(isnot) {
            const rinfo = this.relations.splitOnSome(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to some-split type ${src.emit()}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.overlapSomeT, bindfalse: rinfo.hasnone ? this.getWellKnownType("None") : undefined };
            }
        }
        else {
            const rinfo = this.relations.splitOnNone(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to none-split type ${src.emit()}`);
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
                this.reportError(src.sinfo, `Unable to none-split type ${src.emit()}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.hasnone ? this.getWellKnownType("None") : undefined, bindfalse: rinfo.remainSomeT };
            }
        }
        else {
            const rinfo = this.relations.splitOnSome(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to some-split type ${src.emit()}`);
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
                this.reportError(src.sinfo, `Unable to err-split type ${src.emit()}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.overlapErrE, bindfalse: rinfo.remainOkT };
            }
        }
        else {
            const rinfo = this.relations.splitOnOk(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to nothing-split type ${src.emit()}`);
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
                this.reportError(src.sinfo, `Unable to err-split type ${src.emit()}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.overlapOkT, bindfalse: rinfo.remainErrE };
            }
        }
        else {
            const rinfo = this.relations.splitOnErr(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to nothing-split type ${src.emit()}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.overlapErrE, bindfalse: rinfo.remainOkT };
            }
        }
    }

    private processITest_Error(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        xxxx;
    }

    private processITest_Rejected(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        xxxx;
    }

    private processITest_Denied(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        xxxx;
    }

    private processITest_Flagged(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        xxxx;
    }

    private processITest_Success(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        xxxx;
    }

    private processITest_Type(src: TypeSignature, oftype: TypeSignature): { ttrue: TypeSignature[], tfalse: TypeSignature[] } {
        const rinfo = this.relations.refineType(src, oftype, this.constraints);
        if(rinfo === undefined) {
            this.reportError(src.sinfo, `Unable to some-split type ${src.emit()}`);
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
            else if(tt instanceof ITestError) {
                const tres = this.processITest_Error(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else if(tt instanceof ITestRejected) {
                const tres = this.processITest_Rejected(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else if(tt instanceof ITestDenied) {
                const tres = this.processITest_Denied(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else if(tt instanceof ITestFlagged) {
                const tres = this.processITest_Flagged(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else if(tt instanceof ITestSuccess) {
                const tres = this.processITest_Success(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else {
                assert(tt instanceof ITestFail, "missing case in ITest");
                const tres = this.processITest_Err(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
        }
    }

    private processITestConvertLUB(sinfo: SourceInfo, opts: TypeSignature[], lubtype: TypeSignature): TypeSignature | undefined {
        const flowlub = this.relations.flowTypeLUB(sinfo, lubtype, opts, this.constraints);
        if(flowlub instanceof ErrorTypeSignature) {
            return lubtype;
        }
        else {
            return flowlub;
        }
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
                    const tfalse = tres.ttrue.length !== 0 ? tt.ttype : undefined; //overlap and passes as the user spec type -- does not matter now but short circuiting return will use this

                    return { ttrue: ttrue, tfalse: tfalse };
                }
                else {
                    const ttrue = tres.ttrue.length !== 0 ? tt.ttype : undefined; //always cast to what the user asked for
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
            else if(tt instanceof ITestError) {
                const tres = this.processITest_Error(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else if(tt instanceof ITestRejected) {
                const tres = this.processITest_Rejected(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else if(tt instanceof ITestDenied) {
                const tres = this.processITest_Denied(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else if(tt instanceof ITestFlagged) {
                const tres = this.processITest_Flagged(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else if(tt instanceof ITestSuccess) {
                const tres = this.processITest_Success(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else {
                assert(tt instanceof ITestFail, "missing case in ITest");
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

            if(this.checkError(sinfo, tdecl.tconstraint !== undefined && !this.relations.isSubtypeOf(targ, tdecl.tconstraint, this.constraints), `Template argument ${tdecl.name} is not a subtype of restriction`)) {
                return false;
            }

            if(tdecl.extraTags.length !== 0) {
                if(tdecl.extraTags.includes(TemplateTermDeclExtraTag.KeyType)) {
                    if(this.checkError(sinfo, !this.relations.isKeyType(targ, this.constraints), `Template argument ${tdecl.name} is not a keytype`)) {
                        return false;
                    }
                }
                if(tdecl.extraTags.includes(TemplateTermDeclExtraTag.Numeric)) {
                    if(this.checkError(sinfo, !this.relations.isNumericType(targ, this.constraints), `Template argument ${tdecl.name} is not a numeric type`)) {
                        return false;
                    }
                }
                if(tdecl.extraTags.includes(TemplateTermDeclExtraTag.Equiv)) {
                    if(this.checkError(sinfo, !this.relations.isEquivType(targ, this.constraints), `Template argument ${tdecl.name} is not an equiv type`)) {                        return false;
                    }
                }
                if(tdecl.extraTags.includes(TemplateTermDeclExtraTag.Mergeable)) {
                    if(this.checkError(sinfo, !this.relations.isMergeableType(targ, this.constraints), `Template argument ${tdecl.name} is not a mergeable type`)) {
                        return false;
                    }
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

            if(terminfo.tconstraint !== undefined && this.checkTypeSignature(terminfo.tconstraint)) {
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

            if(terminfo.tconstraint !== undefined && this.checkTypeSignature(terminfo.tconstraint)) {
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
            const resolved = this.constraints.resolveConstraint(type.name);
            if(resolved === undefined) {
                this.reportError(type.sinfo, `Template type ${type.name} is not defined`);
                return false;
            }
            return true;
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
        xxxx;
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

                this.checkError(pp.type.sinfo, pp.isRefParam && !TypeChecker.isTypeUpdatable(pp.type)[0], `Ref parameter must be of an updatable type`);
            }

            if(type.name === "pred" && type.resultType.tkeystr !== "Bool") {
                this.reportError(type.sinfo, `Lambda pred must have a boolean return type`);
                return false;
            }

            return refct <= 1;
        }
        xxxx;
        else {
            assert(false, "Unknown TypeSignature type");
        }
    }

    private checkValueEq(lhsexp: Expression, lhs: TypeSignature, rhsexp: Expression, rhs: TypeSignature): ["err" | "lhsnone" | "rhsnone" | "stricteq" | "lhskeyeqoption" | "rhskeyeqoption", TypeSignature] {
        if(!(lhs instanceof NominalTypeSignature) || !(rhs instanceof NominalTypeSignature)) {
            return ["err", new ErrorTypeSignature(lhsexp.sinfo, undefined)];
        }

        if((lhs.decl instanceof OptionTypeDecl) && (rhs.decl instanceof OptionTypeDecl)) {
            return ["err", new ErrorTypeSignature(lhsexp.sinfo, undefined)];
        }
        else if(lhs.decl instanceof OptionTypeDecl) {
            if(rhsexp.tag === ExpressionTag.LiteralNoneExpression) {
                return ["rhsnone", rhs];
            }
            else {
                if(!this.relations.isKeyType(rhs, this.constraints)) {
                    return ["err", new ErrorTypeSignature(rhsexp.sinfo, undefined)];
                }
                else {
                    return this.relations.areSameTypes(rhs, lhs.alltermargs[0]) ? ["rhskeyeqoption", rhs] : ["err", new ErrorTypeSignature(rhsexp.sinfo, undefined)];
                }
            }
        }
        else if(rhs.decl instanceof OptionTypeDecl) {
            if(lhsexp.tag === ExpressionTag.LiteralNoneExpression) {
                return ["lhsnone", lhs];
            }
            else {
                if(!this.relations.isKeyType(lhs, this.constraints)) {
                    return ["err", new ErrorTypeSignature(lhsexp.sinfo, undefined)];
                }
                else {
                    return this.relations.areSameTypes(lhs, rhs.alltermargs[0]) ? ["lhskeyeqoption", lhs] : ["err", new ErrorTypeSignature(lhsexp.sinfo, undefined)];
                }
            }
        }
        else {
            if(!this.relations.isKeyType(lhs, this.constraints) || !this.relations.isKeyType(rhs, this.constraints)) {
                return ["err", new ErrorTypeSignature(lhsexp.sinfo, undefined)];
            }

            return this.relations.areSameTypes(lhs, rhs) ? ["stricteq", lhs] : ["err", new ErrorTypeSignature(lhsexp.sinfo, undefined)];

        }
    }

    private checkTemplateBindingsOnInvoke(sinfo: SourceInfo, env: TypeEnvironment, targs: TypeSignature[], decl: ExplicitInvokeDecl, refinemap: TemplateNameMapper | undefined): TemplateNameMapper | undefined {
        if(targs.length !== decl.terms.length) {
            this.reportError(sinfo, `Invoke ${decl.name} expected ${decl.terms.length} terms but got ${targs.length}`);
            return undefined;
        }

        let tmap = new Map<string, TypeSignature>();
        for(let i = 0; i < targs.length; ++i) {
            const targ = targs[i];
            const tdecl = decl.terms[i];

            const trestrict = tdecl.tconstraint;
            if(trestrict !== undefined && !this.relations.isSubtypeOf(targ, trestrict, this.constraints)) {
                this.reportError(sinfo, `Template argument ${tdecl.name} is not a subtype of constraint type`);
                return undefined;
            }

            if(tdecl.extraTags.length !== 0) {
                if(tdecl.extraTags.includes(TemplateTermDeclExtraTag.KeyType)) {
                    if(this.checkError(sinfo, !this.relations.isKeyType(targ, this.constraints), `Template argument ${tdecl.name} is not a keytype`)) {
                        return undefined;
                    }
                }
                if(tdecl.extraTags.includes(TemplateTermDeclExtraTag.Numeric)) {
                    if(this.checkError(sinfo, !this.relations.isNumericType(targ, this.constraints), `Template argument ${tdecl.name} is not a numeric type`)) {
                        return undefined;
                    }
                }
            }

            tmap.set(tdecl.name, targ);
        }

        if(decl.termRestriction !== undefined) {
            assert(refinemap !== undefined, "Template mapper must be defined");

            for(let i = 0; i < decl.termRestriction.clauses.length; ++i) {
                let cc = decl.termRestriction.clauses[i];
                let trefine = refinemap.resolveTemplateMapping(cc.t);

                if(cc.subtype !== undefined && !this.relations.isSubtypeOf(trefine, cc.subtype, this.constraints)) {
                    this.reportError(sinfo, `Template argument ${decl.terms[i].name} is not a subtype of subtype restriction`);
                    return undefined;
                }

                if(cc.extraTags.length !== 0) {
                    if(cc.extraTags.includes(TemplateTermDeclExtraTag.KeyType)) {
                        if(this.checkError(sinfo, !this.relations.isKeyType(trefine, this.constraints), `Template argument ${cc.t.name} is not a keytype`)) {
                            return undefined;
                        }
                    }
                    if(cc.extraTags.includes(TemplateTermDeclExtraTag.Numeric)) {
                        if(this.checkError(sinfo, !this.relations.isNumericType(trefine, this.constraints), `Template argument ${cc.t.name} is not a numeric type`)) {
                            return undefined;
                        }
                    }
                }
            }
        }

        return TemplateNameMapper.createInitialMapping(tmap);
    }

    private checkTemplateBindingsOnConstructor(sinfo: SourceInfo, env: TypeEnvironment, targs: TypeSignature[], cdecl: AbstractNominalTypeDecl): TemplateNameMapper | undefined {
        if(targs.length !== cdecl.terms.length) {
            this.reportError(sinfo, `Constructor ${cdecl.name} expected ${cdecl.terms.length} terms but got ${targs.length}`);
            return undefined;
        }

        let tmap = new Map<string, TypeSignature>();
        for(let i = 0; i < targs.length; ++i) {
            const targ = targs[i];
            const tdecl = cdecl.terms[i];

            const trestrict = tdecl.tconstraint;
            if(trestrict !== undefined && !this.relations.isSubtypeOf(targ, trestrict, this.constraints)) {
                this.reportError(sinfo, `Template argument ${tdecl.name} is not a subtype of constraint type`);
                return undefined;
            }

            if(tdecl.extraTags.length !== 0) {
                if(tdecl.extraTags.includes(TemplateTermDeclExtraTag.KeyType)) {
                    if(this.checkError(sinfo, !this.relations.isKeyType(targ, this.constraints), `Template argument ${tdecl.name} is not a keytype`)) {
                        return undefined;
                    }
                }
                if(tdecl.extraTags.includes(TemplateTermDeclExtraTag.Numeric)) {
                    if(this.checkError(sinfo, !this.relations.isNumericType(targ, this.constraints), `Template argument ${tdecl.name} is not a numeric type`)) {
                        return undefined;
                    }
                }
            }

            tmap.set(tdecl.name, targ);
        }

        return TemplateNameMapper.createInitialMapping(tmap);
    }

    private checkSingleParam(env: TypeEnvironment, arg: ArgumentValue, paramname: string, paramtype: TypeSignature, isRefParam: boolean, imapper: TemplateNameMapper): TypeSignature {
        if(arg instanceof SpreadArgumentValue) {
            this.reportError(arg.exp.sinfo, `Spread argument cannot be used except as part of rest args`);
        }

        if(isRefParam) {
            this.checkError(arg.exp.sinfo, !(arg instanceof RefArgumentValue), `Parameter ${paramname} is a reference parameter and must be passed by reference`);
        }
        if(arg instanceof RefArgumentValue) {
            this.checkError(arg.exp.sinfo, !isRefParam, `Parameter ${paramname} is not a reference parameter and argument cannot be passed by reference`);
            
            this.checkError(arg.exp.sinfo, !(arg.exp instanceof AccessVariableExpression), `Reference parameter must be on an variable name`);
            if(arg.exp instanceof AccessVariableExpression) {
                const vname = (arg.exp as AccessVariableExpression).srcname;
                const [vinfo, isparam] = env.resolveLocalVarInfoFromSrcNameWithIsParam(vname);
                if(vinfo === undefined) {
                    this.reportError(arg.exp.sinfo, `Variable ${vname} is not declared`);
                }
                else {
                    if((!isparam && vinfo.isConst) || (isparam && !vinfo.isRef)) {
                        this.reportError(arg.exp.sinfo, `Variable ${vname} is cannot be updated (is local const or not a ref param)`);
                    }
                }
            }
        }

        if(arg instanceof NamedArgumentValue) {
            this.checkError(arg.exp.sinfo, arg.name !== paramname, `Named argument ${arg.name} does not match parameter name ${paramname}`);
        }

        const ptype = paramtype.remapTemplateBindings(imapper);

        const argtype = this.checkExpression(env, arg.exp, new SimpleTypeInferContext(ptype));
        this.checkError(arg.exp.sinfo, !(argtype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(argtype, ptype, this.constraints), `Argument ${paramname} expected type ${ptype.emit()} but got ${argtype.emit()}`);

        return argtype;
    }

    private checkRestParam(env: TypeEnvironment, args: ArgumentValue[], paramname: string, paramtype: TypeSignature, imapper: TemplateNameMapper): [boolean, TypeSignature][] {
        const ptype = paramtype.remapTemplateBindings(imapper);
        const etype = this.relations.getExpandoableOfType(ptype);
        if(etype === undefined) {
            this.reportError(args[args.length - 1].exp.sinfo, `Rest parameter ${paramname} must be of type Expandoable`);
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

                this.checkError(arg.exp.sinfo, !(argtype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(argtype, etype, this.constraints), `Rest argument ${i} expected type ${etype.emit()}`);
            }
            else {
                const argtype = this.checkExpression(env, arg.exp, undefined);
                rtypes.push([true, argtype]);

                const argetype = this.relations.getExpandoableOfType(argtype);
                this.checkError(arg.exp.sinfo, argetype === undefined || !this.relations.areSameTypes(argetype, etype), `Rest argument ${i} expected to be container of type ${etype.emit()}`);
            }
        }

        return rtypes;
    }

    private checkArgumentList(sinfo: SourceInfo, env: TypeEnvironment, refok: boolean, args: ArgumentValue[], params: InvokeParameterDecl[], imapper: TemplateNameMapper): { shuffleinfo: [number, TypeSignature][], resttype: TypeSignature | undefined, restinfo: [number, boolean, TypeSignature][] | undefined } {
        const nonrestparams = params.filter((p) => !p.isRestParam);
        const restparam = params.find((p) => p.isRestParam); //is only 1 at the end (from parser)
        
        let argsuffle: (ArgumentValue | undefined)[] = [];
        let argsuffleidx: number[] = [];
        for(let i = 0; i < nonrestparams.length; ++i) {
            argsuffle.push(undefined);
            argsuffleidx.push(-1);
        }

        //fill in all the parameter arg shuggle info
        let nstart = args.findIndex((arg) => arg instanceof NamedArgumentValue); 
        if(nstart === -1) {
            nstart = args.length;
        }

        for(let i = 0; i < Math.min(nstart, nonrestparams.length); ++i) {
            argsuffle[i] = args[i];
            argsuffleidx[i] = i;

            this.checkError(args[i].exp.sinfo, !refok && (args[i] instanceof RefArgumentValue), `Reference argument only allowed in top-level contexts`);
        }

        //fill in all the named arguments
        let nlast = args.slice(nstart).findIndex((arg) => !(arg instanceof NamedArgumentValue));
        if(nlast === -1) {
            nlast = args.length;
        }
    
        for(let i = nstart; i < nlast; ++i) {
            const narg = args[i] as NamedArgumentValue;
            const paramidx = params.findIndex((p) => p.name === narg.name);
            if(paramidx === -1) {
                this.reportError(narg.exp.sinfo, `Named argument ${narg.name} not found in parameter list`);
            }
            else if(params[paramidx].isRestParam) {
                this.reportError(narg.exp.sinfo, `Named argument ${narg.name} cannot be assigned to rest parameter`);
            }
            else if(argsuffleidx[paramidx] !== -1) {
                this.reportError(narg.exp.sinfo, `Named argument ${narg.name} already assigned to parameter`);
            }
            else {
                argsuffle[paramidx] = narg;
                argsuffleidx[paramidx] = i;
            }
        }

        if(restparam === undefined && args.length > params.length) {
            this.reportError(sinfo, `Too many arguments provided to function`);
        }
            
        let usingdeafults = false;
        let argsuffletype: TypeSignature[] = [];
        for(let i = 0; i < nonrestparams.length; ++i) {
            if(argsuffle[i] === undefined) {
                this.checkError(sinfo, nonrestparams[i].optDefaultValue === undefined, `Required argument ${nonrestparams[i].name} not provided`);
                usingdeafults = true;
                argsuffletype[i] = nonrestparams[i].type;
            }
            else {
                const pp = nonrestparams[i];
                argsuffletype[i] = this.checkSingleParam(env, argsuffle[i] as ArgumentValue, pp.name, pp.type, pp.isRefParam, imapper);
            }
        }
        
        let resttype: TypeSignature | undefined = undefined;
        let restinfo: [number, boolean, TypeSignature][] | undefined = undefined;
        if(restparam !== undefined) {
            let restargs = args.slice(Math.min(nlast, nonrestparams.length));
            this.checkError(sinfo, restargs.length !== 0 && usingdeafults, `Cannot use (implicit) default arguments with rest parameter as uses are ambigious`);

            const restypes = this.checkRestParam(env, restargs, restparam.name, restparam.type, imapper);

            resttype = restparam.type.remapTemplateBindings(imapper);
            restinfo = [];
            for(let i = nonrestparams.length; i < args.length; ++i) {
                const rri = restypes[i - nonrestparams.length] as [boolean, TypeSignature];
                restinfo.push([i, rri[0], rri[1]]);
            }
        }

        let shuffleinfo: [number, TypeSignature][] = [];
        for(let i = 0; i < nonrestparams.length; ++i) {
            shuffleinfo.push([argsuffleidx[i], argsuffletype[i]]);
        }

        return { shuffleinfo: shuffleinfo, resttype: resttype, restinfo: restinfo };
    }

    private checkLambdaArgumentList(sinfo: SourceInfo, env: TypeEnvironment, refok: boolean, args: ArgumentValue[], params: LambdaParameterSignature[]): { arginfo: TypeSignature[], resttype: TypeSignature | undefined, restinfo: [number, boolean, TypeSignature][] | undefined } {
        if(args.some((av) => av instanceof NamedArgumentValue)) {
            this.reportError(sinfo, `Named arguments not allowed in lambda argument list`);
        }

        const nonrestparams = params.filter((p) => !p.isRestParam);
        const restparam = params.find((p) => p.isRestParam); //is only 1 at the end (from parser)

        if(nonrestparams.length > args.length) {
            this.reportError(sinfo, `Too few arguments provided to lambda`);
        }

        let arginfo: TypeSignature[] = [];
        for(let i = 0; i < nonrestparams.length && i < args.length; ++i) {
            const argtype = this.checkSingleParam(env, args[i], "[lambda_param]", nonrestparams[i].type, nonrestparams[i].isRefParam, TemplateNameMapper.createEmpty());
            arginfo.push(argtype);
        }

        let resttype: TypeSignature | undefined = undefined;
        let restinfo: [number, boolean, TypeSignature][] | undefined = undefined;
        if(restparam !== undefined) {
            let restargs = args.slice(nonrestparams.length);
            const restypes = this.checkRestParam(env, restargs, "[lambda_param]", restparam.type, TemplateNameMapper.createEmpty());

            resttype = restparam.type;
            restinfo = [];
            for(let i = nonrestparams.length; i < args.length; ++i) {
                const rri = restypes[i - nonrestparams.length] as [boolean, TypeSignature];
                restinfo.push([i, rri[0], rri[1]]);
            }
        }

        return { arginfo: arginfo, resttype: resttype, restinfo: restinfo };
    }

    private checkConstructorArgumentListStd(sinfo: SourceInfo, env: TypeEnvironment, args: ArgumentValue[], bnames: {name: string, type: TypeSignature, hasdefault: boolean, containingtype: NominalTypeSignature}[], imapper: TemplateNameMapper): [number, TypeSignature, string, TypeSignature][] {
        let argsuffle: (ArgumentValue | undefined)[] = [];
        let argsuffleidx: number[] = [];
        for(let i = 0; i < bnames.length; ++i) {
            argsuffle.push(undefined);
            argsuffleidx.push(-1);
        }

        //fill in all the parameter arg shuggle info
        let nfirst = args.findIndex((arg) => arg instanceof NamedArgumentValue); 
        if(nfirst === -1) {
            nfirst = args.length;
        }

        for(let i = 0; i < Math.min(bnames.length, nfirst); ++i) {
            argsuffle[i] = args[i];
            argsuffleidx[i] = i;

            this.checkError(args[i].exp.sinfo, (args[i] instanceof RefArgumentValue), `Reference argument not allowed in constructors`);
        }

        //fill in all the named arguments
        let nlast = args.slice(nfirst).findIndex((arg) => !(arg instanceof NamedArgumentValue));
        if(nlast === -1) {
            nlast = args.length;
        }
    
        for(let i = nfirst; i < nlast; ++i) {
            const narg = args[i] as NamedArgumentValue;
            const paramidx = bnames.findIndex((p) => p.name === narg.name);
            if(paramidx === -1) {
                this.reportError(narg.exp.sinfo, `Named argument ${narg.name} not found in parameter list`);
            }
            else if(argsuffleidx[paramidx] !== -1) {
                this.reportError(narg.exp.sinfo, `Named argument ${narg.name} already assigned to parameter`);
            }
            else {
                argsuffle[paramidx] = narg;
                argsuffleidx[paramidx] = i;
            }
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

                const ftype = bnames[i].type.remapTemplateBindings(imapper);

                this.checkError(argexp.sinfo, !(argtype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(argtype, ftype, this.constraints), `Argument ${bnames[i].name} expected type ${ftype.emit()} but got ${argtype.emit()}`);
            }
        }

        if(args.length > bnames.length) {
            this.reportError(sinfo, `Too many arguments provided to constructor`);
            return [];
        }

        return argsuffleidx.map((idx, i) => [idx, bnames[i].containingtype.remapTemplateBindings(imapper), bnames[i].name, bnames[i].type.remapTemplateBindings(imapper)]);
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

    private checkLiteralChkNatExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        const nval = BigInt(exp.value.slice(0, exp.value.length - 1));
        this.checkError(exp.sinfo, nval < 0n, "ChkNat literal cannot be negative");
        this.checkError(exp.sinfo, MAX_SAFE_CHK_NAT < nval, "ChkNat literal out of valid range");

        return exp.setType(this.getWellKnownType("ChkNat"));
    }

    private checkLiteralChkIntExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        const nval = BigInt(exp.value.slice(0, exp.value.length - 1));
        this.checkError(exp.sinfo, nval < MIN_SAFE_CHK_INT, "ChkInt literal out of valid range");
        this.checkError(exp.sinfo, MAX_SAFE_CHK_INT < nval, "ChkInt literal out of valid range");
        
        return exp.setType(this.getWellKnownType("ChkInt"));
    }

    private checkLiteralRationalExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        const slpos = exp.value.indexOf("/");
        const num = BigInt(exp.value.slice(0, slpos));
        this.checkError(exp.sinfo, MAX_SAFE_CHK_INT < num, "Rational literal numerator out of valid range");

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

    private checkLiteralTZDateTimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        //TODO: missing years and days in month validation here
        return exp.setType(this.getWellKnownType("TZDateTime"));
    }

    private checkLiteralTAITimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        //TODO: missing years and days in month validation here -- also leap seconds
        return exp.setType(this.getWellKnownType("TAIDateTime"));
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

    private checkLiteralISOTimeStampExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        //TODO: missing years and days in month validation here -- also leap seconds
        return exp.setType(this.getWellKnownType("ISOTimeStamp"));
    }

    private checkLiteralDeltaDateTimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaDateTime"));
    }

    private checkLiteralDeltaISOTimeStampExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaISOTimeStamp"));
    }

    private checkLiteralDeltaSecondsExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaSeconds"));
    }

    private checkLiteralDeltaLogicalExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaLogical"));
    }

    private checkLiteralUnicodeRegexExpression(env: TypeEnvironment, exp: LiteralRegexExpression): TypeSignature {
        try { 
            accepts(exp.value, "", exp.inns.ns.join("::")); //if this throws the the regex was invalid
        }
        catch(err) {
            this.reportError(exp.sinfo, `Invalid UnicodeRegex literal: ${exp.value}`);
        }

        return exp.setType(this.getWellKnownType("Regex"));
    }

    private checkLiteralCRegexExpression(env: TypeEnvironment, exp: LiteralRegexExpression): TypeSignature {
        try { 
            accepts(exp.value, "", exp.inns.ns.join("::")); //if this throws the the regex was invalid
        }
        catch(err) {
            this.reportError(exp.sinfo, `Invalid UnicodeRegex literal: ${exp.value}`);
        }

        return exp.setType(this.getWellKnownType("CRegex"));
    }

    private checkLiteralByteExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        const nval = Number.parseInt(exp.value, 16);
        this.checkError(exp.sinfo, nval < 0 || 255 < nval, "Byte literal out of valid range");

        return exp.setType(this.getWellKnownType("Byte"));
    }

    private checkLiteralCCharExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        try {
            const vcc = validateCStringLiteral(exp.value.slice(2, exp.value.length - 1));
            if(vcc === null) {
                throw new Error(`Invalid CChar literal`);
            }
            if(vcc.length > 1) {
                throw new Error(`Expected zero or one UnicodeChar, but found ${vcc.length} characters`);
            }
            exp.resolvedValue = vcc;
        } catch(err) {
            this.reportError(exp.sinfo, (err as Error).message);
        }

        return exp.setType(this.getWellKnownType("CChar"));
    }

    private checkLiteralUnicodeCharExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        try {
            const vuc = validateStringLiteral(exp.value.slice(2, exp.value.length - 1));
            if(vuc === null) {
                throw new Error(`Invalid UnicodeChar literal`)
            }
            if(vuc.length > 1) {
                throw new Error(`Expected zero or one UnicodeChar, but found ${vuc.length} characters`);
            }
            exp.resolvedValue = vuc;
        } catch(err) {
            this.reportError(exp.sinfo, (err as Error).message);
        }

        return exp.setType(this.getWellKnownType("UnicodeChar"));
    }

    private checkLiteralStringExpression(env: TypeEnvironment, exp: LiteralStringExpression): TypeSignature {
        try {
            const vs = validateStringLiteral(exp.value.slice(1, exp.value.length - 1));
            exp.resolvedValue = vs;
        } catch(err) {
            this.reportError(exp.sinfo, (err as Error).message);
        }
        
        return exp.setType(this.getWellKnownType("String"));
    }

    private checkLiteralCStringExpression(env: TypeEnvironment, exp: LiteralCStringExpression): TypeSignature {
        try {
            const vs = validateCStringLiteral(exp.value.slice(1, exp.value.length - 1));
            exp.resolvedValue = vs;
        } catch(err) {
            this.reportError(exp.sinfo, (err as Error).message);
        }
        
        return exp.setType(this.getWellKnownType("CString"));
    }

    private computeFormatArgsTypes(sinfo: SourceInfo, fmts: FormatStringComponent[], defaulttype: TypeSignature): {argname: string, argtype: TypeSignature}[] {
        let fmttypes: {argname: string, argtype: TypeSignature}[] = [];
        for(let i = 0; i < fmts.length; ++i) {
            const ffmt = fmts[i];
            if(ffmt instanceof FormatStringTextComponent) {
                try {
                    const vs = validateStringLiteral(ffmt.text);
                    ffmt.resolvedValue = vs;
                } catch(err) {
                    this.reportError(sinfo, (err as Error).message);
                }
            }
            else {
                const argfmt = ffmt as FormatStringArgComponent;
                if(argfmt.argType instanceof AutoTypeSignature) {
                    argfmt.resolvedType = defaulttype;
                }
                else {
                    const oktype = this.checkTypeSignature(argfmt.argType);
                    if(!oktype || !(argfmt.argType instanceof NominalTypeSignature)) {
                        argfmt.resolvedType = new ErrorTypeSignature(sinfo, undefined);
                    }
                    else {
                        argfmt.resolvedType = argfmt.argType;
                    }
                }

                fmttypes.push({argname: argfmt.argPos, argtype: argfmt.resolvedType});
            }
        }

        return fmttypes;
    }

    private checkLiteralFormatStringExpression(env: TypeEnvironment, exp: LiteralFormatStringExpression): TypeSignature {
        const fmttypes = this.computeFormatArgsTypes(exp.sinfo, exp.fmts, this.getWellKnownType("String"));
        
        return exp.setType(new FormatStringTypeSignature(exp.sinfo, "String", this.getWellKnownType("String"), fmttypes));
    }

    private checkLiteralFormatCStringExpression(env: TypeEnvironment, exp: LiteralFormatCStringExpression): TypeSignature {
        const fmttypes = this.computeFormatArgsTypes(exp.sinfo, exp.fmts, this.getWellKnownType("CString"));
        
        return exp.setType(new FormatStringTypeSignature(exp.sinfo, "CString", this.getWellKnownType("CString"), fmttypes));
    }

    private checkLiteralPathExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLiteralPathExpression");
    }

    private checkLiteralPathFragmentExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLiteralPathFragmentExpression");
    }

    private checkLiteralGlobExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
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

        const btype = this.relations.getTypeDeclValueType(exp.constype);
        const bvalue = this.checkExpression(env, exp.value, btype !== undefined ? new SimpleTypeInferContext(btype) : undefined);
        this.checkError(exp.sinfo, !(bvalue instanceof ErrorTypeSignature) && btype !== undefined && !this.relations.areSameTypes(bvalue, btype), `Literal value is not the same type (${bvalue.emit()}) as the value type (${TypeChecker.safeTypePrint(btype)})`);

        return exp.setType(exp.constype);
    }

    private checkLiteralTypedStringExpression(env: TypeEnvironment, exp: LiteralTypedStringExpression): TypeSignature {
         if(!this.checkTypeSignature(exp.constype)) {
            return exp.setType(exp.constype);
        }

        if(!(exp.constype instanceof NominalTypeSignature) || !(exp.constype.decl instanceof TypedeclTypeDecl)) {
            this.reportError(exp.sinfo, `Invalid type for typed string literal expression -- ${exp.constype.emit()}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const btype = this.relations.getTypeDeclValueType(exp.constype);
        if(btype === undefined || !this.relations.areSameTypes(btype, this.getWellKnownType("String"))) {
            this.reportError(exp.sinfo, `Typed string literal type must have base type String -- ${exp.constype.emit()}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const vs = this.checkTypeDeclOfStringRestrictions(exp.sinfo, exp.constype.decl as TypedeclTypeDecl, exp.value);
        if(vs === null) {
            exp.resolvedValue = vs;
        }
            
        return exp.setType(exp.constype);
    }

    private checkLiteralTypedCStringExpression(env: TypeEnvironment, exp: LiteralTypedCStringExpression): TypeSignature {
        if(!this.checkTypeSignature(exp.constype)) {
            return exp.setType(exp.constype);
        }

        if(!(exp.constype instanceof NominalTypeSignature) || !(exp.constype.decl instanceof TypedeclTypeDecl)) {
            this.reportError(exp.sinfo, `Invalid type for typed cstring literal expression -- ${exp.constype.emit()}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const btype = this.relations.getTypeDeclValueType(exp.constype);
        if(btype === undefined || !this.relations.areSameTypes(btype, this.getWellKnownType("CString"))) {
            this.reportError(exp.sinfo, `Typed cstring literal type must have base type CString -- ${exp.constype.emit()}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const vs = this.checkTypeDeclOfCStringRestrictions(exp.sinfo, exp.constype.decl as TypedeclTypeDecl, exp.value);
        if(vs === null) {
            exp.resolvedValue = vs;
        }
            
        return exp.setType(exp.constype);
    }

    private checkLiteralTypedFormatStringExpression(env: TypeEnvironment, exp: LiteralTypedFormatStringExpression): TypeSignature {
        if(!this.checkTypeSignature(exp.constype)) {
            return exp.setType(exp.constype);
        }

        if(!(exp.constype instanceof NominalTypeSignature) || !(exp.constype.decl instanceof TypedeclTypeDecl)) {
            this.reportError(exp.sinfo, `Invalid type for typed format string expression -- ${exp.constype.emit()}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const btype = this.relations.getTypeDeclValueType(exp.constype);
        if(!this.relations.areSameTypes(exp.constype, this.getWellKnownType("String")) && (btype === undefined || !this.relations.areSameTypes(btype, this.getWellKnownType("String")))) {
            this.reportError(exp.sinfo, `Typed format string type must have base type String -- ${exp.constype.emit()}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const fmttypes = this.computeFormatArgsTypes(exp.sinfo, exp.fmts, this.getWellKnownType("String"));
        
        return exp.setType(new FormatStringTypeSignature(exp.sinfo, "String", exp.constype, fmttypes));
    }

    private checkLiteralTypedFormatCStringExpression(env: TypeEnvironment, exp: LiteralTypedFormatCStringExpression): TypeSignature {
        if(!this.checkTypeSignature(exp.constype)) {
            return exp.setType(exp.constype);
        }

        if(!(exp.constype instanceof NominalTypeSignature) || !(exp.constype.decl instanceof TypedeclTypeDecl)) {
            this.reportError(exp.sinfo, `Invalid type for typed format cstring expression -- ${exp.constype.emit()}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const btype = this.relations.getTypeDeclValueType(exp.constype);
        if(!this.relations.areSameTypes(exp.constype, this.getWellKnownType("CString")) && (btype === undefined || !this.relations.areSameTypes(btype, this.getWellKnownType("CString")))) {
            this.reportError(exp.sinfo, `Typed format cstring type must have base type CString -- ${exp.constype.emit()}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const fmttypes = this.computeFormatArgsTypes(exp.sinfo, exp.fmts, this.getWellKnownType("CString"));
        
        return exp.setType(new FormatStringTypeSignature(exp.sinfo, "CString", exp.constype, fmttypes));
    }

    private checkAccessEnvValueExpression(env: TypeEnvironment, exp: AccessEnvValueExpression): TypeSignature {
        this.checkError(exp.sinfo, !this.isTaskScope, `Environment values in non-task scopes`);

        if(!exp.keyname.startsWith("'")) {
            exp.resolvedkey = exp.keyname;
        }
        else {
            try {
                const vs = validateCStringLiteral(exp.keyname.slice(1, exp.keyname.length - 1));
                if(vs === null) {
                    this.reportError(exp.sinfo, `Invalid CString literal for environment value key`);
                    return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
                }
                exp.resolvedkey = vs;
            } catch(err) {
                this.reportError(exp.sinfo, (err as Error).message);
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
        }

        const evdecl = this.envDecl.find((ev) => ev.evname === exp.keyname);
        if(exp.opname === "has") {
            if(evdecl === undefined) {
                this.reportError(exp.sinfo, `Environment variable ${exp.keyname} is never defined`);
            }
            else {
                this.checkError(exp.sinfo, evdecl.required, `Environment variable ${exp.keyname} is always defined`);
            }

            return exp.setType(this.getWellKnownType("Bool"));
        }
        else {
            if(evdecl === undefined) {
                this.reportError(exp.sinfo, `Could not find environment value ${exp.keyname}`);
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            exp.mustdefined = evdecl.required;

            this.checkTypeSignature(evdecl.evtype);
            if(exp.opname === undefined || exp.opname === "get") {
                return exp.setType(evdecl.evtype);
            }
            else {
                const optdecl = this.relations.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Option") as OptionTypeDecl;
                return exp.setType(new NominalTypeSignature(exp.sinfo, undefined, optdecl, [evdecl.evtype]));
            }
        }
    }

    private checkTaskAccessInfoExpression(env: TypeEnvironment, exp: TaskAccessInfoExpression): TypeSignature {
        this.checkError(exp.sinfo, !this.isTaskScope, `Task ID values cannot be accessed in non-task scopes`);

        return exp.setType(this.getWellKnownType("UUIDv7"));
    }
    
    private checkAccessNamespaceConstantExpression(env: TypeEnvironment, exp: AccessNamespaceConstantExpression): TypeSignature {
        const cdecl = this.relations.assembly.resolveNamespaceConstant(exp.ns, exp.name);
        if(cdecl === undefined) {
            this.reportError(exp.sinfo, `Could not find namespace constant ${exp.ns}::${exp.name}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        this.checkTypeSignature(cdecl.declaredType);
        return exp.setType(cdecl.declaredType);
    }

    private checkAccessStaticFieldExpression(env: TypeEnvironment, exp: AccessStaticFieldExpression): TypeSignature {
        const tok = this.checkTypeSignature(exp.stype);
        if(!tok) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        if(this.relations.isNumericType(exp.stype, this.constraints)) {
            if(exp.name === "zero") {
                exp.resolvedDeclType = exp.stype;
                return exp.setType(exp.stype);
            }
            if(exp.name === "one") {
                exp.resolvedDeclType = exp.stype;
                return exp.setType(exp.stype);
            }
        }

        const cconst = this.relations.resolveTypeConstant(exp.stype, exp.name, this.constraints);
        if(cconst !== undefined) {
            exp.resolvedDeclType = cconst.typeinfo.tsig;
            return exp.setType(cconst.member.declaredType.remapTemplateBindings(cconst.typeinfo.mapping));
        }
        else {
            this.reportError(exp.sinfo, `Type ${exp.stype.emit()} does not have const field ${exp.name}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }
    }

    private checkAccessEnumExpression(env: TypeEnvironment, exp: AccessEnumExpression): TypeSignature {
        const oktype = this.checkTypeSignature(exp.stype);
        if(!oktype) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        if(!(exp.stype instanceof NominalTypeSignature) || !(exp.stype.decl instanceof EnumTypeDecl)) {
            this.reportError(exp.sinfo, `Invalid type for enum access expression -- ${exp.stype.emit()}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const edecl = exp.stype.decl as EnumTypeDecl;
        if(edecl.members.includes(exp.name)) {
            return exp.setType(exp.stype);
        }
        else {
            this.reportError(exp.sinfo, `Enum ${exp.stype.decl.name} does not have member ${exp.name}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }
    }

    private checkAccessVariableExpression(env: TypeEnvironment, exp: AccessVariableExpression): TypeSignature {
        const vinfo = env.resolveLocalVarInfoFromSrcName(exp.srcname);
        if(vinfo !== undefined) {
            this.checkError(exp.sinfo, !vinfo.mustDefined, `Variable ${exp.srcname} may not be defined on all control flow paths`);
            
            exp.isParameter = env.isLocalVariableAParameter(vinfo.srcname);
            return exp.setType(vinfo.decltype);
        }
        else {
            const cinfo = env.resolveLambdaCaptureVarInfoFromSrcName(exp.srcname);
            if(cinfo === undefined) {
                this.reportError(exp.sinfo, `Variable ${exp.srcname} is not declared here`);
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            else {
                this.checkError(exp.sinfo, !cinfo[0].mustDefined, `Variable ${exp.srcname} may not be defined on all control flow paths`);

                exp.isCaptured = true;
                exp.scopeidx = cinfo[1];
                return exp.setType(cinfo[0].decltype);
            }
        }
    }

/*
    private checkCollectionConstructor(env: TypeEnvironment, cdecl: AbstractCollectionTypeDecl, exp: ConstructorPrimaryExpression): TypeSignature {
        const etype = this.relations.getExpandoableOfType(exp.ctype) as TypeSignature;

        if(exp.args.args.some((arg) => (arg instanceof NamedArgumentValue) || (arg instanceof RefArgumentValue))) {
            this.reportError(exp.sinfo, `Collection constructor expects only positional (or spread) arguments`);
            return exp.setType(exp.ctype);
        }

        let shuffleinfo: [number, TypeSignature | undefined, string, TypeSignature][] = [];
        for(let i = 0; i < exp.args.args.length; ++i) {
            shuffleinfo.push([i, undefined, "_", etype]);
            const arg = exp.args.args[i];

            if(arg instanceof PositionalArgumentValue) {
                const argtype = this.checkExpression(env, arg.exp, new SimpleTypeInferContext(etype));
                this.checkError(arg.exp.sinfo, (argtype instanceof ErrorTypeSignature) || !this.relations.isSubtypeOf(argtype, etype, this.constraints), `Argument ${i} expected type ${etype.emit()}`);
            }
            else {
                const argtype = this.checkExpression(env, arg.exp, undefined);
                const argetype = this.relations.getExpandoableOfType(argtype);
                this.checkError(arg.exp.sinfo, argetype === undefined || !this.relations.areSameTypes(argetype, etype), `Spread argument ${i} expected to be container of type ${etype.emit()}`);
            }
        }

        exp.elemtype = etype;
        exp.shuffleinfo = shuffleinfo;
        return exp.setType(exp.ctype);
    }

    private checkPrimitiveConstructor(env: TypeEnvironment, cdecl: PrimitiveEntityTypeDecl, exp: ConstructorPrimaryExpression): TypeSignature {
        const ctype = exp.ctype as NominalTypeSignature;

        if(exp.args.args.some((arg) => !(arg instanceof PositionalArgumentValue))) {
            this.reportError(exp.sinfo, `Primitive entity constructor expects only positional arguments`);
            return exp.setType(ctype);
        }

        // Note: For now we limit the buffers size to 8
        if(ctype.tkeystr === "CCharBuffer") {
            if(exp.args.args.length > 8) {
                this.reportError(exp.sinfo, `CCharBuffer constructor expects no more than 8 arguments`);
            }
            else {
                for(let i = 0; i < exp.args.args.length; ++i) {
                    let arg = exp.args.args[i];
                    if(arg instanceof PositionalArgumentValue) {
                        let argtype = this.checkExpression(env, arg.exp, new SimpleTypeInferContext(ctype));
                        this.checkError(arg.exp.sinfo, (argtype instanceof ErrorTypeSignature) || argtype.tkeystr !== "CChar", `Argument ${i} expected type CChar`);
                    } 
                    else {
                        this.reportError(exp.sinfo, `CCharBuffer expects positional arguments`);
                    }
                }
            }
        }

        if(ctype.tkeystr === "UnicodeCharBuffer") {
            if(exp.args.args.length > 8) {
                this.reportError(exp.sinfo, `UnicodeCharBuffer constructor expects no more than 8 arguments`);
            }
            else {
                for(let i = 0; i < exp.args.args.length; ++i) {
                    let arg = exp.args.args[i];
                    if(arg instanceof PositionalArgumentValue) {
                        let argtype = this.checkExpression(env, arg.exp, new SimpleTypeInferContext(ctype));
                        this.checkError(arg.exp.sinfo, (argtype instanceof ErrorTypeSignature) || argtype.tkeystr !== "UnicodeChar", `Argument ${i} expected type UnicodeChar`);
                    } 
                    else {
                        this.reportError(exp.sinfo, `UnicodeCharBuffer expects positional arguments`);
                    }
                }
            }
        }
        
        return exp.setType(ctype);
    }

    private checkSpecialConstructableConstructor(env: TypeEnvironment, cdecl: ConstructableTypeDecl, exp: ConstructorPrimaryExpression): TypeSignature {
        /*
        const ctype = exp.ctype as NominalTypeSignature;

        if(exp.args.args.some((arg) => !(arg instanceof PositionalArgumentValue))) {
            this.reportError(exp.sinfo, `Special constructor expects only positional arguments`);
            return exp.setType(ctype);
        }

        if(cdecl instanceof OkTypeDecl) {
            if(exp.args.args.length !== 1) {
                this.reportError(exp.sinfo, `Ok constructor expects 1 argument`);
            }
            else {
                const oktype = ctype.alltermargs[0];
                exp.shuffleinfo = [[0, undefined, "value", oktype]];

                const okarg = this.checkExpression(env, exp.args.args[0].exp, new SimpleTypeInferContext(oktype));
                this.checkError(exp.sinfo, (okarg instanceof ErrorTypeSignature) || !this.relations.isSubtypeOf(okarg, oktype, this.constraints), `Ok constructor argument is not a subtype of ${oktype.emit()}`);
            }
        }
        else if(cdecl instanceof FailTypeDecl) {
            if(exp.args.args.length !== 1) {
                this.reportError(exp.sinfo, `Fail constructor expects 1 argument`);
            }
            else {
                const errtype = ctype.alltermargs[1];
                exp.shuffleinfo = [[0, undefined, "value", errtype]];

                const errarg = this.checkExpression(env, exp.args.args[0].exp, new SimpleTypeInferContext(errtype));
                this.checkError(exp.sinfo, (errarg instanceof ErrorTypeSignature) || !this.relations.isSubtypeOf(errarg, errtype, this.constraints), `Err constructor argument is not a subtype of ${errtype.emit()}`);
            }
        }
        else if((cdecl instanceof APIRejectedTypeDecl) || (cdecl instanceof APIFailedTypeDecl) || (cdecl instanceof APIErrorTypeDecl) || (cdecl instanceof APISuccessTypeDecl)) {
            if(exp.args.args.length !== 1) {
                this.reportError(exp.sinfo, `API result constructor expects 1 argument`);
            }
            else {
                const apitype = ctype.alltermargs[0];
                exp.shuffleinfo = [[0, undefined, "value", apitype]];

                const apiarg = this.checkExpression(env, exp.args.args[0].exp, new SimpleTypeInferContext(apitype));
                this.checkError(exp.sinfo, (apiarg instanceof ErrorTypeSignature) || !this.relations.isSubtypeOf(apiarg, apitype, this.constraints), `API result constructor argument is not a subtype of ${apitype.emit()}`);
            }
        }
        else if(cdecl instanceof SomeTypeDecl) {
            if(exp.args.args.length !== 1) {
                this.reportError(exp.sinfo, `Some constructor expects 1 argument`);
            }
            else {
                const ttype = ctype.alltermargs[0];
                exp.shuffleinfo = [[0, undefined, "value", ttype]];

                const etype = this.checkExpression(env, exp.args.args[0].exp, new SimpleTypeInferContext(ttype));
                this.checkError(exp.sinfo, (etype instanceof ErrorTypeSignature) || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Some constructor argument is not a subtype of ${ttype.emit()}`);
            }
        }
        else if(cdecl instanceof MapEntryTypeDecl) {
            if(exp.args.args.length !== 2) {
                this.reportError(exp.sinfo, `MapEntry constructor expects 2 arguments`);
            }
            else {
                const ktype = ctype.alltermargs[0];
                exp.shuffleinfo = [[0, undefined, "key", ktype]];
                const ketype = this.checkExpression(env, exp.args.args[0].exp, new SimpleTypeInferContext(ktype));
                this.checkError(exp.sinfo, (ketype instanceof ErrorTypeSignature) || !this.relations.isSubtypeOf(ketype, ktype, this.constraints), `MapEntry constructor key argument is not a subtype of ${ktype.emit()}`);

                const vtype = ctype.alltermargs[1];
                exp.shuffleinfo = [[1, undefined, "value", vtype]];
                const vetype = this.checkExpression(env, exp.args.args[1].exp, new SimpleTypeInferContext(vtype));
                this.checkError(exp.sinfo, (vetype instanceof ErrorTypeSignature) || !this.relations.isSubtypeOf(vetype, vtype, this.constraints), `MapEntry constructor value argument is not a subtype of ${vtype.emit()}`);
            }
        }
        else {
            assert(false, "Unknown ConstructableTypeDecl type");
        }

        return exp.setType(ctype);
    }

    private checkSpecialTypeDeclConstructor(env: TypeEnvironment, cdecl: TypedeclTypeDecl, exp: ConstructorPrimaryExpression): TypeSignature {
        const ctype = exp.ctype as NominalTypeSignature;

        if(exp.args.args.length !== 1) {
            this.reportError(exp.sinfo, `${ctype.emit()} constructor expects 1 argument`);
        }
        else if(!(exp.args.args[0] instanceof PositionalArgumentValue)) {
            this.reportError(exp.sinfo, `Type alias constructor expects only positional arguments`);
        }
        else {
            const vtype = this.relations.getTypeDeclValueType(ctype);
            if(vtype !== undefined) {
                const etype = this.checkExpression(env, exp.args.args[0].exp, new SimpleTypeInferContext(vtype));
                this.checkError(exp.sinfo, (etype instanceof ErrorTypeSignature) || !(this.relations.areSameTypes(etype, vtype)), `${etype.emit()} constructor argument is not compatible with ${vtype.emit()}`);
            }
        }
        
        return exp.setType(ctype);
    }

    private checkStandardConstructor(env: TypeEnvironment, fields: MemberFieldDecl[], exp: ConstructorPrimaryExpression): TypeSignature {
        const ctype = exp.ctype as NominalTypeSignature;

        const imapper = this.checkTemplateBindingsOnConstructor(exp.sinfo, env, ctype.alltermargs, ctype.decl);
        if(imapper === undefined) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }
        
        const bnames = this.relations.generateAllFieldBNamesInfo(ctype, fields, this.constraints);
        const shuffleinfo = this.checkConstructorArgumentListStd(exp.sinfo, env, exp.args.args, bnames, imapper);

        exp.shuffleinfo = shuffleinfo;
        return exp.setType(ctype);
        
    }
*/
    private checkConstructorPrimaryExpression(env: TypeEnvironment, exp: ConstructorPrimaryExpression): TypeSignature {
        /*
        const tok = this.checkTypeSignature(exp.ctype);

        if(!tok) {
            this.reportError(exp.sinfo, `Invalid type for constructor expression -- ${exp.ctype.emit()}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const decl = exp.ctype.decl;
        if(decl instanceof AbstractCollectionTypeDecl) {
            return this.checkCollectionConstructor(env, decl, exp);
        }
        else if(decl instanceof ConstructableTypeDecl) {
            return this.checkSpecialConstructableConstructor(env, decl, exp);
        }
        else if(decl instanceof PrimitiveEntityTypeDecl) {
            return this.checkPrimitiveConstructor(env, decl, exp);
        }
        else if(decl instanceof TypedeclTypeDecl) {
            return this.checkSpecialTypeDeclConstructor(env, decl, exp);
        }
        else {
            if(decl instanceof EntityTypeDecl) {
                return this.checkStandardConstructor(env, decl.fields, exp);
            }
            else if(decl instanceof DatatypeMemberEntityTypeDecl) {
                return this.checkStandardConstructor(env, decl.fields, exp);
            }
            else {
                this.reportError(exp.sinfo, `Invalid type for constructor expression -- ${exp.ctype.emit()}`);
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
        }
        */
        assert(false, "Not Implemented -- checkConstructorPrimaryExpression");
    }
    
    private checkConstructorEListExpression(env: TypeEnvironment, exp: ConstructorEListExpression, infertype: TypeInferContext | undefined): TypeSignature {
        /*
        if(infertype === undefined) {
            const ttypes = exp.args.args.map((arg) => this.checkExpression(env, (arg as PositionalArgumentValue).exp, undefined));
            const rel = new EListTypeSignature(exp.sinfo, ttypes);

            return exp.setType(rel);
        }
        else {
            let iopts: (TypeSignature | undefined)[] = [];
            if(infertype instanceof EListStyleTypeInferContext) {
                let itype = infertype as EListStyleTypeInferContext;
                iopts = itype.elist;
            }
            else {
                const itype = (infertype as SimpleTypeInferContext).ttype;
                if(!(itype instanceof EListTypeSignature)) {
                    this.reportError(exp.sinfo, `Invalid type for list constructor -- ${itype.emit()}`);
                    return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
                }

                iopts = itype.entries;
            }

            if(iopts.length !== exp.args.args.length) {
                this.reportError(exp.sinfo, `List constructor expects ${iopts.length} arguments but got ${exp.args.args.length}`);
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }

            let ttypes: TypeSignature[] = [];
            for(let i = 0; i < exp.args.args.length; ++i) {
                const etype = this.checkExpression(env, (exp.args.args[i] as PositionalArgumentValue).exp, i < iopts.length ? new SimpleTypeInferContext(iopts[i] as TypeSignature) : undefined);
                
                if(iopts[i] === undefined) {
                    ttypes.push(etype);
                }
                else {
                    this.checkError(exp.sinfo, !(etype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(etype, iopts[i] as TypeSignature, this.constraints), `Type ${etype.emit()} is not a subtype of ${(iopts[i] as TypeSignature).emit()} as expected`);
                    ttypes.push(iopts[i] as TypeSignature);
                }
            }

            const rel = new EListTypeSignature(exp.sinfo, ttypes);
            return exp.setType(rel);
        }
        */
        assert(false, "Not Implemented -- checkConstructorEListExpression");
    }

    private checkConstructorLambdaExpression(env: TypeEnvironment, exp: ConstructorLambdaExpression, infertype: TypeSignature | undefined): TypeSignature {
        /*
        let itype: LambdaTypeSignature | undefined = undefined;
        if(infertype !== undefined && infertype instanceof LambdaTypeSignature && infertype.params.length === exp.invoke.params.length) {
            itype = infertype;
        }
        
        let argsok = true;
        let args: VarInfo[] = [];
        let params: LambdaParameterSignature[] = [];
        let rtype: TypeSignature = new ErrorTypeSignature(exp.sinfo, undefined);

        if(exp.invoke.isAuto) {
            if(itype == undefined || itype.params.length !== exp.invoke.params.length) {
                argsok = false;
                this.reportError(exp.sinfo, `Cannot infer type for lambda constructor`);
            }
            else {
                for(let i = 0; i < itype.params.length; ++i) {
                    const iptype = itype.params[i];
                    const ipdecl = exp.invoke.params[i];

                    args.push(new VarInfo(ipdecl.name, iptype.type, [], true, true, ipdecl.isRefParam));
                    params.push(new LambdaParameterSignature(ipdecl.name, iptype.type, ipdecl.isRefParam, ipdecl.isRestParam));
                }
            }
        }
        else {
            for(let i = 0; i < exp.invoke.params.length; ++i) {
                const ipdecl = exp.invoke.params[i];

                args.push(new VarInfo(ipdecl.name, ipdecl.type, [], true, true, ipdecl.isRefParam));
                params.push(new LambdaParameterSignature(ipdecl.name, ipdecl.type, ipdecl.isRefParam, ipdecl.isRestParam));
            }
        }

        if(!(exp.invoke.resultType instanceof AutoTypeSignature)) {
            rtype = exp.invoke.resultType;
        }
        else {
            if(itype !== undefined) {
                rtype = itype.resultType;
            }
            else {
                this.reportError(exp.sinfo, `Cannot infer type for lambda constructor`);
            }
        }

        //check that we don't have a lambda parameter that takes a lambda
        for(let i = 0; i < params.length; ++i) {
            const ptype = params[i].type;
            if(ptype instanceof LambdaTypeSignature) {
                this.reportError(exp.sinfo, `Lambda parameters cannot be a lambda type --  ${params[i].name}`);
                argsok = false;
            }
        }

        if(!argsok || (rtype instanceof ErrorTypeSignature)) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }
        else {
            const ltype = new LambdaTypeSignature(exp.sinfo, exp.invoke.recursive, exp.invoke.name as "fn" | "pred", params, rtype);

            const ireturn = this.relations.convertTypeSignatureToTypeInferCtx(rtype);
            const lenv = TypeEnvironment.createInitialLambdaEnv(args, rtype, ireturn, env);
            this.checkBodyImplementation(lenv, exp.invoke.body);
            
            return exp.setType(ltype);
        }
        */
        assert(false, "Not Implemented -- checkConstructorLambdaExpression");
    }

    private checkLambdaInvokeExpression(env: TypeEnvironment, refok: boolean, exp: LambdaInvokeExpression): TypeSignature {
        /*
        let llvar = env.resolveLocalVarInfoFromSrcName(exp.name);
        if(llvar === undefined) {
            exp.isCapturedLambda = true;
            llvar = env.resolveLambdaCaptureVarInfoFromSrcName(exp.name);
        }

        if(llvar === undefined) {
            this.reportError(exp.sinfo, `Could not find lambda variable ${exp.name}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        if(!(llvar.decltype instanceof LambdaTypeSignature)) {
            this.reportError(exp.sinfo, `Variable ${exp.name} is not a lambda value`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const lsig = llvar.decltype as LambdaTypeSignature;

        const arginfo = this.checkLambdaArgumentList(exp.sinfo, env, refok, exp.args.args, lsig.params);
        exp.lambda = llvar.decltype;
        exp.arginfo = arginfo.arginfo;
        exp.resttype = arginfo.resttype;
        exp.restinfo = arginfo.restinfo;

        return exp.setType(lsig.resultType);
        */
        assert(false, "Not Implemented -- checkLambdaInvokeExpression");
    }
/*
    private checkSpecialConstructorExpressionNoInfer(env: TypeEnvironment, exp: SpecialConstructorExpression): TypeSignature {
        const corens = this.relations.assembly.getCoreNamespace();

        const etype = this.checkExpression(env, exp.arg, undefined);
        if((etype instanceof ErrorTypeSignature)) {
            this.reportError(exp.sinfo, `Invalid type for special constructor -- got ${etype.emit()}`);
            return exp.setType(etype);
        }

        if(exp.rop === "some") {
            exp.constype = new NominalTypeSignature(exp.sinfo, undefined, corens.typedecls.find((td) => td.name === "Some") as SomeTypeDecl, [etype]);
            return exp.setType(exp.constype);
        }
        else {
            this.reportError(exp.sinfo, "Cannot infer type for special Ok/Err constructor");
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }
    }
*/
    private checkSpecialConstructorExpression(env: TypeEnvironment, exp: SpecialConstructorExpression, infertype: TypeSignature | undefined): TypeSignature {
        /*
        if(infertype === undefined || !(infertype instanceof NominalTypeSignature)) {
            return this.checkSpecialConstructorExpressionNoInfer(env, exp);
        }
        else {
            const ninfer = infertype as NominalTypeSignature;
            if(exp.rop === "some") {
                if(ninfer.decl instanceof SomeTypeDecl) {
                    const ttype = ninfer.alltermargs[0];
                    const etype = this.checkExpression(env, exp.arg, new SimpleTypeInferContext(ttype));
                    this.checkError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Some constructor argument is not a subtype of ${ttype.emit()}`);

                    exp.constype = ninfer;
                    return exp.setType(ninfer);
                }
                else if(ninfer.decl instanceof OptionTypeDecl) {
                    const ttype = ninfer.alltermargs[0];
                    const etype = this.checkExpression(env, exp.arg, new SimpleTypeInferContext(ttype));
                    this.checkError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Some constructor argument is not a subtype of ${ttype.emit()}`);

                    exp.constype = new NominalTypeSignature(exp.sinfo, undefined, this.relations.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Some") as SomeTypeDecl, [ttype]);
                    return exp.setType(exp.constype);
                }
                else {
                    return this.checkSpecialConstructorExpressionNoInfer(env, exp);
                }
            }
            else if(exp.rop === "ok") {
                if(ninfer.decl instanceof OkTypeDecl) {
                    const ttype = ninfer.alltermargs[0];
                    const etype = this.checkExpression(env, exp.arg, new SimpleTypeInferContext(ttype));
                    this.checkError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Ok constructor argument is not a subtype of ${ttype.emit()}`);

                    exp.constype = ninfer;
                    return exp.setType(ninfer);
                }
                else if(ninfer.decl instanceof ResultTypeDecl) {
                    const ttype = ninfer.alltermargs[0];
                    const etype = this.checkExpression(env, exp.arg, new SimpleTypeInferContext(ttype));
                    this.checkError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Ok constructor argument is not a subtype of ${ttype.emit()}`);

                    exp.constype = new NominalTypeSignature(exp.sinfo, undefined, ninfer.decl.getOkType(), [ttype, ninfer.alltermargs[1]]);
                    return exp.setType(exp.constype);
                }
                else {
                    this.reportError(exp.sinfo, `Cannot infer type for special Ok constructor -- got ${infertype.emit()}`);
                    return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
                }
            }
            else {
                if(ninfer.decl instanceof FailTypeDecl) {
                    const ttype = ninfer.alltermargs[1];
                    const etype = this.checkExpression(env, exp.arg, new SimpleTypeInferContext(ttype));
                    this.checkError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Fail constructor argument is not a subtype of ${ttype.emit()}`);

                    exp.constype = ninfer;
                    return exp.setType(ninfer);
                }
                else if(ninfer.decl instanceof ResultTypeDecl) {
                    const ttype = ninfer.alltermargs[1];
                    const etype = this.checkExpression(env, exp.arg, new SimpleTypeInferContext(ttype));
                    this.checkError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, ttype, this.constraints), `Err constructor argument is not a subtype of ${ttype.emit()}`);

                    exp.constype = new NominalTypeSignature(exp.sinfo, undefined, ninfer.decl.getFailType(), [ninfer.alltermargs[0], ttype]);
                    return exp.setType(exp.constype);
                }
                else {
                    this.reportError(exp.sinfo, `Cannot infer type for special Fail constructor -- got ${infertype.emit()}`);
                    return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
                }
            }
        }
        */
        assert(false, "Not Implemented -- checkSpecialConstructorExpression");
    }

    private checkCallNamespaceFunctionExpression(env: TypeEnvironment, refok: boolean, exp: CallNamespaceFunctionExpression): TypeSignature {
        /*
        const fdecl = this.relations.assembly.resolveNamespaceFunction(exp.ns, exp.name);
        if(fdecl === undefined) {
            this.reportError(exp.sinfo, `Could not find namespace function ${exp.ns.emit()}::${exp.name}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const imapper = this.checkTemplateBindingsOnInvoke(exp.sinfo, env, exp.terms, fdecl, undefined);
        if(imapper === undefined) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const arginfo = this.checkArgumentList(exp.sinfo, env, refok, exp.args.args, fdecl.params, imapper);
        exp.shuffleinfo = arginfo.shuffleinfo;
        exp.resttype = arginfo.resttype;
        exp.restinfo = arginfo.restinfo;

        return exp.setType(fdecl.resultType.remapTemplateBindings(imapper));
        */
        assert(false, "Not Implemented -- checkCallNamespaceFunctionExpression");
    }

    private checkCallTypeFunctionExpression(env: TypeEnvironment, refok: boolean, exp: CallTypeFunctionExpression): TypeSignature {
        /*
        const oktype = this.checkTypeSignature(exp.ttype);
        if(!oktype) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }
        
        const fdecl = this.relations.resolveTypeFunction(exp.ttype, exp.name, this.constraints);
        if(fdecl === undefined) {
            this.reportError(exp.sinfo, `Could not find type scoped function ${exp.ttype.emit()}::${exp.name}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        //special case for type Foo = String of ... Foo::from
        if(fdecl.member === null) {
            if(exp.args.args.length !== 1 || !(exp.args.args[0] instanceof PositionalArgumentValue)) {
                this.reportError(exp.sinfo, `Conversion from expects 1 argument`);
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }

            const etype = this.checkExpression(env, exp.args.args[0].exp, undefined);
            this.checkError(exp.sinfo, !(etype instanceof NominalTypeSignature), `Invalid arg type for conversion from ${etype.emit()} -- converting to ${fdecl.typeinfo.tsig.emit()}`);

            if(etype instanceof NominalTypeSignature) {
                if(etype.tkeystr === "String" || etype.tkeystr === "CString") {
                    this.checkError(exp.sinfo, !this.relations.areSameTypes((fdecl.typeinfo.tsig.decl as TypedeclTypeDecl).valuetype, etype), `Invalid arg type for conversion from ${etype.emit()} -- converting to ${fdecl.typeinfo.tsig.emit()}`);
                }
                else if(etype.decl instanceof TypedeclTypeDecl) {
                    this.checkError(exp.sinfo, !this.relations.areSameTypes((fdecl.typeinfo.tsig.decl as TypedeclTypeDecl).valuetype, (etype.decl as TypedeclTypeDecl).valuetype), `Invalid arg type for conversion from ${etype.emit()} -- converting to ${fdecl.typeinfo.tsig.emit()}`);
                }
                else {
                    this.reportError(exp.sinfo, `Invalid arg type for conversion from ${etype.emit()} -- converting to ${fdecl.typeinfo.tsig.emit()}`);
                }
            }

            exp.isSpecialCall = true;
            exp.resolvedDeclType = fdecl.typeinfo.tsig;
            exp.shuffleinfo = [[0, etype]];

            return exp.setType(fdecl.typeinfo.tsig);
        }
        else {
            const refinemap = this.relations.generateTemplateMappingForTypeDecl(fdecl.typeinfo.tsig as NominalTypeSignature);
            const imapper = this.checkTemplateBindingsOnInvoke(exp. sinfo, env, exp.terms, fdecl.member, refinemap);
            if(imapper === undefined) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }

            const fullmapper = TemplateNameMapper.merge(fdecl.typeinfo.mapping, imapper);
            const arginfo = this.checkArgumentList(exp.sinfo, env, refok, exp.args.args, fdecl.member.params, fullmapper);
            exp.resolvedDeclType = fdecl.typeinfo.tsig;
            exp.shuffleinfo = arginfo.shuffleinfo;
            exp.resttype = arginfo.resttype;
            exp.restinfo = arginfo.restinfo;

            return exp.setType(fdecl.member.resultType.remapTemplateBindings(fullmapper));
        }
        */
        assert(false, "Not Implemented -- checkCallTypeFunctionExpression");
    }

    private checkParseAsTypeExpression(env: TypeEnvironment, exp: ParseAsTypeExpression): TypeSignature {
        /*
        const oktype = this.checkTypeSignature(exp.ttype);
        const etype = this.checkExpression(env, exp.exp, oktype ? new SimpleTypeInferContext(exp.ttype) : undefined);
        if(!oktype) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        this.checkError(exp.sinfo, etype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(etype, exp.ttype, this.constraints), `ParseAsType expression is not a subtype of ${exp.ttype.emit()}`);
        return exp.setType(exp.ttype);
        */
        assert(false, "Not Implemented -- checkParseAsTypeExpression");
    }

    ////////
    // Postfix Expressions
    private checkPostfixAccessFromName(env: TypeEnvironment, exp: PostfixAccessFromName, rcvrtype: TypeSignature): TypeSignature {
        /*
        const finfo = this.relations.resolveTypeField(rcvrtype, exp.name, this.constraints);
        if(finfo === undefined) {
            this.reportError(exp.sinfo, `Could not find field ${exp.name} in type ${rcvrtype.emit()}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }
        else {
            exp.declaredInType = finfo.typeinfo.tsig;
            exp.fieldDecl = finfo.member;
        }

        return exp.setType(finfo.member.declaredType.remapTemplateBindings(finfo.typeinfo.mapping));
        */
        assert(false, "Not Implemented -- checkPostfixAccessFromName");
    }

    private checkPostfixProjectFromNames(env: TypeEnvironment, exp: PostfixProjectFromNames, rcvrtype: TypeSignature, infertype: TypeInferContext | undefined): TypeSignature {
        assert(false, "Not Implemented -- checkPostfixProjectFromNames");
    }

    private checkPostfixAccessFromIndex(env: TypeEnvironment, exp: PostfixAccessFromIndex, rcvrtype: TypeSignature): TypeSignature {
        /*
        if(!(rcvrtype instanceof EListTypeSignature)) {
            this.reportError(exp.sinfo, `Cannot access index from non-elist type ${rcvrtype.emit()}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        if(exp.idx >= rcvrtype.entries.length) {
            this.reportError(exp.sinfo, `Index ${exp.idx} out of bounds for elist type ${rcvrtype.emit()}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        return exp.setType(rcvrtype.entries[exp.idx]);
        */
        assert(false, "Not Implemented -- checkPostfixAccessFromIndex");
    }

    private checkPostfixIsTest(env: TypeEnvironment, exp: PostfixIsTest, rcvrtype: TypeSignature): TypeSignature {
        /*
        const splits = this.processITestAsBoolean(exp.sinfo, env, rcvrtype, exp.ttest);
        this.checkError(exp.sinfo, !splits.ttrue, "Test is never true");
        this.checkError(exp.sinfo, !splits.tfalse, "Test is never false");

        return exp.setType(this.getWellKnownType("Bool"));
        */
        assert(false, "Not Implemented -- checkPostfixIsTest");
    }

    private checkPostfixAsConvert(env: TypeEnvironment, exp: PostfixAsConvert, rcvrtype: TypeSignature): TypeSignature {
        /*
        const splits = this.processITestAsConvert(exp.sinfo, env, rcvrtype, exp.ttest);
        this.checkError(exp.sinfo, splits.ttrue === undefined, "Convert always fails");
        //if always true then this is an upcast and OK!

        return exp.setType(splits.ttrue || new ErrorTypeSignature(exp.sinfo, undefined));
        */
        assert(false, "Not Implemented -- checkPostfixAsConvert");
    }

    private checkPostfixAssignFields(env: TypeEnvironment, exp: PostfixAssignFields, rcvrtype: TypeSignature): TypeSignature {
        /*
        const [okupdate, isdirect] = TypeChecker.isTypeUpdatable(rcvrtype);
        if(!okupdate) {
            this.reportError(rcvrtype.sinfo, `Expression is not an updatable type (entity/concept or datatype)`);
            return rcvrtype;
        }

        const updates = exp.updates.map((upd) => {
            const bname = "$" + upd[0];
            const ftype = this.getFieldType(rcvrtype, upd[0]);

            if(ftype === undefined) {
                this.reportError(exp.sinfo, `Field ${upd[0]} is not a member of type ${rcvrtype.emit()}`);
                return {fieldname: upd[0], fieldtype: new ErrorTypeSignature(exp.sinfo, undefined), etype: new ErrorTypeSignature(exp.sinfo, undefined)};
            }

            const cenv = env.pushNewLocalBinderScope(bname, ftype);
            const etype = this.checkExpression(cenv, upd[1], new SimpleTypeInferContext(ftype));
            if(!(etype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(etype, ftype, this.constraints)) {
                this.reportError(exp.sinfo, `Expression of type ${etype.emit()} cannot be assigned to field ${upd[0]} of type ${ftype.emit()}`);
            }

            return {fieldname: upd[0], fieldtype: ftype, etype: etype};
        });

        exp.updatetype = rcvrtype;
        exp.updateinfo = updates;
        exp.isdirect = isdirect;

        return rcvrtype;
        */
        assert(false, "Not Implemented -- checkPostfixAssignFields");
    }

    /*
    private postfixInvokeStaticResolve(env: TypeEnvironment, mdeclaration: MemberLookupInfo<MethodDecl>, name: string, resolvefrom: TypeSignature): MemberLookupInfo<MethodDecl> | undefined {
        /*
        if(mdeclaration.member.attributes.every((attr) => attr.name !== "virtual" && attr.name !== "abstract")) {
            return mdeclaration; //There is no overloading so the declaration is the implementation!
        }

        const tdecl = (resolvefrom as NominalTypeSignature).decl;
        if(tdecl instanceof AbstractEntityTypeDecl) {
            return this.relations.resolveTypeMethodDeclaration(resolvefrom, name, this.constraints); //a concrete subtype so we can resolve statically
        }
    }
    */

    private checkPostfixInvoke(env: TypeEnvironment, refok: boolean, exp: PostfixInvoke, rcvrtype: TypeSignature): TypeSignature {
        /*
        let resolvefrom = rcvrtype;
        if(exp.specificResolve !== undefined) {
            const specificok = this.checkTypeSignature(exp.specificResolve);
            if(specificok) {
                resolvefrom = exp.specificResolve
            }
        }
        
        const mresolve = this.relations.resolveTypeMethodDeclaration(resolvefrom, exp.name, this.constraints);
        if(mresolve === undefined) {
            this.reportError(exp.sinfo, `Could not find method ${exp.name} in type ${rcvrtype.emit()}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        if(mresolve.member.isThisRef) {
            this.reportError(exp.sinfo, `Method ${exp.name} is a "ref" method and cannot be called without a ref rcvr`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const refinemap = this.relations.generateTemplateMappingForTypeDecl(mresolve.typeinfo.tsig);
        const imapper = this.checkTemplateBindingsOnInvoke(exp.sinfo, env, exp.terms, mresolve.member, refinemap);
        if(imapper === undefined) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const fullmapper = TemplateNameMapper.merge(mresolve.typeinfo.mapping, imapper);
        const arginfo = this.checkArgumentList(exp.sinfo, env, refok, exp.args.args, mresolve.member.params, fullmapper);
        exp.shuffleinfo = arginfo.shuffleinfo;
        exp.resttype = arginfo.resttype;
        exp.restinfo = arginfo.restinfo;

        if(exp.specificResolve !== undefined) {
            const rrt = this.relations.resolveTypeMethodImplementation(resolvefrom, exp.name, this.constraints);
            this.checkError(exp.sinfo, rrt === undefined, `Method ${exp.name} is not specifically resolvable from type ${resolvefrom.emit()}`);

            if(rrt !== undefined) { 
                exp.resolvedTrgt = rrt.typeinfo.tsig;
            }
        }
        else {
            const smresolve = this.postfixInvokeStaticResolve(env, mresolve, exp.name, resolvefrom);
            if(smresolve !== undefined) {
                exp.resolvedTrgt = smresolve.typeinfo.tsig;
                exp.resolvedMethod = smresolve.member;
            }
        }

        return exp.setType(mresolve.member.resultType.remapTemplateBindings(fullmapper));
        */
        assert(false, "Not Implemented -- checkPostfixInvoke");
    }

    private checkPostfixOp(env: TypeEnvironment, refok: boolean, exp: PostfixOp, typeinfer: TypeInferContext | undefined): TypeSignature {
        let ctype = this.checkExpression(env, exp.rootExp, undefined);
        if(ctype instanceof ErrorTypeSignature) {
            return exp.setType(ctype);
        }

        const refokpreops = exp.ops.slice(0, exp.ops.length - 1).every((op) => {
            const ttag = op.tag;
            return (ttag === PostfixOpTag.PostfixAccessFromName) || (ttag === PostfixOpTag.PostfixAccessFromIndex) || (ttag === PostfixOpTag.PostfixAsConvert);
        });
        const refokops = refok && refokpreops && exp.ops[exp.ops.length - 1].tag === PostfixOpTag.PostfixInvoke;

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
                case PostfixOpTag.PostfixAccessFromIndex: {
                    ctype = this.checkPostfixAccessFromIndex(env, op as PostfixAccessFromIndex, ctype);
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
                case PostfixOpTag.PostfixOfOperator: {
                    assert(false, "Of operator not implemented in postfix expressions");
                    break;
                }
                case PostfixOpTag.PostfixInvoke: {
                    ctype = this.checkPostfixInvoke(env, refokops, op as PostfixInvoke, ctype);
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

    private resolveUnderlyingType(ttype: TypeSignature): TypeSignature | undefined {
        if(this.relations.isPrimitiveType(ttype)) {
            return ttype;
        }
        else if(this.relations.isEnumType(ttype)) {
            return ttype;
        }
        else if(this.relations.isTypeDeclType(ttype)) {
            return this.relations.getTypeDeclValueType(ttype);
        }
        else if(ttype instanceof TemplateTypeSignature) {
            return ttype;
        }
        else {
            return undefined;
        }
    }

    private checkPrefixNotOpExpression(env: TypeEnvironment, exp: PrefixNotOpExpression): TypeSignature {
        const etype = this.checkExpression(env, exp.exp, undefined);
        if(etype instanceof ErrorTypeSignature) {
            return exp.setType(etype);
        }

        this.checkError(exp.sinfo, !this.relations.isBooleanType(etype), "Prefix Not operator requires a Bool based type");
        
        exp.opertype = this.resolveUnderlyingType(etype);
        return exp.setType(etype);
    }

    private checkPrefixNegateOrPlusOpExpression(env: TypeEnvironment, exp: PrefixNegateOrPlusOpExpression): TypeSignature {
        const etype = this.checkExpression(env, exp.exp, undefined);
        if(etype instanceof ErrorTypeSignature) {
            return exp.setType(etype);
        }

        if(this.checkError(exp.sinfo, !this.relations.isNumericType(etype, this.constraints), "Prefix Negate/Plus operator requires a unique numeric type")) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        exp.opertype = this.resolveUnderlyingType(etype);
        return exp.setType(etype);
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

        if(this.checkError(lhs.sinfo, !this.relations.isNumericType(tlhs, this.constraints), "Binary operator requires a unique numeric type")) {
            return [false, tlhs, trhs];
        }
        if(this.checkError(rhs.sinfo, !this.relations.isNumericType(trhs, this.constraints), "Binary operator requires a unique numeric type")) {
            return [false, tlhs, trhs];
        }

        return [true, tlhs, trhs];
    }

    private checkBinAddExpression(env: TypeEnvironment, exp: BinAddExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }
        
        if(this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs), "Addition operator requires 2 arguments of the same type")) {
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

        if(this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs), "Subtraction operator requires 2 arguments of the same type")) {
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
            if(this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs), "Multiplication operator requires 2 arguments of the same type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            res = tlhs;
        }
        else if(this.relations.isTypeDeclType(tlhs) && this.relations.isPrimitiveType(trhs)) {
            const baselhs = this.relations.getTypeDeclValueType(tlhs);
            if(this.checkError(exp.sinfo, baselhs === undefined || !this.relations.areSameTypes(baselhs, trhs), "Multiplication operator requires a unit-less argument that matches underlying unit type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            res = tlhs
        }
        else if(this.relations.isPrimitiveType(tlhs) && this.relations.isTypeDeclType(trhs)) {
            const baserhs = this.relations.getTypeDeclValueType(trhs);
            if(this.checkError(exp.sinfo, baserhs === undefined || !this.relations.areSameTypes(tlhs, baserhs), "Multiplication operator requires a unit-less argument that matches underlying unit type")) {
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
            if(this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs), "Division operator requires 2 arguments of the same type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            res = tlhs;
        }
        else if(this.relations.isTypeDeclType(tlhs) && this.relations.isPrimitiveType(trhs)) {
            const baselhs = this.relations.getTypeDeclValueType(tlhs);
            if(this.checkError(exp.sinfo, baselhs === undefined || !this.relations.areSameTypes(baselhs, trhs), "Division operator requires a unit-less divisor argument that matches the underlying unit type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            res = tlhs
        }
        else if(this.relations.isTypeDeclType(tlhs) && this.relations.isTypeDeclType(trhs)) {
            if(this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs), "Division operator requires 2 arguments of the same type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            const basetype = this.relations.getTypeDeclValueType(trhs);
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
        /*
        const lhstype = this.checkExpression(env, exp.lhs, undefined);
        const rhstype = this.checkExpression(env, exp.rhs, undefined);

        if (lhstype instanceof ErrorTypeSignature || rhstype instanceof ErrorTypeSignature) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        const action = this.checkValueEq(exp.lhs, lhstype, exp.rhs, rhstype);
        if (action[0] === "err") {
            this.reportError(exp.sinfo, `Types ${lhstype.emit()} and ${rhstype.emit()} are not comparable`);
        }
        else {
            exp.operkind = action[0];
            exp.opertype = this.resolveUnderlyingType(action[1]);
        }

        return exp.setType(this.getWellKnownType("Bool"));
        */
        assert(false, "Not Implemented -- checkBinKeyEqExpression");
    }

    private checkBinKeyNeqExpression(env: TypeEnvironment, exp: BinKeyNeqExpression): TypeSignature {
        /*
        const lhstype = this.checkExpression(env, exp.lhs, undefined);
        const rhstype = this.checkExpression(env, exp.rhs, undefined);

        if (lhstype instanceof ErrorTypeSignature || rhstype instanceof ErrorTypeSignature) {
            return exp.setType(this.getWellKnownType("Bool"));
        }
        
        const action = this.checkValueEq(exp.lhs, lhstype, exp.rhs, rhstype);
        if (action[0] === "err") {
            this.reportError(exp.sinfo, `Types ${lhstype.emit()} and ${rhstype.emit()} are not comparable`);
        }
        else {
            exp.operkind = action[0];
            exp.opertype = this.resolveUnderlyingType(action[1]);
        }

        return exp.setType(this.getWellKnownType("Bool"));
        */
        assert(false, "Not Implemented -- checkBinKeyNeqExpression");
    }

    private checkKeyCompareEqExpression(env: TypeEnvironment, exp: KeyCompareEqExpression): TypeSignature {
        /*
        const ktypeok = this.checkTypeSignature(exp.ktype);

        const tlhs = this.checkExpression(env, exp.lhs, ktypeok ? exp.ktype : undefined);
        const trhs = this.checkExpression(env, exp.rhs, ktypeok ? exp.ktype : undefined);

        if(ktypeok) {
            this.checkError(exp.sinfo, !this.relations.isKeyType(tlhs, this.constraints) || !this.relations.areSameTypes(tlhs, exp.ktype), `Type ${tlhs.emit()} is not a (keytype) of ${exp.ktype.emit()}`);
            this.checkError(exp.sinfo, !this.relations.isKeyType(trhs, this.constraints) || !this.relations.areSameTypes(trhs, exp.ktype), `Type ${trhs.emit()} is not a (keytype) of ${exp.ktype.emit()}`);
        
            exp.optype = this.resolveUnderlyingType(exp.ktype);
        }

        return exp.setType(this.getWellKnownType("Bool"));
        */
        assert(false, "Not Implemented -- checkKeyCompareEqExpression");
    }

    private checkKeyCompareLessExpression(env: TypeEnvironment, exp: KeyCompareLessExpression): TypeSignature {
        /*
        const ktypeok = this.checkTypeSignature(exp.ktype);

        const tlhs = this.checkExpression(env, exp.lhs, ktypeok ? exp.ktype : undefined);
        const trhs = this.checkExpression(env, exp.rhs, ktypeok ? exp.ktype : undefined);

        if(ktypeok) {
            this.checkError(exp.sinfo, !this.relations.isKeyType(tlhs, this.constraints) || !this.relations.areSameTypes(tlhs, exp.ktype), `Type ${tlhs.emit()} is not a (keytype) of ${exp.ktype.emit()}`);
            this.checkError(exp.sinfo, !this.relations.isKeyType(trhs, this.constraints) || !this.relations.areSameTypes(trhs, exp.ktype), `Type ${trhs.emit()} is not a (keytype) of ${exp.ktype.emit()}`);

            exp.optype = this.resolveUnderlyingType(exp.ktype);
        }

        return exp.setType(this.getWellKnownType("Bool"));
        */
        assert(false, "Not Implemented -- checkKeyCompareLessExpression");
    }

    private checkNumericEqExpression(env: TypeEnvironment, exp: NumericEqExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs), "Operator == requires 2 arguments of the same type");
        
        exp.opertype = this.resolveUnderlyingType(tlhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkNumericNeqExpression(env: TypeEnvironment, exp: NumericNeqExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs), "Operator != requires 2 arguments of the same type");
        
        exp.opertype = this.resolveUnderlyingType(tlhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkNumericLessExpression(env: TypeEnvironment, exp: NumericLessExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs), "Operator < requires 2 arguments of the same type");
        
        exp.opertype = this.resolveUnderlyingType(tlhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkNumericLessEqExpression(env: TypeEnvironment, exp: NumericLessEqExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs), "Operator <= requires 2 arguments of the same type");
        
        exp.opertype = this.resolveUnderlyingType(tlhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkNumericGreaterExpression(env: TypeEnvironment, exp: NumericGreaterExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs), "Operator > requires 2 arguments of the same type");
        
        exp.opertype = this.resolveUnderlyingType(tlhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkNumericGreaterEqExpression(env: TypeEnvironment, exp: NumericGreaterEqExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs), "Operator >= requires 2 arguments of the same type");
        
        exp.opertype = this.resolveUnderlyingType(tlhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkBinaryBooleanArg(env: TypeEnvironment, arg: Expression): TypeSignature | undefined {
        const targ = this.checkExpression(env, arg, undefined);
        if(targ instanceof ErrorTypeSignature) {
            return undefined;
        }

        this.checkError(arg.sinfo, !this.relations.isBooleanType(targ), "Binary operator requires a Bool type");

        return targ;
    }

    private checkBinLogicAndExpression(env: TypeEnvironment, exp: LogicAndExpression): TypeSignature {
        const etypes = exp.exps.map((arg) => this.checkBinaryBooleanArg(env, arg));
        
        const oftype = etypes.find((t) => t !== undefined);
        if(oftype === undefined) {
            return exp.setType(this.getWellKnownType("Bool"));    
        }
        else {
            const ft = etypes.every((t) => t !== undefined && t.tkeystr === oftype.tkeystr) ? oftype : this.getWellKnownType("Bool");
            return exp.setType(ft);
        }
    }

    private checkBinLogicOrExpression(env: TypeEnvironment, exp: LogicOrExpression): TypeSignature {
        const etypes = exp.exps.map((arg) => this.checkBinaryBooleanArg(env, arg));
        
        const oftype = etypes.find((t) => t !== undefined);
        if(oftype === undefined) {
            return exp.setType(this.getWellKnownType("Bool"));    
        }
        else {
            const ft = etypes.every((t) => t !== undefined && t.tkeystr === oftype.tkeystr) ? oftype : this.getWellKnownType("Bool");
            return exp.setType(ft);
        }
    }

    private checkMapEntryConstructorExpression(env: TypeEnvironment, exp: MapEntryConstructorExpression, infertype: TypeSignature | undefined): TypeSignature {
        /*
        const ioktype = infertype !== undefined && (infertype instanceof NominalTypeSignature) && (infertype.decl instanceof MapEntryTypeDecl);
        if(!ioktype) {
            this.reportError(exp.sinfo, `MapEntryConstructor requires a MapEntry type as the inferred type`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const iktype: TypeSignature = infertype.alltermargs[0];
        const ktype = this.checkExpression(env, exp.kexp, new SimpleTypeInferContext(iktype));
        this.checkError(exp.sinfo, !this.relations.isKeyType(iktype, this.constraints), `MapEntryConstructor requires a key type as the first argument`); 
        this.checkError(exp.sinfo, ktype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(ktype, iktype, this.constraints), `MapEntryConstructor key expression is not a subtype of ${iktype.emit()}`);

        let ivtype: TypeSignature = infertype.alltermargs[1];
        const vtype = this.checkExpression(env, exp.vexp, new SimpleTypeInferContext(ivtype));
        this.checkError(exp.sinfo, vtype instanceof ErrorTypeSignature || !this.relations.isSubtypeOf(vtype, ivtype, this.constraints), `MapEntryConstructor value expression is not a subtype of ${ivtype.emit()}`);

        exp.ctype = infertype;
        return exp.setType(infertype);
        */
        assert(false, "Not Implemented -- checkMapEntryConstructorExpression");
    }

    /*
    private checkConditionalValueExpression(env: TypeEnvironment, exp: ConditionalValueExpression, typeinfer: TypeInferContext | undefined): TypeSignature {
        assert(false, "Not Implemented -- checkConditionalValueExpression");
    }

    private checkShortCircuitAssignRHSITestExpression(env: TypeEnvironment, exp: ShortCircuitAssignRHSITestExpression, typeinfer: TypeInferContext | undefined): TypeSignature {
        assert(false, "Not Implemented -- checkShortCircuitAssignRHSITestExpression");
    }
    */

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
            case ExpressionTag.LiteralChkNatExpression: {
                return this.checkLiteralChkNatExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralChkIntExpression: {
                return this.checkLiteralChkIntExpression(env, exp as LiteralSimpleExpression);
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
            case ExpressionTag.LiteralTZDateTimeExpression: {
                return this.checkLiteralTZDateTimeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralTAITimeExpression: {
                return this.checkLiteralTAITimeExpression(env, exp as LiteralSimpleExpression);
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
            case ExpressionTag.LiteralISOTimeStampExpression: {
                return this.checkLiteralISOTimeStampExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaDateTimeExpression: {
                return this.checkLiteralDeltaDateTimeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaISOTimeStampExpression: {
                return this.checkLiteralDeltaISOTimeStampExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaSecondsExpression: {
                return this.checkLiteralDeltaSecondsExpression(env, exp as LiteralSimpleExpression);
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
            case ExpressionTag.LiteralByteExpression: {
                return this.checkLiteralByteExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralCCharExpression: {
                return this.checkLiteralCCharExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUnicodeCharExpression: {
                return this.checkLiteralUnicodeCharExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralStringExpression: {
                return this.checkLiteralStringExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralCStringExpression: {
                return this.checkLiteralCStringExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralFormatStringExpression: {
                return this.checkLiteralFormatStringExpression(env, exp as LiteralFormatStringExpression);
            }
            case ExpressionTag.LiteralFormatCStringExpression: {
                return this.checkLiteralFormatCStringExpression(env, exp as LiteralFormatCStringExpression);
            }
            case ExpressionTag.LiteralPathExpression: {
                return this.checkLiteralPathExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralPathFragmentExpression: {
                return this.checkLiteralPathFragmentExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralGlobExpression: {
                return this.checkLiteralGlobExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralTypeDeclValueExpression: {
                return this.checkLiteralTypeDeclValueExpression(env, exp as LiteralTypeDeclValueExpression);
            }
            case ExpressionTag.LiteralTypedStringExpression: {
                return this.checkLiteralTypedStringExpression(env, exp as LiteralTypedStringExpression);
            }
            case ExpressionTag.LiteralTypedCStringExpression: {
                return this.checkLiteralTypedCStringExpression(env, exp as LiteralTypedCStringExpression);
            }
            case ExpressionTag.LiteralTypedFormatStringExpression: {
                return this.checkLiteralTypedFormatStringExpression(env, exp as LiteralTypedFormatStringExpression);
            }
            case ExpressionTag.LiteralTypedFormatCStringExpression: {
                return this.checkLiteralTypedFormatCStringExpression(env, exp as LiteralTypedFormatCStringExpression);
            }
            case ExpressionTag.AccessEnvValueExpression: {
                return this.checkAccessEnvValueExpression(env, exp as AccessEnvValueExpression);
            }
            case ExpressionTag.TaskAccessIDExpression: {
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
                return this.checkConstructorEListExpression(env, exp as ConstructorEListExpression, typeinfer);
            }
            case ExpressionTag.ConstructorLambdaExpression: {
                return this.checkConstructorLambdaExpression(env, exp as ConstructorLambdaExpression, TypeInferContext.asSimpleType(typeinfer));
            }
            case ExpressionTag.LambdaInvokeExpression: {
                return this.checkLambdaInvokeExpression(env, false, exp as LambdaInvokeExpression);
            }
            case ExpressionTag.SpecialConstructorExpression: {
                return this.checkSpecialConstructorExpression(env, exp as SpecialConstructorExpression, TypeInferContext.asSimpleType(typeinfer));
            }
            case ExpressionTag.CallNamespaceFunctionExpression: {
                return this.checkCallNamespaceFunctionExpression(env, false, exp as CallNamespaceFunctionExpression);
            }
            case ExpressionTag.CallTypeFunctionExpression: {
                return this.checkCallTypeFunctionExpression(env, false, exp as CallTypeFunctionExpression);
            }
            case ExpressionTag.ParseAsTypeExpression: {
                return this.checkParseAsTypeExpression(env, exp as ParseAsTypeExpression);
            }
            case ExpressionTag.PostfixOpExpression: {
                return this.checkPostfixOp(env, false, exp as PostfixOp, typeinfer);
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
            case ExpressionTag.KeyCompareEqExpression: {
                return this.checkKeyCompareEqExpression(env, exp as KeyCompareEqExpression);
            }
            case ExpressionTag.KeyCompareLessExpression: {
                return this.checkKeyCompareLessExpression(env, exp as KeyCompareLessExpression);
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
            case ExpressionTag.LogicAndExpression: {
                return this.checkBinLogicAndExpression(env, exp as LogicAndExpression);
            }
            case ExpressionTag.LogicOrExpression: {
                return this.checkBinLogicOrExpression(env, exp as LogicOrExpression);
            }
            case ExpressionTag.MapEntryConstructorExpression: {
                return this.checkMapEntryConstructorExpression(env, exp as MapEntryConstructorExpression, TypeInferContext.asSimpleType(typeinfer));
            }
            default: {
                assert(exp.tag === ExpressionTag.ErrorExpression, "Unknown expression kind");
                return new ErrorTypeSignature(exp.sinfo, undefined);
            }
        }
    }

    private checkCallRefInvokeExpression(env: TypeEnvironment, exp: CallRefInvokeExpression): TypeSignature {
        /*
        const rcvrtype: TypeSignature = this.checkExpression(env, exp.rcvr, undefined);

        let resolvefrom = rcvrtype;
        if(exp.specificResolve !== undefined) {
            const specificok = this.checkTypeSignature(exp.specificResolve);
            if(specificok) {
                resolvefrom = exp.specificResolve
            }
        }
        
        const mresolve = this.relations.resolveTypeMethodDeclaration(resolvefrom, exp.name, this.constraints);
        if(mresolve === undefined) {
            this.reportError(exp.sinfo, `Could not find method ${exp.name} in type ${rcvrtype.emit()}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        if(!mresolve.member.isThisRef) {
            this.reportError(exp.sinfo, `Method ${exp.name} is not a "ref" method and cannot be called with a ref rcvr`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const rcvrname = exp.rcvr.srcname;
        const [vinfo, isparam] = env.resolveLocalVarInfoFromSrcNameWithIsParam(rcvrname);
        if(vinfo === undefined) {
            this.reportError(exp.sinfo, `Variable ${rcvrname} is not declared`);
        }
        else {
            if((!isparam && vinfo.isConst) || (isparam && !vinfo.isRef)) {
                this.reportError(exp.sinfo, `Variable ${rcvrname} is cannot be updated (is local const or not a ref param)`);
            }
        }

        const refinemap = this.relations.generateTemplateMappingForTypeDecl(mresolve.typeinfo.tsig);
        const imapper = this.checkTemplateBindingsOnInvoke(exp.sinfo, env, exp.terms, mresolve.member, refinemap);
        if(imapper === undefined) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        const fullmapper = TemplateNameMapper.merge(mresolve.typeinfo.mapping, imapper);
        const arginfo = this.checkArgumentList(exp.sinfo, env, true, exp.args.args, mresolve.member.params, fullmapper);
        exp.shuffleinfo = arginfo.shuffleinfo;
        exp.resttype = arginfo.resttype;
        exp.restinfo = arginfo.restinfo;

        if(exp.specificResolve !== undefined) {
            const rrt = this.relations.resolveTypeMethodImplementation(resolvefrom, exp.name, this.constraints);
            this.checkError(exp.sinfo, rrt === undefined, `Method ${exp.name} is not specifically resolvable from type ${resolvefrom.emit()}`);

            exp.resolvedTrgt = (rrt !== undefined) ? rrt.typeinfo.tsig : undefined;
        }
        else {
            const smresolve = this.postfixInvokeStaticResolve(env, mresolve, exp.name, resolvefrom);
            if(smresolve !== undefined) {
                exp.resolvedTrgt = smresolve.typeinfo.tsig;
            }
        }

        return exp.setType(mresolve.member.resultType.remapTemplateBindings(fullmapper));
        */
        assert(false, "Not Implemented -- checkCallRefInvokeExpression");
    }

    private checkCallRefVariableExpression(env: TypeEnvironment, exp: CallRefVariableExpression): TypeSignature {
        return this.checkCallRefInvokeExpression(env, exp);
    }

    private checkCallRefThisExpression(env: TypeEnvironment, exp: CallRefThisExpression): TypeSignature {
        return this.checkCallRefInvokeExpression(env, exp);
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

    private checkBaseRValueExpression(env: TypeEnvironment, exp: Expression, typeinfer: TypeInferContext | undefined): TypeSignature {
        const ttag = exp.tag;

        switch (ttag) {
            case ExpressionTag.CallRefVariableExpression: {
                return this.checkCallRefVariableExpression(env, exp as CallRefVariableExpression);
            }
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
                if(ttag === ExpressionTag.CallNamespaceFunctionExpression) {
                    return this.checkCallNamespaceFunctionExpression(env, true, exp as CallNamespaceFunctionExpression);
                }
                else if(ttag === ExpressionTag.CallTypeFunctionExpression) {
                    return this.checkCallTypeFunctionExpression(env, true, exp as CallTypeFunctionExpression);
                }
                else if(ttag === ExpressionTag.LambdaInvokeExpression) {
                    return this.checkLambdaInvokeExpression(env, true, exp as LambdaInvokeExpression);
                }
                else if(ttag === ExpressionTag.PostfixOpExpression) {
                    return this.checkPostfixOp(env, true, exp as PostfixOp, typeinfer);
                }
                else {
                    return this.checkExpression(env, exp, typeinfer);
                }
            }
        }
    }

    private checkExpressionRHS(env: TypeEnvironment, exp: RValueExpression, typeinfer: TypeInferContext | undefined): TypeSignature {
        const ttag = exp.tag;
        
        if(ttag === RValueExpressionTag.BaseExpression) {
            return this.checkBaseRValueExpression(env, (exp as BaseRValueExpression).exp, typeinfer);
        }
        else if(ttag === RValueExpressionTag.ShortCircuitAssignRHSExpressionFail) {
            assert(false, "Not Implemented -- checkShortCircuitAssignRHSFailExpression");
        }
        else if(ttag === RValueExpressionTag.ShortCircuitAssignRHSExpressionReturn) {
            assert(false, "Not Implemented -- checkShortCircuitAssignRHSReturnExpression");
        }
        else if(ttag === RValueExpressionTag.ConditionalValueExpression) {
            assert(false, "Not Implemented -- checkConditionalValueExpression");
        }
        else {
            assert(false, "Unknown RValueExpression kind");
        }
    }

    /*
    private checkExpressionRootCondition(env: TypeEnvironment, exp: xxx): TypeSignature {
        xxxx;
    }
    */

    private checkEmptyStatement(env: TypeEnvironment, stmt: EmptyStatement): TypeEnvironment {
        return env;
    }

    private checkVariableDeclarationStatement(env: TypeEnvironment, stmt: VariableDeclarationStatement): TypeEnvironment {
        this.checkTypeSignature(stmt.vtype);
        
        return env.addLocalVar(stmt.name, stmt.vtype, "var", false);
    }
    
    private checkVariableMultiDeclarationStatement(env: TypeEnvironment, stmt: VariableMultiDeclarationStatement): TypeEnvironment {
        for(let i = 0; i < stmt.decls.length; ++i) {
            this.checkTypeSignature(stmt.decls[i].vtype);
            env = env.addLocalVar(stmt.decls[i].name, stmt.decls[i].vtype, "var", false);
        }
        return env;
    }

    private checkVariableInitializationStatement(env: TypeEnvironment, stmt: VariableInitializationStatement): TypeEnvironment {
        this.checkTypeSignature(stmt.vtype);

        const itype = !(stmt.vtype instanceof AutoTypeSignature) ? stmt.vtype : undefined;
        const rhs = this.checkExpressionRHS(env, stmt.exp, itype !== undefined ? new SimpleTypeInferContext(itype) : undefined);

        this.checkError(stmt.sinfo, itype !== undefined && !(rhs instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(rhs, itype, this.constraints), `Expression of type ${TypeChecker.safeTypePrint(rhs)} cannot be assigned to variable of type ${TypeChecker.safeTypePrint(itype)}`);
        
        if(stmt.name === "_") {
            return env;
        }
        else {
            stmt.actualtype = itype || rhs;
            return env.addLocalVar(stmt.name, itype || rhs, stmt.vkind, true);
        }
    }

    private checkVariableMultiInitializationStatement(env: TypeEnvironment, stmt: VariableMultiInitializationStatement): TypeEnvironment {
        /*
        for(let i = 0; i < stmt.decls.length; ++i) {
            this.checkTypeSignature(stmt.decls[i].vtype);
        }

        const iopts = stmt.decls.map((decl) => !(decl.vtype instanceof AutoTypeSignature) ? decl.vtype : undefined);
        let evals: TypeSignature[] = [];
        if(Array.isArray(stmt.exp)) {
            for(let i = 0; i < stmt.exp.length; ++i) {
                const cenv = env.addLocalVarSet(stmt.decls.filter((dd, ii) => dd.name !== "_" && ii !== i), stmt.isConst);

                //note this is Expression -- RHS expressions are not allowed in multi-expression initialization -- maybe a better error message here
                const etype = this.checkExpression(cenv, stmt.exp[i], i < iopts.length && iopts[i] !== undefined ? new SimpleTypeInferContext(iopts[i] as TypeSignature) : undefined); 
                evals.push(etype);
            }

            this.checkError(stmt.sinfo, iopts.length !== evals.length, "Mismatch in number of variables and expressions in multi-variable initialization");
            for(let i = evals.length; i < iopts.length; ++i) {
                evals.push(new ErrorTypeSignature(stmt.sinfo, undefined)); //try to recover a bit
            }

            for(let i = 0; i < stmt.decls.length; ++i) {
                const decl = stmt.decls[i];
                const itype = iopts[i];
                const etype = evals[i];
    
                this.checkError(stmt.sinfo, decl.name === "_", "Cannot use _ for variable initialization with multiple explicit expressions!!!");
                this.checkError(stmt.sinfo, itype !== undefined && !(etype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(etype, itype, this.constraints), `Expression of type ${TypeChecker.safeTypePrint(etype)} cannot be assigned to variable of type ${TypeChecker.safeTypePrint(itype)}`);
                
                stmt.actualtypes.push(itype || etype);
                if(decl.name !== "_") {
                    env = env.addLocalVar(decl.name, itype || etype, stmt.isConst, true); //try to recover a bit
                }
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

            this.checkError(stmt.sinfo, iopts.length !== evals.length, "Mismatch in number of variables and expressions in multi-variable initialization");
            for(let i = evals.length; i < iopts.length; ++i) {
                evals.push(new ErrorTypeSignature(stmt.sinfo, undefined)); //try to recover a bit
            }

            for(let i = 0; i < stmt.decls.length; ++i) {
                const decl = stmt.decls[i];
                const itype = iopts[i];
                const etype = evals[i];
    
                this.checkError(stmt.sinfo, itype !== undefined && !(etype instanceof ErrorTypeSignature) && !this.relations.areSameTypes(etype, itype), `Expression of type ${TypeChecker.safeTypePrint(etype)} (from EList) cannot be assigned to variable of type ${TypeChecker.safeTypePrint(itype)}`);
                
                stmt.actualtypes.push(itype || etype);
                if(decl.name !== "_") {
                    env = env.addLocalVar(decl.name, itype || etype, stmt.isConst, true); //try to recover a bit
                }
            }
        }

        return env;
        */
        assert(false, "Not Implemented -- checkVariableMultiInitializationStatement");
    }

    private checkVariableAssignmentStatement(env: TypeEnvironment, stmt: VariableAssignmentStatement): TypeEnvironment {
        /*
        const vinfo = env.resolveLocalVarInfoFromSrcName(stmt.name);
        if(vinfo === undefined && stmt.name !== "_") {
            this.reportError(stmt.sinfo, `Variable ${stmt.name} is not declared`);
            return env;
        }

        let decltype: TypeSignature | undefined = undefined;
        if(vinfo !== undefined) {
            //TODO: I think we also need to check ref here (we shouldn't assign to those)

            this.checkError(stmt.sinfo, vinfo.isConst, `Variable ${stmt.name} is declared as const and cannot be assigned`);
            decltype = vinfo.decltype;
        }

        const rhs = this.checkExpressionRHS(env, stmt.exp, decltype !== undefined ? new SimpleTypeInferContext(decltype) : undefined);

        this.checkError(stmt.sinfo, decltype !== undefined && !(rhs instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(rhs, decltype, this.constraints), `Expression of type ${TypeChecker.safeTypePrint(rhs)} cannot be assigned to variable of type ${TypeChecker.safeTypePrint(decltype)}`);
        
        stmt.vtype = decltype || rhs;
        return stmt.name !== "_" ? env.assignLocalVariable(stmt.name) : env;
        */
        assert(false, "Not Implemented -- checkVariableAssignmentStatement");
    }

    private checkVariableMultiAssignmentStatement(env: TypeEnvironment, stmt: VariableMultiAssignmentStatement): TypeEnvironment {
        /*
        const opts = stmt.names.map((vname) => env.resolveLocalVarInfoFromSrcName(vname));
        let iopts: (TypeSignature | undefined)[] = [];
        for(let i = 0; i < opts.length; ++i) {
            if(opts[i] !== undefined) {
                //TODO: I think we also need to check ref here (we shouldn't assign to those)

                this.checkError(stmt.sinfo, (opts[i] as VarInfo).isConst, `Variable ${stmt.names[i]} is declared as const and cannot be assigned`);
                iopts.push((opts[i] as VarInfo).decltype);
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
            //This evaluation is fully parallel -- no updates happen before all expressions are evaluated!!!!
            for(let i = 0; i < stmt.exp.length; ++i) {
                //note this is Expression -- RHS expressions are not allowed in multi-expression initialization -- maybe a better error message here
                const etype = this.checkExpression(env, stmt.exp[i], i < iopts.length && iopts[i] !== undefined ? new SimpleTypeInferContext(iopts[i] as TypeSignature) : undefined); 
                evals.push(etype);
            }

            this.checkError(stmt.sinfo, opts.length !== evals.length, "Mismatch in number of variables and expressions in multi-variable initialization");
            for(let i = evals.length; i < opts.length; ++i) {
                evals.push(new ErrorTypeSignature(stmt.sinfo, undefined)); //try to recover a bit
            }

            for(let i = 0; i < stmt.names.length; ++i) {
                const name = stmt.names[i];
                const itype = i < iopts.length && iopts[i] !== undefined ? (iopts[i] as TypeSignature) : undefined;
                const etype = evals[i];
    

                this.checkError(stmt.sinfo, name === "_", "Cannot use _ for variable assignment with multiple explicit expressions!!!");
                this.checkError(stmt.sinfo, itype !== undefined && !(etype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(etype, itype, this.constraints), `Expression of type ${TypeChecker.safeTypePrint(etype)} cannot be assigned to variable of type ${TypeChecker.safeTypePrint(itype)}`);
                
                stmt.vtypes.push(itype || etype);
                if(name !== "_") {
                    env = env.assignLocalVariable(name); //recover a bit
                }
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

            this.checkError(stmt.sinfo, opts.length !== evals.length, "Mismatch in number of variables and expressions in multi-variable initialization");
            for(let i = evals.length; i < opts.length; ++i) {
                evals.push(new ErrorTypeSignature(stmt.sinfo, undefined)); //try to recover a bit
            }

            for(let i = 0; i < stmt.names.length; ++i) {
                const name = stmt.names[i];
                const itype = i < iopts.length && iopts[i] !== undefined ? (iopts[i] as TypeSignature) : undefined;
                const etype = evals[i];
    
                this.checkError(stmt.sinfo, itype !== undefined && !(etype instanceof ErrorTypeSignature) && !this.relations.areSameTypes(etype, itype), `Expression of type ${TypeChecker.safeTypePrint(etype)} (from EList) cannot be assigned to variable of type ${TypeChecker.safeTypePrint(itype)}`);
                
                stmt.vtypes.push(itype || etype);
                if(name !== "_") {
                    env = env.assignLocalVariable(name); //recover a bit
                }
            }
        }

        return env;
        */
        assert(false, "Not Implemented -- checkVariableMultiAssignmentStatement");
    }

    private checkReturnVoidStatement(env: TypeEnvironment, stmt: ReturnVoidStatement): TypeEnvironment {
        this.checkError(stmt.sinfo, !this.isVoidType(env.declReturnType), `Expected a void return`);

        return env.setReturnFlow();
    }

    private checkReturnSingleStatement(env: TypeEnvironment, stmt: ReturnSingleStatement): TypeEnvironment {
        const rtype = this.checkExpressionRHS(env, stmt.value, env.inferReturn);

        stmt.rtype = env.declReturnType;
        this.checkError(stmt.sinfo, !(rtype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(rtype, env.declReturnType, this.constraints), `Expected a return value of type ${env.declReturnType.emit()} but got ${rtype.emit()}`);
        
        return env.setReturnFlow();
    }

    private checkReturnMultiStatement(env: TypeEnvironment, stmt: ReturnMultiStatement): TypeEnvironment {
        /*
        if(this.checkError(stmt.sinfo, !(env.inferReturn instanceof EListStyleTypeInferContext), `Multiple return requires an Elist type but got ${env.declReturnType.emit()}`)) {
            return env.setReturnFlow();
        }

        const rtypes = TypeInferContext.asEListOptions(env.inferReturn) as (TypeSignature | undefined)[];
        this.checkError(stmt.sinfo, rtypes.length !== stmt.value.length, `Mismatch in number of return values and expected return types`);

        for(let i = 0; i < stmt.value.length; ++i) {
            const rtype = rtypes[i] !== undefined ? rtypes[i] : undefined;
            const infertype = rtype !== undefined ? this.relations.convertTypeSignatureToTypeInferCtx(rtype) : undefined;
            const etype = this.checkExpression(env, stmt.value[i], infertype);

            const rtname = rtype !== undefined ? rtype.emit() : "skip";
            this.checkError(stmt.sinfo, rtype !== undefined && !(etype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(etype, rtype, this.constraints), `Expected a return value of type ${rtname} but got ${etype.emit()}`);

            stmt.rtypes.push(rtype || etype);
        }

        stmt.elsig = new EListTypeSignature(stmt.sinfo, stmt.rtypes);
        return env.setReturnFlow();
        */
        assert(false, "Not Implemented -- checkReturnMultiStatement");
    }

    private checkIfStatement(env: TypeEnvironment, stmt: IfStatement): TypeEnvironment {
        /*
        let eetype = this.checkExpression(env, stmt.cond.exp, undefined);
        
        if(stmt.cond.itestopt === undefined) {
            if(eetype instanceof ErrorTypeSignature) {
                eetype = this.getWellKnownType("Bool");
            }

            this.checkError(stmt.cond.exp.sinfo, !this.relations.isBooleanType(eetype), "If test requires a Bool type");
            this.checkError(stmt.cond.exp.sinfo, stmt.binder !== undefined, "Binder is not valid here -- requires use of an ITest");

            const ttrue = this.checkBlockStatement(env, stmt.trueBlock);
            return TypeEnvironment.mergeEnvironmentsSimple(env, env, ttrue);
        }
        else {
            const splits = this.processITestAsConvert(stmt.sinfo, env, eetype, stmt.cond.itestopt);
            this.checkError(stmt.cond.exp.sinfo, splits.ttrue === undefined, "Test is never true -- true branch of if is unreachable");
            this.checkError(stmt.cond.exp.sinfo, splits.tfalse === undefined, "Test is never false -- false branch of if is unreachable");

            if(stmt.binder === undefined) {
                const ttrue = this.checkBlockStatement(env, stmt.trueBlock);
                return TypeEnvironment.mergeEnvironmentsSimple(env, env, ttrue);
            }
            else {
                stmt.trueBindType = splits.ttrue || eetype;

                const nenv = env.pushNewLocalBinderScope(stmt.binder.srcname, splits.ttrue || eetype);
                const ttrue = this.checkStatement(nenv, stmt.trueBlock).popLocalScope();

                const retypename = stmt.binder.srcname.slice(1);
                this.checkFlowRebinder(stmt.sinfo, stmt.binder, retypename, env);
                if(ttrue.normalflow && splits.tfalse !== undefined) {
                    return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, { ttype: eetype, specialaccess: undefined }, env, ttrue, nenv);
                }
                else if(ttrue.normalflow) {
                    return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, { ttype: splits.ttrue as TypeSignature, specialaccess: splits.tspecialfubx }, env, ttrue, nenv);
                }
                else if(splits.tfalse !== undefined) {
                    return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, { ttype: splits.tfalse as TypeSignature, specialaccess: splits.fspecialfubx }, env, ttrue, nenv);
                }
                else {
                    return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, { ttype: eetype, specialaccess: undefined }, env, ttrue, nenv);    
                }
            }
        }
        */
        assert(false, "Not Implemented -- checkIfStatement");
    }

    private checkIfElseStatement(env: TypeEnvironment, stmt: IfElseStatement): TypeEnvironment {
        /*
        let eetype = this.checkExpression(env, stmt.cond.exp, undefined);

        if(stmt.cond.itestopt === undefined) {
            if(eetype instanceof ErrorTypeSignature) {
                eetype = this.getWellKnownType("Bool");
            }

            this.checkError(stmt.cond.exp.sinfo, !this.relations.isBooleanType(eetype), "If test requires a Bool type");
            this.checkError(stmt.cond.exp.sinfo, stmt.binder !== undefined, "Binder is not valid here -- requires use of an ITest");

            const ttrue = this.checkBlockStatement(env, stmt.trueBlock);
            const tfalse = this.checkBlockStatement(env, stmt.falseBlock);
            return TypeEnvironment.mergeEnvironmentsSimple(env, ttrue, tfalse);
        }
        else {
            const splits = this.processITestAsConvert(stmt.sinfo, env, eetype, stmt.cond.itestopt);
            this.checkError(stmt.cond.exp.sinfo, splits.ttrue === undefined, "Test is never true -- true branch of if is unreachable");
            this.checkError(stmt.cond.exp.sinfo, splits.tfalse === undefined, "Test is never false -- false branch of if is unreachable");

            if(stmt.binder === undefined) {
                const ttrue = this.checkBlockStatement(env, stmt.trueBlock);
                const tfalse = this.checkBlockStatement(env, stmt.falseBlock);
                return TypeEnvironment.mergeEnvironmentsSimple(env, ttrue, tfalse);
            }
            else {
                stmt.trueBindType = splits.ttrue || eetype;
                stmt.falseBindType = splits.tfalse || eetype;

                const tenv = env.pushNewLocalBinderScope(stmt.binder.srcname, splits.ttrue || eetype);
                const ttrue = this.checkStatement(tenv, stmt.trueBlock).popLocalScope();

                const fenv = env.pushNewLocalBinderScope(stmt.binder.srcname, splits.tfalse || eetype);
                const tfalse = this.checkStatement(fenv, stmt.falseBlock).popLocalScope();

                const retypename = stmt.binder.srcname.slice(1);
                this.checkFlowRebinder(stmt.sinfo, stmt.binder, retypename, env);
                if(ttrue.normalflow && tfalse.normalflow) {
                    return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, { ttype: eetype, specialaccess: undefined }, ttrue, tfalse);
                }
                else if(ttrue.normalflow) {
                    return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, { ttype: splits.ttrue as TypeSignature, specialaccess: splits.tspecialfubx }, ttrue, tfalse);
                }
                else if(tfalse.normalflow) {
                    return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, { ttype: splits.tfalse as TypeSignature, specialaccess: splits.fspecialfubx }, ttrue, tfalse);
                }
                else {
                    return TypeEnvironment.mergeEnvironmentsOptBinderFlow(env, stmt.binder, { ttype: eetype, specialaccess: undefined }, ttrue, tfalse);
                }
            }
        }
        */
        assert(false, "Not Implemented -- checkIfElseStatement");
    }

    private checkIfElifElseStatement(env: TypeEnvironment, stmt: IfElifElseStatement): TypeEnvironment {
        /*
        let branchflows: TypeEnvironment[] = [];

        for(let i = 0; i < stmt.condflow.length; ++i) {
            let etype = this.checkExpression(env, stmt.condflow[i].cond, undefined);
            if(etype instanceof ErrorTypeSignature) {
                etype = this.getWellKnownType("Bool");
            }

            this.checkError(stmt.condflow[i].cond.sinfo, !this.relations.isBooleanType(etype), `Expected a boolean expression but got ${etype.emit()}`);
            
            const resenv = this.checkBlockStatement(env, stmt.condflow[i].block);
            branchflows.push(resenv);
        }

        const elseflow = this.checkBlockStatement(env, stmt.elseflow);

        return TypeEnvironment.mergeEnvironmentsSimple(env, ...branchflows, elseflow);
        */
        assert(false, "Not Implemented -- checkIfElifElseStatement");
    }

    private checkSwitchStatement(env: TypeEnvironment, stmt: SwitchStatement): TypeEnvironment {
        /*
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
                if(!this.relations.isKeyType(littype, this.constraints)) {
                    this.reportError(slitexp.sinfo, `Switch statement requires a unique key type but got ${littype.emit()}`);
                }
                else {
                    const cmpok = this.checkValueEq(stmt.sval, ctype, slitexp, littype);
                    this.checkError(slitexp.sinfo, cmpok[0] === "err", `Cannot compare arguments in switch statement ${littype.emit()}`);

                    if(cmpok[0] !== "err") {
                        stmt.optypes.push(this.resolveUnderlyingType(littype) as TypeSignature);
                    }
                }

                const cenv = this.checkBlockStatement(env, stmt.switchflow[i].value);
                results.push(cenv);
            }
        }
        stmt.mustExhaustive = exhaustive;

        //TODO: once we have exhaustive for enums (and bools) then we should do a type check for exhaustive too

        return TypeEnvironment.mergeEnvironmentsSimple(env, ...results);
        */
        assert(false, "Not Implemented -- checkSwitchStatement");
    }

    private checkMatchStatement(env: TypeEnvironment, stmt: MatchStatement): TypeEnvironment {
        /*
        const eetype = this.checkExpression(env, stmt.sval[0], undefined);
        if(eetype instanceof ErrorTypeSignature) {
            return env;
        }

        let ctype = this.relations.decomposeType(eetype) || [];
        if(ctype.length === 0) {
            this.reportError(stmt.sval[0].sinfo, `Match statement requires a decomposable type but got ${eetype.emit()}`);
            return env;
        }
        
        let exhaustive = false;
        let results: TypeEnvironment[] = [];

        this.checkError(stmt.sinfo, stmt.matchflow.length < 2, "Match statement must have 2 or more choices");

        for (let i = 0; i < stmt.matchflow.length && !exhaustive; ++i) {
            //it is a wildcard match
            if(stmt.matchflow[i].mtype === undefined) {
                this.checkError(stmt.matchflow[i].value.sinfo, i !== stmt.matchflow.length - 1, `wildcard should be last option in switch expression but there were ${stmt.matchflow.length - (i + 1)} more that are unreachable`);
                exhaustive = true;

                const lubattempt = this.relations.flowTypeLUB(stmt.matchflow[i].value.sinfo, eetype, ctype, this.constraints);
                const defaulttype = (lubattempt instanceof ErrorTypeSignature) ? eetype : lubattempt;
                stmt.implicitFinalType = defaulttype;

                let cenv = env;
                if(stmt.sval[1] !== undefined) {
                    cenv = env.pushNewLocalBinderScope(stmt.sval[1].srcname, defaulttype)
                }
                
                cenv = this.checkBlockStatement(cenv, stmt.matchflow[i].value);

                if(stmt.sval[1] !== undefined) {
                    cenv = cenv.popLocalScope();
                }
                results.push(cenv);
            }
            else {
                const mtype = stmt.matchflow[i].mtype as TypeSignature;
                this.checkTypeSignature(mtype);
                if(mtype instanceof ErrorTypeSignature) {
                    return env;
                }

                const splits = this.relations.refineMatchType(ctype, mtype, this.constraints);
                if(splits === undefined) {
                    this.reportError(stmt.matchflow[i].value.sinfo, `Match statement requires a type that is a subtype of the decomposed type but got ${mtype.emit()}`);
                    return env;
                }
                else {
                    this.checkError(stmt.matchflow[i].value.sinfo, splits.overlap.length === 0, "Test is never true -- true branch of match is unreachable");

                    exhaustive = splits.remain.length === 0;
                    this.checkError(stmt.matchflow[i].value.sinfo, exhaustive && i !== stmt.matchflow.length - 1, `Test is never false -- but there were ${stmt.matchflow.length - (i + 1)} more that are unreachable`);

                    let cenv = env;
                    if(stmt.sval[1] !== undefined) {
                        cenv = env.pushNewLocalBinderScope(stmt.sval[1].srcname, mtype);
                    }
                    cenv = this.checkBlockStatement(cenv, stmt.matchflow[i].value);

                    if(stmt.sval[1] !== undefined) {
                        cenv = cenv.popLocalScope();
                    }
                    ctype = splits.remain || ctype;
                    results.push(cenv);
                }
            }
        }
        
        stmt.mustExhaustive = exhaustive;
        return TypeEnvironment.mergeEnvironmentsSimple(env, ...results);

        */
        assert(false, "Not Implemented -- checkMatchStatement");
    }

    private checkAbortStatement(env: TypeEnvironment, stmt: AbortStatement): TypeEnvironment {
        return env.setDeadFlow();
    }

    private checkAssertStatement(env: TypeEnvironment, stmt: AssertStatement): TypeEnvironment {
        /*
        const etype = this.checkExpression(env, stmt.cond, undefined);
        if(etype instanceof ErrorTypeSignature) {
            return env;
        }

        this.checkError(stmt.sinfo, !this.relations.isBooleanType(etype), `Expected a boolean type for assert condition but got ${etype.emit()}`);
        return env;
        */
        assert(false, "Not Implemented -- checkAssertStatement");
    }

    private checkValidateStatement(env: TypeEnvironment, stmt: ValidateStatement): TypeEnvironment {
        /*
        const etype = this.checkExpression(env, stmt.cond, undefined);
        if(etype instanceof ErrorTypeSignature) {
            return env;
        }

        this.checkError(stmt.sinfo, !this.relations.isBooleanType(etype), `Expected a boolean type for validate condition but got ${etype.emit()}`);
        return env;
        */
        assert(false, "Not Implemented -- checkValidateStatement");
    }

    private checkDebugStatement(env: TypeEnvironment, stmt: DebugStatement): TypeEnvironment {
        this.checkExpression(env, stmt.value, undefined);

        return env;
    }

    private checkVoidRefCallStatement(env: TypeEnvironment, stmt: VoidRefCallStatement): TypeEnvironment {
        /*
        const etype = this.checkExpressionRHS(env, stmt.exp, undefined);
        this.checkError(stmt.sinfo, !(etype instanceof ErrorTypeSignature) && !(etype instanceof VoidTypeSignature), `Expected a void return but got ${etype.emit()}`);

        return env;
        */
        assert(false, "Not Implemented -- checkVoidRefCallStatement");
    }

    /*
    private static isTypeUpdatable(ttype: TypeSignature): [boolean, boolean] {
        if(!(ttype instanceof NominalTypeSignature)) {
            return [false, false];
        }

        const decl = ttype.decl;
        const okupdate = (decl instanceof EntityTypeDecl) || (decl instanceof DatatypeMemberEntityTypeDecl) || (decl instanceof ConceptTypeDecl) || (decl instanceof DatatypeTypeDecl);
        const isdirect = (decl instanceof EntityTypeDecl) || (decl instanceof DatatypeMemberEntityTypeDecl);

        return [okupdate, isdirect];
    }

    private getFieldType(rcvrtype: TypeSignature, fname: string): TypeSignature | undefined {
        const finfo = this.relations.resolveTypeField(rcvrtype, fname, this.constraints);
        if(finfo === undefined) {
            return undefined;
        }

        return finfo.member.declaredType.remapTemplateBindings(finfo.typeinfo.mapping);
    }
    */
    
    private checkUpdateStatement(env: TypeEnvironment, stmt: UpdateStatement): TypeEnvironment {
        /*
        const vtype = this.checkExpression(env, stmt.vexp, undefined);
        const vname = stmt.vexp.srcname;

        const [vinfo, isparam] = env.resolveLocalVarInfoFromSrcNameWithIsParam(vname);
        if(vinfo === undefined) {
            this.reportError(stmt.sinfo, `Variable ${vname} is not declared`);
            return env;
        }
        if((!isparam && vinfo.isConst) || (isparam && !vinfo.isRef)) {
            this.reportError(stmt.sinfo, `Variable ${vname} is cannot be updated (is local const or not a ref param)`);
            return env;
        }

        const [okupdate, isdirect] = TypeChecker.isTypeUpdatable(vtype);
        if(!okupdate) {
            this.reportError(stmt.sinfo, `Variable ${vname} is not an updatable type (entity/concept or datatype)`);
            return env;
        }

        const updates = stmt.updates.map((upd) => {
            const bname = "$" + upd[0];
            const ftype = this.getFieldType(vtype, upd[0]);

            if(ftype === undefined) {
                this.reportError(stmt.sinfo, `Field ${upd[0]} is not a member of type ${vtype.emit()}`);
                return {fieldname: upd[0], fieldtype: new ErrorTypeSignature(stmt.sinfo, undefined), etype: new ErrorTypeSignature(stmt.sinfo, undefined)};
            }

            const cenv = env.pushNewLocalBinderScope(bname, ftype);
            const etype = this.checkExpression(cenv, upd[1], new SimpleTypeInferContext(ftype));
            if(!(etype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(etype, ftype, this.constraints)) {
                this.reportError(stmt.sinfo, `Expression of type ${etype.emit()} cannot be assigned to field ${upd[0]} of type ${ftype.emit()}`);
            }

            return {fieldname: upd[0], fieldtype: ftype, etype: etype};
        });

        stmt.updatetype = vtype;
        stmt.updateinfo = updates;
        stmt.isdirect = isdirect;

        return env;
        */
        assert(false, "Not Implemented -- checkUpdateStatement");
    }

    private checkVarUpdateStatement(env: TypeEnvironment, stmt: VarUpdateStatement): TypeEnvironment {
        return this.checkUpdateStatement(env, stmt);
    }

    private checkThisUpdateStatement(env: TypeEnvironment, stmt: ThisUpdateStatement): TypeEnvironment {
        return this.checkUpdateStatement(env, stmt);
    }

    private checkSelfUpdateStatement(env: TypeEnvironment, stmt: SelfUpdateStatement): TypeEnvironment {
        assert(false, "Not implemented -- SelfUpdateStatement");
    }

    private checkTaskYieldStatement(env: TypeEnvironment, stmt: TaskYieldStatement): TypeEnvironment {
        assert(false, "Not implemented -- TaskYieldStatement");
    }

    private checkBlockStatement(env: TypeEnvironment, stmt: BlockStatement): TypeEnvironment {
        let cenv = env;

        if(stmt.isScoping) {
            cenv = cenv.pushNewLocalScope();
            for (let i = 0; i < stmt.statements.length; ++i) {
                cenv = this.checkStatement(cenv, stmt.statements[i]);
            }
            [cenv, ] = cenv.popLocalScope();
        }
        else {
            for (let i = 0; i < stmt.statements.length; ++i) {
                cenv = this.checkStatement(cenv, stmt.statements[i]);
            }
        }

        return cenv;
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
        if(!env.isnormalflow) {
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
            case StatementTag.ReturnVoidStatement: {
                return this.checkReturnVoidStatement(env, stmt as ReturnVoidStatement);
            }
            case StatementTag.ReturnSingleStatement: {
                return this.checkReturnSingleStatement(env, stmt as ReturnSingleStatement);
            }
            case StatementTag.ReturnMultiStatement: {
                return this.checkReturnMultiStatement(env, stmt as ReturnMultiStatement);
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
        if((body instanceof AbstractBodyImplementation) || (body instanceof PredicateUFBodyImplementation) || (body instanceof BuiltinBodyImplementation) || (body instanceof HoleBodyImplementation)) {
            return;
        }

        if(body instanceof ExpressionBodyImplementation) {
            const etype = this.checkExpression(env, body.exp, env.inferReturn);
            this.checkError(body.sinfo, !(etype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(etype, env.declReturnType, this.constraints), `Expression body does not match expected return type -- expected ${env.declReturnType.emit()} but got ${etype.emit()}`);
        }
        else {
            assert(body instanceof StandardBodyImplementation);
            
            for(let i = 0; i < body.statements.length; ++i) {
                env = this.checkStatement(env, body.statements[i]);
            }

            this.checkError(body.sinfo, !this.isVoidType(env.declReturnType) && env.isnormalflow, "Function does not have a return statement in all code paths");
        }
    }

    private checkRequires(env: TypeEnvironment, requires: PreConditionDecl[]) {
        /*
        for(let i = 0; i < requires.length; ++i) {
            const precond = requires[i];
            const etype = this.checkExpression(env, precond.exp, undefined);
            this.checkError(precond.sinfo, !this.relations.isBooleanType(etype), `Requires expression does not have a boolean type -- got ${etype.emit()}`);
        }
        */
        assert(false, "Not Implemented -- checkRequires");
    }

    private checkEnsures(env: TypeEnvironment, returntype: TypeSignature, refvars: string[], eventtype: TypeSignature | undefined, ensures: PostConditionDecl[]) {
        /*
        let eev = env.pushNewLocalScope();
        
        eev = eev.addLocalVar(WELL_KNOWN_RETURN_VAR_NAME, returntype, true, true);
        if(eventtype !== undefined) {
            const eldecl = this.relations.assembly.getCoreNamespace().typedecls.find((td) => td.name === "EventList") as EventListTypeDecl;
            const eventlisttype = new NominalTypeSignature(SourceInfo.implicitSourceInfo(), undefined, eldecl, [eventtype]);
            eev = eev.addLocalVar(WELL_KNOWN_EVENTS_VAR_NAME, eventlisttype, true, true);
        }
        
        for(let i = 0; i < refvars.length; ++i) {
            const v = refvars[i];
            eev = eev.addLocalVar("$" + v, (env.resolveLocalVarInfoFromSrcName(v) as VarInfo).decltype, true, true);
        }

        for(let i = 0; i < ensures.length; ++i) {
            const postcond = ensures[i];
            const etype = this.checkExpression(eev, postcond.exp, undefined);
            this.checkError(postcond.sinfo, !this.relations.isBooleanType(etype), `Ensures expression does not have a boolean type -- got ${etype.emit()}`);
        }
        */
        assert(false, "Not Implemented -- checkEnsures");
    }

    private checkInvariants(bnames: {name: string, type: TypeSignature, hasdefault: boolean}[], invariants: InvariantDecl[]) {
        /*
        const env = TypeEnvironment.createInitialStdEnv(bnames.map((bn) => new VarInfo("$" + bn.name, bn.type, [], true, true, false)), this.getWellKnownType("Bool"), new SimpleTypeInferContext(this.getWellKnownType("Bool")));

        for(let i = 0; i < invariants.length; ++i) {
            const inv = invariants[i];
            const etype = this.checkExpression(env, inv.exp.exp, undefined);
            this.checkError(invariants[i].sinfo, !this.relations.isBooleanType(etype), `Invariant expression does not have a boolean type -- got ${etype.emit()}`);
        }
        */
        assert(false, "Not Implemented -- checkInvariants");
    }

    private checkValidates(bnames: {name: string, type: TypeSignature, hasdefault: boolean}[], validates: ValidateDecl[]) {
        /*
        const env = TypeEnvironment.createInitialStdEnv(bnames.map((bn) => new VarInfo("$" + bn.name, bn.type, [], true, true, false)), this.getWellKnownType("Bool"), new SimpleTypeInferContext(this.getWellKnownType("Bool")));

        for(let i = 0; i < validates.length; ++i) {
            const validate = validates[i];
            const etype = this.checkExpression(env, validate.exp.exp, undefined);
            this.checkError(validates[i].sinfo, !this.relations.isBooleanType(etype), `Validate expression does not have a boolean type -- got ${etype.emit()}`);
        }
        */
        assert(false, "Not Implemented -- checkValidates");
    }

    private checkExplicitInvokeDeclTermInfoClause(sinfo: SourceInfo, trclause: InvokeTemplateTypeRestrictionClause) {
        const tok = this.checkTypeSignature(trclause.t);
        const subtok = trclause.subtype === undefined || this.checkTypeSignature(trclause.subtype);
        
        if(!tok || !subtok) {
            return;
        }

        const tinscope = this.constraints.resolveConstraint(trclause.t.name);
        if(tinscope === undefined) {
            this.checkError(sinfo, true, `Template argument ${trclause.t.name} is not in scope -- so can't refine it`);
            return;
        }

        this.checkError(sinfo, trclause.subtype !== undefined && !this.relations.isSubtypeOf(trclause.t, trclause.subtype, this.constraints), `Template argument ${trclause.t.name} is not a subtype of restriction`);
    }

    private checkExplicitInvokeDeclTermInfo(idecl: ExplicitInvokeDecl) {
        this.checkTemplateTypesOnInvoke(idecl.sinfo, idecl.terms);

        if(idecl.termRestriction !== undefined) {
            for(let i = 0; i < idecl.termRestriction.clauses.length; ++i) {
                this.checkExplicitInvokeDeclTermInfoClause(idecl.sinfo, idecl.termRestriction.clauses[i]);
            }
        }
    }

    private checkExplicitInvokeDeclSignature(idecl: ExplicitInvokeDecl, specialvinfo: VarInfo[]) {
        let argnames = new Set<string>();
        const fullvinfo = [...specialvinfo, ...idecl.params.map((p) => new VarInfo("$" + p.name, p.type, [], true, true, p.isRefParam))];
        for(let i = 0; i < idecl.params.length; ++i) {
            const p = idecl.params[i];
            this.checkError(idecl.sinfo, argnames.has(p.name), `Duplicate parameter name ${p.name}`);
            argnames.add(p.name);

            const tok = this.checkTypeSignature(p.type);
            if(tok && p.optDefaultValue !== undefined) {
                const env = TypeEnvironment.createInitialStdEnv(fullvinfo, idecl.resultType, new SimpleTypeInferContext(idecl.resultType));
                const etype = this.checkExpression(env, p.optDefaultValue.exp, p.type);

                this.checkError(idecl.sinfo, !(etype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(etype, p.type, this.constraints), `Default value does not match declared type -- expected ${p.type.emit()} but got ${etype.emit()}`);
            }

            this.checkError(p.type.sinfo, p.isRefParam && !TypeChecker.isTypeUpdatable(p.type)[0], `Ref parameter must be of an updatable type`);
        }

        this.checkTypeSignature(idecl.resultType);
    }

    private checkExplicitInvokeDeclMetaData(idecl: ExplicitInvokeDecl, specialvinfo: VarInfo[], specialrefvars: string[], eventtype: TypeSignature | undefined) {
        const fullvinfo = [...specialvinfo, ...idecl.params.map((p) => new VarInfo(p.name, p.type, [], true, true, p.isRefParam))];
        const fullrefvars = [...specialrefvars, ...idecl.params.filter((p) => p.isRefParam).map((p) => p.name)];

        const ienv = TypeEnvironment.createInitialStdEnv(fullvinfo, this.getWellKnownType("Bool"), new SimpleTypeInferContext(this.getWellKnownType("Bool")));
        this.checkRequires(ienv, idecl.preconditions);
        this.checkEnsures(ienv, idecl.resultType, fullrefvars, eventtype, idecl.postconditions);
    }

    private checkNamespaceFunctionDecls(fdecls: NamespaceFunctionDecl[]) {
        for(let i = 0; i < fdecls.length; ++i) {
            const fdecl = fdecls[i];
    
            this.file = fdecl.file;
            this.checkExplicitInvokeDeclTermInfo(fdecl);

            if(fdecl.terms.length !== 0) {
                this.constraints.pushConstraintScope(fdecl.terms, undefined);
            }

            this.checkExplicitInvokeDeclSignature(fdecl, []);
            this.checkExplicitInvokeDeclMetaData(fdecl, [], [], undefined);

            const infertype = this.relations.convertTypeSignatureToTypeInferCtx(fdecl.resultType);
            const env = TypeEnvironment.createInitialStdEnv(fdecl.params.map((p) => new VarInfo(p.name, p.type, [], true, true, p.isRefParam)), fdecl.resultType, infertype);
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

            if(fdecl.terms.length !== 0 || fdecl.termRestriction !== undefined) {
                this.constraints.pushConstraintScope(fdecl.terms, fdecl.termRestriction);
            }

            this.checkExplicitInvokeDeclSignature(fdecl, []);
            this.checkExplicitInvokeDeclMetaData(fdecl, [], [], undefined);

            const infertype = this.relations.convertTypeSignatureToTypeInferCtx(fdecl.resultType);
            const env = TypeEnvironment.createInitialStdEnv(fdecl.params.map((p) => new VarInfo(p.name, p.type, [], true, true, p.isRefParam)), fdecl.resultType, infertype);
            this.checkBodyImplementation(env, fdecl.body);

            if(fdecl.terms.length !== 0) {
                this.constraints.popConstraintScope();
            }
        }
    }

    private checkMethodDecls(tdecl: AbstractNominalTypeDecl, rcvr: TypeSignature, mdecls: MethodDecl[]) {
        for(let i = 0; i < mdecls.length; ++i) {   
            const mdecl = mdecls[i];
    
            this.checkExplicitInvokeDeclTermInfo(mdecl);

            if(mdecl.terms.length !== 0 || mdecl.termRestriction !== undefined) {
                this.constraints.pushConstraintScope(mdecl.terms, mdecl.termRestriction);
            }

            const thisvinfo = new VarInfo("this", rcvr, [], true, true, mdecl.isThisRef);

            this.checkExplicitInvokeDeclSignature(mdecl, [thisvinfo]);
            this.checkExplicitInvokeDeclMetaData(mdecl, [thisvinfo], mdecl.isThisRef ? ["this"] : [], undefined);

            const infertype = this.relations.convertTypeSignatureToTypeInferCtx(mdecl.resultType);
            const env = TypeEnvironment.createInitialStdEnv([thisvinfo, ...mdecl.params.map((p) => new VarInfo(p.name, p.type, [], true, true, p.isRefParam))], mdecl.resultType, infertype);
            this.checkBodyImplementation(env, mdecl.body);

            if(mdecl.terms.length !== 0) {
                this.constraints.popConstraintScope();
            }
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
                const infertype = this.relations.convertTypeSignatureToTypeInferCtx(m.declaredType);
                const env = TypeEnvironment.createInitialStdEnv([], m.declaredType, infertype);

                const decltype = this.checkExpression(env, m.value.exp, new SimpleTypeInferContext(m.declaredType));
                this.checkError(m.sinfo, !this.relations.isSubtypeOf(decltype, m.declaredType, this.constraints), `Const initializer does not match declared type -- expected ${m.declaredType.emit()} but got ${decltype.emit()}`);
            }
        }
    }

    private checkMemberFieldDecls(bnames: {name: string, type: TypeSignature, hasdefault: boolean}[], fdecls: MemberFieldDecl[]) {
        for(let i = 0; i < fdecls.length; ++i) {
            const f = fdecls[i];
            
            if(this.checkTypeSignature(f.declaredType)) {
                if(f.defaultValue !== undefined) {
                    const infertype = this.relations.convertTypeSignatureToTypeInferCtx(f.declaredType);
                    const env = TypeEnvironment.createInitialStdEnv(bnames.map((bn) => new VarInfo("$" + bn.name, bn.type, [], true, true, false)), f.declaredType, infertype);

                    const decltype = this.checkExpression(env, f.defaultValue.exp, new SimpleTypeInferContext(f.declaredType));
                    this.checkError(f.sinfo, !this.relations.isSubtypeOf(decltype, f.declaredType, this.constraints), `Field initializer does not match declared type -- expected ${f.declaredType.emit()} but got ${decltype.emit()}`);
                }
            }
        }
    }

    private checkProvides(provides: TypeSignature[]) {
        for(let i = 0; i < provides.length; ++i) {
            const p = provides[i];
            this.checkTypeSignature(p);

            if(!this.relations.isValidProvidesType(p)) {
                this.reportError(p.sinfo, `Invalid provides type -- ${p.emit()}`);
            }
        }
    }

    private checkAbstractNominalTypeDeclVCallAndInheritance(tdecl: AbstractNominalTypeDecl, provides: TypeSignature[], isentity: boolean) {
        if(isentity) {
            const thisdynamic = tdecl.methods.some((mm) => mm.hasAttribute("override"));
            const pdynamic = provides.some((pp) => (pp as NominalTypeSignature).decl.hasAttribute("abstract") || (pp as NominalTypeSignature).decl.hasAttribute("virtual"));

            tdecl.hasDynamicInvokes = thisdynamic || pdynamic;
        }

        ////
        //TODO: Check that there are no name collisions on inhertied members and members in this
        //TODO: Check that all of the vcall resolves are unique .... and all of the vcall decls are implemented (depending on isentity)
        ////
    }

    private checkAbstractNominalTypeDeclHelper(bnames: {name: string, type: TypeSignature, hasdefault: boolean, containingtype: NominalTypeSignature}[], rcvr: TypeSignature, tdecl: AbstractNominalTypeDecl, optfdecls: MemberFieldDecl[] | undefined, isentity: boolean) {
        this.file = tdecl.file;
        this.checkTemplateTypesOnType(tdecl.sinfo, tdecl.terms);

        if(tdecl.terms.length !== 0) {
            this.constraints.pushConstraintScope(tdecl.terms, undefined);
        }

        this.checkProvides(tdecl.provides);
        tdecl.saturatedProvides = this.relations.resolveTransitiveProvidesDecls(rcvr, this.constraints).map((tli) => tli.tsig.remapTemplateBindings(tli.mapping));
        tdecl.saturatedBFieldInfo = bnames;

        //make sure all of the invariants on this typecheck
        this.checkInvariants(bnames, tdecl.invariants);
        this.checkValidates(bnames, tdecl.validates);
        
        const {invariants, validators} = this.relations.resolveAllInheritedValidatorDecls(rcvr, this.constraints);
        tdecl.allInvariants = invariants.map((inv) => {
            return { containingtype: inv.typeinfo.tsig.remapTemplateBindings(inv.typeinfo.mapping) as NominalTypeSignature, ii: inv.member.ii, file: inv.member.file, sinfo: inv.member.sinfo, tag: inv.member.diagnosticTag };
        });
        tdecl.allValidates = validators.map((inv) => {
            return { containingtype: inv.typeinfo.tsig.remapTemplateBindings(inv.typeinfo.mapping) as NominalTypeSignature, ii: inv.member.ii, file: inv.member.file, sinfo: inv.member.sinfo, tag: inv.member.diagnosticTag };
        });

        this.checkConstMemberDecls(tdecl, tdecl.consts);
        this.checkTypeFunctionDecls(tdecl, tdecl.functions);
        this.checkMethodDecls(tdecl, rcvr, tdecl.methods);

        if(optfdecls !== undefined) {
            this.checkMemberFieldDecls(bnames, optfdecls);
        }

        this.checkAbstractNominalTypeDeclVCallAndInheritance(tdecl, tdecl.saturatedProvides, isentity);

        if(tdecl.terms.length !== 0) {
            this.constraints.popConstraintScope();
        }
        this.file = CLEAR_FILENAME;
    }

    private checkEnumTypeDecl(ns: NamespaceDeclaration, tdecl: EnumTypeDecl) {
        this.file = tdecl.file;
        this.checkError(tdecl.sinfo, tdecl.terms.length !== 0, "Enums cannot have template terms");
        
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);

        this.checkProvides(tdecl.provides);
        this.checkError(tdecl.sinfo, tdecl.provides.length !== 0, "Enums cannot have provides types");
        
        this.checkError(tdecl.sinfo, tdecl.invariants.length !== 0 || tdecl.validates.length !== 0, "Enums cannot have invariants");

        this.checkError(tdecl.sinfo, tdecl.consts.length !== 0, "Enums cannot have consts");
        this.checkError(tdecl.sinfo, tdecl.functions.length !== 0, "Enums cannot have functions");

        this.checkMethodDecls(tdecl, rcvr, tdecl.methods);

        this.checkAbstractNominalTypeDeclVCallAndInheritance(tdecl, tdecl.saturatedProvides, true);

        let opts = new Set<string>();
        for(let i = 0; i < tdecl.members.length; ++i) {
            this.checkError(tdecl.sinfo, opts.has(tdecl.members[i]), `Duplicate enum option ${tdecl.members[i]}`);
            opts.add(tdecl.members[i]);
        }
        this.file = CLEAR_FILENAME;
    }

    private checkTypedeclTypeDecl(ns: NamespaceDeclaration, tdecl: TypedeclTypeDecl) {
        this.file = tdecl.file;

        const okvalue = this.checkTypeSignature(tdecl.valuetype);
        if(!okvalue) {
            return;
        }

        const isvalueok = (tdecl.valuetype instanceof NominalTypeSignature) && (tdecl.valuetype as NominalTypeSignature).decl.attributes.some((attr) => attr.name === "__typedeclable");
        if(!isvalueok) {
            this.reportError(tdecl.sinfo, `In type declaration value type must be simple primitive -- Bool, Int, etc.`);
            return;
        }

        if(tdecl.optofexp !== undefined) {
            const checkerexp = tdecl.optofexp !== undefined ? this.relations.assembly.resolveValidatorLiteral(tdecl.optofexp.exp) : undefined;
            this.checkError(tdecl.sinfo, checkerexp === undefined, `of expression must be regex or glob`);

            const typevaluename = (tdecl.valuetype as NominalTypeSignature).decl.name;
            if(checkerexp !== undefined) {
                if(typevaluename === "String") {
                    this.checkError(tdecl.sinfo, checkerexp.tag !== ExpressionTag.LiteralUnicodeRegexExpression, `of expression must be unicode regex`);
                    
                    const uretype = this.getWellKnownType("Regex") as NominalTypeSignature;
                    this.checkExpression(TypeEnvironment.createInitialStdEnv([], uretype, new SimpleTypeInferContext(uretype)), checkerexp, undefined);
                    this.checkExpression(TypeEnvironment.createInitialStdEnv([], uretype, new SimpleTypeInferContext(uretype)), tdecl.optofexp.exp, undefined);
                }
                else if(typevaluename === "CString") {
                    this.checkError(tdecl.sinfo, checkerexp.tag !== ExpressionTag.LiteralCRegexExpression, `of expression must be char regex`);

                    const cretype = this.getWellKnownType("CRegex") as NominalTypeSignature;
                    this.checkExpression(TypeEnvironment.createInitialStdEnv([], cretype, new SimpleTypeInferContext(cretype)), checkerexp, undefined);
                    this.checkExpression(TypeEnvironment.createInitialStdEnv([], cretype, new SimpleTypeInferContext(cretype)), tdecl.optofexp.exp, undefined);
                }
                else if(typevaluename === "Path") {
                    this.checkError(tdecl.sinfo, checkerexp.tag !== ExpressionTag.LiteralGlobExpression, `of expression must be path glob`);

                    const pgretype = this.getWellKnownType("PathGlob") as NominalTypeSignature;
                    this.checkExpression(TypeEnvironment.createInitialStdEnv([], pgretype, new SimpleTypeInferContext(pgretype)), checkerexp, undefined);
                    this.checkExpression(TypeEnvironment.createInitialStdEnv([], pgretype, new SimpleTypeInferContext(pgretype)), tdecl.optofexp.exp, undefined);
                }
                else {
                    this.reportError(tdecl.sinfo, `can only use "of" pattern on String/SCtring/Path types`);
                }
            }
        }

        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);

        this.checkProvides(tdecl.provides);
        tdecl.saturatedProvides = this.relations.resolveTransitiveProvidesDecls(rcvr, this.constraints).map((tli) => tli.tsig.remapTemplateBindings(tli.mapping));

        //Make sure that any provides types are not adding on fields!
        const providesdecls = this.relations.resolveTransitiveProvidesDecls(rcvr, this.constraints);
        for(let i = 0; i < providesdecls.length; ++i) {
            const pdecl = providesdecls[i];
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).fields.length !== 0, `Provides type cannot have member fields -- ${pdecl.tsig.decl.name}`);
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).invariants.length !== 0 || (pdecl.tsig.decl as ConceptTypeDecl).validates.length !== 0, `Provides type cannot have invariants -- ${pdecl.tsig.decl.name}`);
        }

        if(this.checkTypeSignature(tdecl.valuetype)) {
            //make sure the base type is typedeclable
            this.checkError(tdecl.sinfo, !this.relations.isTypedeclableType(tdecl.valuetype), `Base type is not typedeclable -- ${tdecl.valuetype.emit()}`);

            //make sure all of the invariants on this typecheck
            this.checkInvariants([{name: "value", type: tdecl.valuetype, hasdefault: false}], tdecl.invariants);
            this.checkValidates([{name: "value", type: tdecl.valuetype, hasdefault: false}], tdecl.validates);
        }
        
        const {invariants, validators} = this.relations.resolveAllTypeDeclaredValidatorDecls(rcvr, this.constraints);
        tdecl.allInvariants = invariants.map((inv) => {
            return { containingtype: inv.typeinfo.tsig.remapTemplateBindings(inv.typeinfo.mapping) as NominalTypeSignature, ii: inv.member.ii, file: inv.member.file, sinfo: inv.member.sinfo, tag: inv.member.diagnosticTag };
        });
        tdecl.allValidates = validators.map((inv) => {
            return { containingtype: inv.typeinfo.tsig.remapTemplateBindings(inv.typeinfo.mapping) as NominalTypeSignature, ii: inv.member.ii, file: inv.member.file, sinfo: inv.member.sinfo, tag: inv.member.diagnosticTag };
        });

        this.checkConstMemberDecls(tdecl, tdecl.consts);
        this.checkTypeFunctionDecls(tdecl, tdecl.functions);

        this.checkMethodDecls(tdecl, rcvr, tdecl.methods);
        this.checkAbstractNominalTypeDeclVCallAndInheritance(tdecl, [], true);

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

    private checkCRopeIteratorTypeDecl(ns: NamespaceDeclaration, tdecl: CRopeIteratorTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkOkTypeDecl(ns: NamespaceDeclaration, tdecl: OkTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkFailTypeDecl(ns: NamespaceDeclaration, tdecl: FailTypeDecl) {
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

    private checkMapEntryTypeDecl(ns: NamespaceDeclaration, tdecl: MapEntryTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkListTypeDecl(ns: NamespaceDeclaration, tdecl: ListTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkCRopeTypeDecl(ns: NamespaceDeclaration, tdecl: CRopeTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkUnicodeRopeTypeDecl(ns: NamespaceDeclaration, tdecl: UnicodeRopeTypeDecl) {
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
        const bnames = this.relations.generateAllFieldBNamesInfo(rcvr, tdecl.fields, this.constraints);

        this.checkAbstractNominalTypeDeclHelper(bnames, rcvr, tdecl, tdecl.fields, true);
        this.file = CLEAR_FILENAME;
    }

    private checkOptionTypeDecl(ns: NamespaceDeclaration, tdecl: OptionTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, false);
    }

    private checkResultTypeDecl(ns: NamespaceDeclaration, tdecl: ResultTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, false);

        this.constraints.pushConstraintScope(tdecl.terms, undefined);
        for(let i = 0; i < tdecl.nestedEntityDecls.length; ++i) {
            const ned = tdecl.nestedEntityDecls[i];
            if(ned instanceof OkTypeDecl) {
                this.checkOkTypeDecl(ns, ned);
            }
            else {
                this.checkFailTypeDecl(ns, ned as FailTypeDecl);
            }
        }
        this.constraints.popConstraintScope();
    }

    private checkAPIResultTypeDecl(ns: NamespaceDeclaration, tdecl: APIResultTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, false);

        this.constraints.pushConstraintScope(tdecl.terms, undefined);
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

    private checkConceptTypeDecl(ns: NamespaceDeclaration, tdecl: ConceptTypeDecl) {
        this.file = tdecl.file;
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = this.relations.generateAllFieldBNamesInfo(rcvr, tdecl.fields, this.constraints);

        this.checkAbstractNominalTypeDeclHelper(bnames, rcvr, tdecl, tdecl.fields, false);
        this.file = CLEAR_FILENAME;
    }

    private checkDatatypeMemberEntityTypeDecl(ns: NamespaceDeclaration, parent: DatatypeTypeDecl, tdecl: DatatypeMemberEntityTypeDecl) {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = this.relations.generateAllFieldBNamesInfo(rcvr, tdecl.fields, this.constraints);

        this.checkAbstractNominalTypeDeclHelper(bnames, rcvr, tdecl, tdecl.fields, true);
    }

    private checkDatatypeTypeDecl(ns: NamespaceDeclaration, tdecl: DatatypeTypeDecl) {
        this.file = tdecl.file;
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = this.relations.generateAllFieldBNamesInfo(rcvr, tdecl.fields, this.constraints);

        this.checkAbstractNominalTypeDeclHelper(bnames, rcvr, tdecl, tdecl.fields, true);

        for(let i = 0; i < tdecl.associatedMemberEntityDecls.length; ++i) {
            this.checkDatatypeMemberEntityTypeDecl(ns, tdecl, tdecl.associatedMemberEntityDecls[i]);
        }
        this.file = CLEAR_FILENAME;
    }

    private checkEventInfo(einfo: TypeSignature) {
        const oksig = this.checkTypeSignature(einfo);
        if(oksig) {
            this.checkError(einfo.sinfo, !this.relations.isEventDataType(einfo), `Event type is not a valid event type -- ${einfo.emit()}`);
        }
    }

    private checkStatusInfo(sinfo: TypeSignature[]) {
        for(let i = 0; i < sinfo.length; ++i) {
            const oksig = this.checkTypeSignature(sinfo[i]);
            if(oksig) {
                this.checkError(sinfo[i].sinfo, !this.relations.isStatusDataType(sinfo[i]), `Event type is not a valid status type -- ${sinfo[i].emit()}`);
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
            this.constraints.pushConstraintScope(tdecl.terms, undefined);
        }

        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = tdecl.fields.map((f) => { return {name: f.name, type: f.declaredType, hasdefault: f.defaultValue !== undefined, containingtype: rcvr}; });
        tdecl.saturatedBFieldInfo = bnames;

        //make sure all of the invariants on this typecheck
        this.checkInvariants(bnames, tdecl.invariants);
        this.checkValidates(bnames, tdecl.validates);
        
        const {invariants, validators} = this.relations.resolveAllInheritedValidatorDecls(rcvr, this.constraints);
        tdecl.allInvariants = invariants.map((inv) => {
            return { containingtype: inv.typeinfo.tsig.remapTemplateBindings(inv.typeinfo.mapping) as NominalTypeSignature, ii: inv.member.ii, file: inv.member.file, sinfo: inv.member.sinfo, tag: inv.member.diagnosticTag };
        });
        tdecl.allValidates = validators.map((inv) => {
            return { containingtype: inv.typeinfo.tsig.remapTemplateBindings(inv.typeinfo.mapping) as NominalTypeSignature, ii: inv.member.ii, file: inv.member.file, sinfo: inv.member.sinfo, tag: inv.member.diagnosticTag };
        });

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
                const infertype = this.relations.convertTypeSignatureToTypeInferCtx(m.declaredType);
                const decltype = this.checkExpression(TypeEnvironment.createInitialStdEnv([], m.declaredType, infertype), m.value.exp, m.declaredType);

                this.checkError(m.sinfo, !this.relations.isSubtypeOf(decltype, m.declaredType, this.constraints), `Const initializer does not match declared type -- expected ${m.declaredType.emit()} but got ${decltype.emit()}`);
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
                this.checkTypedeclTypeDecl(ns, tt);
            }
            else if(tt instanceof PrimitiveEntityTypeDecl) {
                this.checkPrimitiveEntityTypeDecl(ns, tt);
            }
            else if(tt instanceof CRopeIteratorTypeDecl) {
                this.checkCRopeIteratorTypeDecl(ns, tt);
            }
            else if(tt instanceof OkTypeDecl) {
                this.checkOkTypeDecl(ns, tt);
            }
            else if(tt instanceof FailTypeDecl) {
                this.checkFailTypeDecl(ns, tt);
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
            else if(tt instanceof MapEntryTypeDecl) {
                this.checkMapEntryTypeDecl(ns, tt);
            }
            else if(tt instanceof ListTypeDecl) {
                this.checkListTypeDecl(ns, tt);
            }
            else if(tt instanceof CRopeTypeDecl) {
                this.checkCRopeTypeDecl(ns, tt);
            }
           else if(tt instanceof UnicodeRopeTypeDecl) {
                this.checkUnicodeRopeTypeDecl(ns, tt);
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
            else if(tt instanceof DatatypeMemberEntityTypeDecl) {
                this.checkDatatypeMemberEntityTypeDecl(ns, tt.parentTypeDecl, tt);
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

    private processConstsAndValidatorREs(assembly: Assembly) {
        const asmreinfo = assembly.toplevelNamespaces.flatMap((ns) => assembly.loadConstantsAndValidatorREs(ns));

        //Now process the regexs
        const err = loadConstAndValidateRESystem(asmreinfo);
        if(err !== null) {
            for(let i = 0; i < err.length; ++i) {
                this.reportError(SourceInfo.implicitSourceInfo(), err[i]);
            }
        }
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

        TypeChecker.loadWellKnownType(assembly, "None", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Some", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Bool", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Int", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Nat", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "ChkInt", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "ChkNat", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Rational", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Float", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Decimal", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "DecimalDegree", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "LatLongCoordinate", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "Complex", wellknownTypes);

        TypeChecker.loadWellKnownType(assembly, "CChar", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "UnicodeChar", wellknownTypes);

        TypeChecker.loadWellKnownType(assembly, "String", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "CString", wellknownTypes);

        TypeChecker.loadWellKnownType(assembly, "Regex", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "CRegex", wellknownTypes);

        TypeChecker.loadWellKnownType(assembly, "UUIDv4", wellknownTypes);
        TypeChecker.loadWellKnownType(assembly, "UUIDv7", wellknownTypes);

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
