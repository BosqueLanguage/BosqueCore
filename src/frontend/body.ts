import assert from "node:assert";

import { FullyQualifiedNamespace, AutoTypeSignature, RecursiveAnnotation, TypeSignature, LambdaTypeSignature, NominalTypeSignature } from "./type.js";

import { BuildLevel, CodeFormatter, SourceInfo } from "./build_decls.js";
import { LambdaDecl, MemberFieldDecl, MethodDecl, NamespaceDeclaration } from "./assembly.js";

class BinderInfo {
    readonly srcname: string; //the name in the source code
    readonly implicitdef: boolean;

    constructor(srcname: string, implicitdef: boolean, refineonfollow: boolean) {
        this.srcname = srcname;
        this.implicitdef = implicitdef;
    }

    emitoptdef(): string {
        return !this.implicitdef ? `${this.srcname} = ` : "";
    }
}

abstract class ITest {
    readonly isnot: boolean;

    constructor(isnot: boolean) {
        this.isnot = isnot;
    }

    abstract emit(fmt: CodeFormatter): string;
}

class ITestType extends ITest {
    readonly ttype: TypeSignature;
    
    constructor(isnot: boolean, ttype: TypeSignature) {
        super(isnot);
        this.ttype = ttype;
    }

    emit(fmt: CodeFormatter): string {
        return `${this.isnot ? "!" : ""}<${this.ttype.emit()}>`;
    }
}

class ITestNone extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(fmt: CodeFormatter): string {
        return `${this.isnot ? "!" : ""}none`;
    }
}

class ITestSome extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(fmt: CodeFormatter): string {
        return `${this.isnot ? "!" : ""}some`;
    }
}

class ITestOk extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(fmt: CodeFormatter): string {
        return `${this.isnot ? "!" : ""}ok`;
    }
}

class ITestFail extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(fmt: CodeFormatter): string {
        return `${this.isnot ? "!" : ""}fail`;
    }
}

class ITestRejected extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(fmt: CodeFormatter): string {
        return `${this.isnot ? "!" : ""}rejected`;
    }
}

class ITestFailed extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(fmt: CodeFormatter): string {
        return `${this.isnot ? "!" : ""}failed`;
    }
}

class ITestError extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(fmt: CodeFormatter): string {
        return `${this.isnot ? "!" : ""}error`;
    }
}

class ITestSuccess extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(fmt: CodeFormatter): string {
        return `${this.isnot ? "!" : ""}success`;
    }
}

abstract class ITestGuard {
    readonly exp: Expression;
    
    constructor(exp: Expression) {
        this.exp = exp;
    }

    abstract emit(fmt: CodeFormatter): string;
}

class ITestBinderGuard extends ITestGuard {
    readonly itestopt: ITest | undefined;
    readonly bindinfo: BinderInfo | undefined;

    constructor(exp: Expression, itestopt: ITest | undefined, bindinfo: BinderInfo | undefined) {
        super(exp);
        this.itestopt = itestopt;
        this.bindinfo = bindinfo;
    }

    emit(fmt: CodeFormatter): string {
        const bexp = this.bindinfo !== undefined ? this.bindinfo.emitoptdef() : "";
        const itest = this.itestopt !== undefined ? `${this.itestopt.emit(fmt)}` : "";
        
        return `(${bexp}${this.exp.emit(true, fmt)})${itest}`;
    }
}

class ITestSimpleGuard extends ITestGuard {
    emit(fmt: CodeFormatter): string {
        return `${this.exp.emit(true, fmt)}`;
    }
}

class ITestGuardSet {
    readonly guards: ITestGuard[];

    constructor(guards: ITestGuard[]) {
        this.guards = guards;
    }

    emit(fmt: CodeFormatter): string {
        return this.guards.map((g) => g.emit(fmt)).join(" && ");
    }
}

abstract class ArgumentValue {
    readonly exp: Expression;

    constructor(exp: Expression) {
        this.exp = exp;
    }

    abstract emit(fmt: CodeFormatter): string;
}

class RefArgumentValue extends ArgumentValue {
    constructor(exp: AccessVariableExpression) {
        super(exp);
    }

    emit(fmt: CodeFormatter): string {
        return `ref ${this.exp.emit(true, fmt)}`;
    }
}

class OutArgumentValue extends ArgumentValue {
    constructor(exp: AccessVariableExpression) {
        super(exp);
    }

    emit(fmt: CodeFormatter): string {
        return `out ${this.exp.emit(true, fmt)}`;
    }
}

class OutCondArgumentValue extends ArgumentValue {
    constructor(exp: AccessVariableExpression) {
        super(exp);
    }

    emit(fmt: CodeFormatter): string {
        return `out? ${this.exp.emit(true, fmt)}`;
    }
}

class InOutArgumentValue extends ArgumentValue {
    constructor(exp: AccessVariableExpression) {
        super(exp);
    }
    emit(fmt: CodeFormatter): string {
        return `inout ${this.exp.emit(true, fmt)}`;
    }
}

class PositionalArgumentValue extends ArgumentValue {
    constructor(exp: Expression) {
        super(exp);
    }

    emit(fmt: CodeFormatter): string {
        return this.exp.emit(true, fmt);
    }
}

class NamedArgumentValue extends ArgumentValue {
    readonly name: string;

    constructor(name: string, exp: Expression) {
        super(exp);
        this.name = name;
    }

    emit(fmt: CodeFormatter): string {
        return `${this.name} = ${this.exp.emit(true, fmt)}`;
    }
}

class SpreadArgumentValue extends ArgumentValue {
    constructor(exp: Expression) {
        super(exp);
    }

    emit(fmt: CodeFormatter): string {
        return `...${this.exp.emit(true, fmt)}`;
    }
}

class ArgumentList {
    readonly args: ArgumentValue[];

    constructor(args: ArgumentValue[]) {
        this.args = args;
    }

    emit(fmt: CodeFormatter, lp: string, rp: string): string {
        return lp + this.args.map((arg) => arg.emit(fmt)).join(", ") + rp;
    }

    hasSpread(): boolean {
        return this.args.some((arg) => arg instanceof SpreadArgumentValue);
    }
}

enum ExpressionTag {
    Clear = "[CLEAR]",
    ErrorExpression = "ErrorExpression",

    LiteralNoneExpression = "LiteralNoneExpression",
    LiteralBoolExpression = "LiteralBoolExpression",
    LiteralNatExpression = "LiteralNatExpression",
    LiteralIntExpression = "LiteralIntExpression",
    LiteralBigNatExpression = "LiteralBigNatExpression",
    LiteralBigIntExpression = "LiteralBigIntExpression",
    LiteralRationalExpression = "LiteralRationalExpression",
    LiteralFloatExpression = "LiteralFloatExpression",
    LiteralDecimalExpression = "LiteralDecimalExpression",
    LiteralDecimalDegreeExpression = "LiteralDecimalDegreeExpression",
    LiteralLatLongCoordinateExpression = "LiteralLatLongCoordinateExpression",
    LiteralComplexNumberExpression = "LiteralComplexNumberExpression",
    LiteralByteBufferExpression = "LiteralByteBufferExpression",
    LiteralUUIDv4Expression = "LiteralUUIDv4Expression",
    LiteralUUIDv7Expression = "LiteralUUIDv7Expression",
    LiteralSHAContentHashExpression = "LiteralSHAContentHashExpression",
    LiteralTZDateTimeExpression = "LiteralTZDateTimeExpression",
    LiteralTAITimeExpression = "LiteralTAITimeExpression",
    LiteralPlainDateExpression = "LiteralPlainDateExpression",
    LiteralPlainTimeExpression = "LiteralPlainTimeExpression",
    LiteralLogicalTimeExpression = "LiteralLogicalTimeExpression",
    LiteralISOTimeStampExpression = "LiteralISOTimeStampExpression",
    LiteralDeltaDateTimeExpression = "LiteralDeltaDateTimeExpression",
    LiteralDeltaISOTimeStampExpression = "LiteralDeltaISOTimeStampExpression",
    LiteralDeltaSecondsExpression = "LiteralDeltaSecondsExpression",
    LiteralDeltaLogicalExpression = "LiteralDeltaLogicalExpression",

    LiteralUnicodeRegexExpression = "LiteralUnicodeRegexExpression",
    LiteralCRegexExpression = "LiteralCRegexExpression",

    LiteralCCharExpression = "LiteralCCharExpression",
    LiteralUnicodeCharExpression = "LiteralUnicodeCharExpression",

    LiteralStringExpression = "LiteralStringExpression",
    LiteralCStringExpression = "LiteralCStringExpression",
    
    LiteralPathExpression = "LiteralPathExpression",
    LiteralPathItemExpression = "LiteralPathItemExpression",
    LiteralGlobExpression = "LiteralGlobExpression",

    LiteralTypeDeclValueExpression = "LiteralTypeDeclValueExpression",

    HasEnvValueExpression = "HasEnvValueExpression",
    AccessEnvValueExpression = "AccessEnvValueExpression",
    TaskAccessInfoExpression = "TaskAccessInfoExpression",
    AccessNamespaceConstantExpression = "AccessNamespaceConstantExpression",
    AccessStaticFieldExpression = " AccessStaticFieldExpression",
    AccessEnumExpression = "AccessEnumExpression",
    AccessVariableExpression = "AccessVariableExpression",

    ConstructorPrimaryExpression = "ConstructorPrimaryExpression",
    ConstructorEListExpression = "ConstructorEListExpression",
    ConstructorLambdaExpression = "ConstructorLambdaExpression",

    LambdaInvokeExpression = "LambdaInvokeExpression",
    SpecialConstructorExpression = "SpecialConstructorExpression",
    SpecialConverterExpression = "SpecialConverterExpression",
    CallNamespaceFunctionExpression = "CallNamespaceFunctionExpression",
    CallTypeFunctionExpression = "CallTypeFunctionExpression",
    CallRefVariableExpression = "CallRefVariableExpression",
    CallRefThisExpression = "CallRefThisExpression",
    CallRefSelfExpression = "CallRefSelfExpression",
    CallTaskActionExpression = "CallTaskActionExpression",

    ParseAsTypeExpression = "ParseAsTypeExpression",
    SafeConvertExpression = "SafeConvertExpression",
    CreateDirectExpression = "CreateDirectExpression",

    PostfixOpExpression = "PostfixOpExpression",

    PrefixNotOpExpression = "PrefixNotOpExpression",
    PrefixNegateOrPlusOpExpression = "PrefixNegateOrPlusOpExpression",

    BinAddExpression = "BinAddExpression",
    BinSubExpression = "BinSubExpression",
    BinMultExpression = "BinMultExpression",
    BinDivExpression = "BinDivExpression",

    BinKeyEqExpression = "BinKeyEqExpression",
    BinKeyNeqExpression = "BinKeyNeqExpression",

    KeyCompareEqExpression = "KeyCompareEqExpression",
    KeyCompareLessExpression = "KeyCompareLessExpression",

    NumericEqExpression = "NumericEqExpression",
    NumericNeqExpression = "NumericNeqExpression",
    NumericLessExpression = "NumericLessExpression",
    NumericLessEqExpression = "NumericLessEqExpression",
    NumericGreaterExpression = "NumericGreaterExpression",
    NumericGreaterEqExpression = "NumericGreaterEqExpression",

    BinLogicAndExpression = "BinLogicAndExpression",
    BinLogicOrExpression = "BinLogicOrExpression",
    
    MapEntryConstructorExpression = "MapEntryConstructorExpression",

    IfExpression = "IfExpression",

    TaskRunExpression = "TaskRunExpression", //run single task
    TaskMultiExpression = "TaskMultiExpression", //run multiple explicitly identified tasks -- complete all
    TaskDashExpression = "TaskDashExpression", //run multiple explicitly identified tasks -- first completion wins
    TaskAllExpression = "TaskAllExpression", //run the same task on all args in a list -- complete all
    TaskRaceExpression = "TaskRaceExpression" //run the same task on all args in a list -- first completion wins
}

abstract class Expression {
    readonly tag: ExpressionTag;
    readonly sinfo: SourceInfo;

    private etype: TypeSignature | undefined = undefined;

    constructor(tag: ExpressionTag, sinfo: SourceInfo) {
        this.tag = tag;
        this.sinfo = sinfo;
    }

    getType(): TypeSignature {
        assert(this.etype !== undefined, "Type signature not set");
        return this.etype as TypeSignature;
    }

    setType(etype: TypeSignature): TypeSignature {
        this.etype = etype;
        return etype;
    }

    isLiteralExpression(): boolean {
        return false;
    }

    abstract emit(toplevel: boolean, fmt: CodeFormatter): string;
}

class ErrorExpression extends Expression {
    readonly staticPrefix: {ns: NamespaceDeclaration, typeopt: TypeSignature | undefined} | undefined;
    readonly dotaccess: {btype: TypeSignature | undefined, names: string[]} | undefined;

    constructor(sinfo: SourceInfo, staticPrefix: {ns: NamespaceDeclaration, typeopt: TypeSignature | undefined} | undefined, dotaccess: {btype: TypeSignature | undefined, names: string[]} | undefined) {
        super(ExpressionTag.ErrorExpression, sinfo);

        this.staticPrefix = staticPrefix;
        this.dotaccess = dotaccess;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return "[!ERROR_EXP!]";
    }
}

class LiteralNoneExpression extends Expression {
    constructor(tag: ExpressionTag, sinfo: SourceInfo) {
        super(tag, sinfo);
    }

    override isLiteralExpression(): boolean {
        return true;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return "none";
    }
}

class LiteralSimpleExpression extends Expression {
    readonly value: string;
    resolvedValue: any = undefined; //e.g. for string types after unescaping

    constructor(tag: ExpressionTag, sinfo: SourceInfo, value: string) {
        super(tag, sinfo);
        this.value = value;
    }

    override isLiteralExpression(): boolean {
        return true;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.value;
    }
}

class LiteralRegexExpression extends Expression {
    readonly value: string;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, value: string) {
        super(tag, sinfo);
        this.value = value;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.value;
    }
}

class LiteralTypeDeclValueExpression extends Expression {
    readonly value: Expression;
    readonly constype: TypeSignature;
    
    optResolvedString: string | undefined = undefined;

    constructor(sinfo: SourceInfo, value: Expression, constype: TypeSignature) {
        super(ExpressionTag.LiteralTypeDeclValueExpression, sinfo);
        this.value = value;
        this.constype = constype;
    }

    override isLiteralExpression(): boolean {
        return true;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.value.emit(toplevel, fmt)}<${this.constype.emit()}>`;
    }
}

class AccessEnvValueExpression extends Expression {
    readonly keyname: string;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, keyname: string) {
        super(tag, sinfo);
        this.keyname = keyname;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `env${this.tag === ExpressionTag.HasEnvValueExpression ? "?" : ""}[${this.keyname}]`;
    }
}

class TaskAccessInfoExpression extends Expression {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string) {
        super(ExpressionTag.TaskAccessInfoExpression, sinfo);
        this.name = name;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `Task::${this.name}()`;
    }
}

class AccessNamespaceConstantExpression extends Expression {
    readonly ns: FullyQualifiedNamespace;
    readonly isImplicitNS: boolean;
    readonly name: string;

    constructor(sinfo: SourceInfo, isImplicitNS: boolean, ns: FullyQualifiedNamespace, name: string) {
        super(ExpressionTag.AccessNamespaceConstantExpression, sinfo);
        this.ns = ns;
        this.isImplicitNS = isImplicitNS;
        this.name = name;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${!this.isImplicitNS ? (this.ns.emit() + "::") : ""}${this.name}`;
    }
}

class AccessStaticFieldExpression extends Expression {
    readonly stype: TypeSignature;
    readonly name: string;

    resolvedDeclType: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, stype: TypeSignature, name: string) {
        super(ExpressionTag.AccessStaticFieldExpression, sinfo);
        this.stype = stype;
        this.name = name;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.stype.emit()}::${this.name}`;
    }
}

class AccessEnumExpression extends Expression {
    readonly stype: NominalTypeSignature;
    readonly name: string;

    constructor(sinfo: SourceInfo, stype: NominalTypeSignature, name: string) {
        super(ExpressionTag.AccessEnumExpression, sinfo);
        this.stype = stype;
        this.name = name;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.stype.emit()}#${this.name}`;
    }
}

class AccessVariableExpression extends Expression {
    readonly srcname: string; //the name in the source code

    specialaccess: { ttype: TypeSignature, specialaccess: string | undefined }[] = []; //field name to access to a special re-typed variable (specifically extracting an option or result value)
    layouttype: TypeSignature | undefined = undefined; //if this was re-typed then this is the layout type -- while the type of the expression is the infered type
    isCaptured: boolean;

    constructor(sinfo: SourceInfo, srcname: string) {
        super(ExpressionTag.AccessVariableExpression, sinfo);
        this.srcname = srcname;
        this.isCaptured = false;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.srcname;
    }
}

abstract class ConstructorExpression extends Expression {
    readonly args: ArgumentList;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, args: ArgumentList) {
        super(tag, sinfo);
        this.args = args;
    }
}

class ConstructorPrimaryExpression extends ConstructorExpression {
    readonly ctype: NominalTypeSignature;

    elemtype: TypeSignature | undefined = undefined;
    shuffleinfo: [number, TypeSignature | undefined, string, TypeSignature][] = [];
    
    constructor(sinfo: SourceInfo, ctype: NominalTypeSignature, args: ArgumentList) {
        super(ExpressionTag.ConstructorPrimaryExpression, sinfo, args);
        this.ctype = ctype;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.ctype.emit()}${this.args.emit(fmt, "{", "}")}`;
    }
}

class ConstructorEListExpression extends ConstructorExpression {
    constructor(sinfo: SourceInfo, args: ArgumentList) {
        super(ExpressionTag.ConstructorEListExpression, sinfo, args);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.args.emit(fmt, "(|", "|)");
    }
}

class ConstructorLambdaExpression extends Expression {
    readonly invoke: LambdaDecl;

    constructor(sinfo: SourceInfo, invoke: LambdaDecl) {
        super(ExpressionTag.ConstructorLambdaExpression, sinfo);
        this.invoke = invoke;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.invoke.emit(fmt);
    }
}

class SpecialConstructorExpression extends Expression {
    readonly rop: "ok" | "fail" | "some";
    readonly arg: Expression;

    constype: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, rop: "ok" | "fail" | "some", arg: Expression) {
        super(ExpressionTag.SpecialConstructorExpression, sinfo);
        this.rop = rop;
        this.arg = arg;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.rop}(${this.arg.emit(toplevel, fmt)})`;
    }
}

class SpecialConverterExpression extends Expression {
    readonly rop: "option" | "result";
    readonly arg: Expression;

    constructor(sinfo: SourceInfo, rop: "option" | "result", arg: Expression) {
        super(ExpressionTag.SpecialConverterExpression, sinfo);
        this.rop = rop;
        this.arg = arg;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.rop}(${this.arg.emit(toplevel, fmt)})`;
    }
}

class LambdaInvokeExpression extends Expression {
    readonly name: string;
    readonly rec: RecursiveAnnotation;
    readonly args: ArgumentList;

    isCapturedLambda: boolean = false;
    lambda: LambdaTypeSignature | undefined = undefined;
    arginfo: TypeSignature[] = [];
    resttype: TypeSignature | undefined = undefined;
    restinfo: [number, boolean, TypeSignature][] | undefined = undefined;

    constructor(sinfo: SourceInfo, name: string, rec: RecursiveAnnotation, args: ArgumentList) {
        super(ExpressionTag.LambdaInvokeExpression, sinfo);
        this.name = name;
        this.rec = rec;
        this.args = args;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        let rec = "";
        if(this.rec !== "no") {
            rec = "[" + (this.rec === "yes" ? "recursive" : "recursive?") + "]";
        }
        
        return `${this.name}${rec}${this.args.emit(fmt, "(", ")")}`;
    }
}

class CallNamespaceFunctionExpression extends Expression {
    readonly ns: FullyQualifiedNamespace;
    readonly isImplicitNS: boolean;

    readonly name: string;
    readonly rec: RecursiveAnnotation;
    readonly terms: TypeSignature[];
    readonly args: ArgumentList;

    shuffleinfo: [number, TypeSignature][] = [];
    resttype: TypeSignature | undefined = undefined;
    restinfo: [number, boolean, TypeSignature][] | undefined = undefined;

    constructor(sinfo: SourceInfo, isImplicitNS: boolean, ns: FullyQualifiedNamespace, name: string, terms: TypeSignature[], rec: RecursiveAnnotation, args: ArgumentList) {
        super(ExpressionTag.CallNamespaceFunctionExpression, sinfo);
        this.ns = ns;
        this.isImplicitNS = isImplicitNS;
        this.name = name;
        this.rec = rec;
        this.terms = terms;
        this.args = args;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        let rec = "";
        if(this.rec !== "no") {
            rec = "[" + (this.rec === "yes" ? "recursive" : "recursive?") + "]";
        }
        
        let terms = "";
        if(this.terms.length !== 0) {
            terms = "<" + this.terms.map((tt) => tt.emit()).join(", ") + ">";
        }

        return `${!this.isImplicitNS ? (this.ns.emit() + "::") : ""}${this.name}${rec}${terms}${this.args.emit(fmt, "(", ")")}`;
    }
}

class CallTypeFunctionExpression extends Expression {
    readonly ttype: TypeSignature;
    readonly name: string;
    readonly rec: RecursiveAnnotation;
    readonly terms: TypeSignature[];
    readonly args: ArgumentList;

    isSpecialCall: boolean = false;
    resolvedDeclType: TypeSignature | undefined = undefined;
    shuffleinfo: [number, TypeSignature][] = [];
    resttype: TypeSignature | undefined = undefined;
    restinfo: [number, boolean, TypeSignature][] | undefined = undefined;

    constructor(sinfo: SourceInfo, ttype: TypeSignature, name: string, terms: TypeSignature[], rec: RecursiveAnnotation, args: ArgumentList) {
        super(ExpressionTag.CallTypeFunctionExpression, sinfo);
        this.ttype = ttype;
        this.name = name;
        this.rec = rec;
        this.terms = terms;
        this.args = args;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        let rec = "";
        if(this.rec !== "no") {
            rec = "[" + (this.rec === "yes" ? "recursive" : "recursive?") + "]";
        }
        
        let terms = "";
        if(this.terms.length !== 0) {
            terms = "<" + this.terms.map((tt) => tt.emit()).join(", ") + ">";
        }

        return `${this.ttype.emit()}::${this.name}${rec}${terms}${this.args.emit(fmt, "(", ")")}`;
    }
}

class CallRefInvokeExpression extends Expression {
    readonly rcvr: AccessVariableExpression;
    readonly specificResolve: TypeSignature | undefined;
    readonly name: string;
    readonly rec: RecursiveAnnotation;
    readonly terms: TypeSignature[];
    readonly args: ArgumentList;

    shuffleinfo: [number, TypeSignature][] = [];
    resttype: TypeSignature | undefined = undefined;
    restinfo: [number, boolean, TypeSignature][] | undefined = undefined;
    resolvedTrgt: TypeSignature | undefined = undefined;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, rcvr: AccessVariableExpression, specificResolve: TypeSignature | undefined, name: string, terms: TypeSignature[], rec: RecursiveAnnotation, args: ArgumentList) {
        super(tag, sinfo);
        this.rcvr = rcvr;
        this.specificResolve = specificResolve;
        this.name = name;
        this.rec = rec;
        this.terms = terms;
        this.args = args;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        let rec = "";
        if(this.rec !== "no") {
            rec = "[" + (this.rec === "yes" ? "recursive" : "recursive?") + "]";
        }
        
        let terms = "";
        if(this.terms.length !== 0) {
            terms = "<" + this.terms.map((tt) => tt.emit()).join(", ") + ">";
        }

        return `ref ${this.rcvr.emit(true, fmt)}.${this.specificResolve ? this.specificResolve.emit() + "::" : ""}${this.name}${rec}${terms}${this.args.emit(fmt, "(", ")")}`;
    }
}

class CallRefVariableExpression extends CallRefInvokeExpression {
    constructor(sinfo: SourceInfo, rcvr: AccessVariableExpression, specificResolve: TypeSignature | undefined, name: string, terms: TypeSignature[], rec: RecursiveAnnotation, args: ArgumentList) {
        super(ExpressionTag.CallRefVariableExpression, sinfo, rcvr, specificResolve, name, terms, rec, args);
    }
}

class CallRefThisExpression extends CallRefInvokeExpression {
    constructor(sinfo: SourceInfo, rcvr: AccessVariableExpression, specificResolve: TypeSignature | undefined, name: string, terms: TypeSignature[], rec: RecursiveAnnotation, args: ArgumentList) {
        super(ExpressionTag.CallRefThisExpression, sinfo, rcvr, specificResolve, name, terms, rec, args);
    }
}

class CallRefSelfExpression extends CallRefInvokeExpression {
    constructor(sinfo: SourceInfo, rcvr: AccessVariableExpression, name: string, terms: TypeSignature[], rec: RecursiveAnnotation, args: ArgumentList) {
        super(ExpressionTag.CallRefSelfExpression, sinfo, rcvr, undefined, name, terms, rec, args);
    }
}

class CallTaskActionExpression extends Expression {
    readonly name: string;
    readonly terms: TypeSignature[];
    readonly args: ArgumentList;

    constructor(sinfo: SourceInfo, name: string, terms: TypeSignature[], args: ArgumentList) {
        super(ExpressionTag.CallTaskActionExpression, sinfo);
        this.name = name;
        this.terms = terms;
        this.args = args;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        let terms = "";
        if(this.terms.length !== 0) {
            terms = "<" + this.terms.map((tt) => tt.emit()).join(", ") + ">";
        }

        return `do self.${this.name}${terms}${this.args.emit(fmt, "(", ")")}`;
    }
}

class ParseAsTypeExpression extends Expression {
    readonly exp: Expression;
    readonly ttype: TypeSignature;

    constructor(sinfo: SourceInfo, exp: Expression, ttype: TypeSignature) {
        super(ExpressionTag.ParseAsTypeExpression, sinfo);
        this.exp = exp;
        this.ttype = ttype;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `<${this.ttype.emit()}>(${this.exp.emit(toplevel, fmt)})`;
    }
}

class SafeConvertExpression extends Expression {
    readonly exp: Expression;
    readonly srctype: TypeSignature;
    readonly trgttype: TypeSignature;

    constructor(sinfo: SourceInfo, exp: Expression, srctype: TypeSignature, trgttype: TypeSignature) {
        super(ExpressionTag.SafeConvertExpression, sinfo);
        this.exp = exp;
        this.srctype = srctype;
        this.trgttype = trgttype;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `s_safeas<${this.srctype.emit()}, ${this.trgttype.emit()}>(${this.exp.emit(toplevel, fmt)})`;
    }
}

class CreateDirectExpression extends Expression {
    readonly exp: Expression;
    readonly srctype: TypeSignature;
    readonly trgttype: TypeSignature;

    constructor(sinfo: SourceInfo, exp: Expression, srctype: TypeSignature, trgttype: TypeSignature) {
        super(ExpressionTag.CreateDirectExpression, sinfo);
        this.exp = exp;
        this.srctype = srctype;
        this.trgttype = trgttype;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `s_createDirect<${this.srctype.emit()}, ${this.trgttype.emit()}>(${this.exp.emit(toplevel, fmt)})`;
    }
}

enum PostfixOpTag {
    PostfixError = "PostfixError",

    PostfixAccessFromName = "PostfixAccessFromName",
    PostfixProjectFromNames = "PostfixProjectFromNames",

    PostfixAccessFromIndex = "PostfixAccessFromIndex",

    PostfixIsTest = "PostfixIsTest",
    PostfixAsConvert = "PostfixAsConvert",

    PostfixAssignFields = "PostfixAssignFields",

    PostfixInvoke = "PostfixInvoke",
    PostfixLiteralKeyAccess = "PostfixLiteralKeyAccess"
}

abstract class PostfixOperation {
    readonly sinfo: SourceInfo;
    readonly tag: PostfixOpTag;

    private rcvrType: TypeSignature | undefined = undefined;
    private etype: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, tag: PostfixOpTag) {
        this.sinfo = sinfo;
        this.tag = tag;
    }

    getRcvrType(): TypeSignature {
        assert(this.rcvrType !== undefined, "Type signature not set");
        return this.rcvrType as TypeSignature;
    }

    setRcvrType(rcvrType: TypeSignature): TypeSignature {
        this.rcvrType = rcvrType;
        return rcvrType;
    }

    getType(): TypeSignature {
        assert(this.etype !== undefined, "Type signature not set");
        return this.etype as TypeSignature;
    }

    setType(etype: TypeSignature): TypeSignature {
        this.etype = etype;
        return etype;
    }

    abstract emit(fmt: CodeFormatter): string;
}

class PostfixOp extends Expression {
    readonly rootExp: Expression;
    readonly ops: PostfixOperation[];

    constructor(sinfo: SourceInfo, root: Expression, ops: PostfixOperation[]) {
        super(ExpressionTag.PostfixOpExpression, sinfo);
        this.rootExp = root;
        this.ops = ops;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        let res = this.rootExp.emit(false, fmt);
        for(let i = 0; i < this.ops.length; ++i) {
            res += this.ops[i].emit(fmt);
        }

        return res;
    }
}

class PostfixError extends PostfixOperation {
    constructor(sinfo: SourceInfo) {
        super(sinfo, PostfixOpTag.PostfixError);
    }

    emit(fmt: CodeFormatter): string {
        return "[!ERROR!]";
    }
}

class PostfixAccessFromName extends PostfixOperation {
    readonly name: string;
    
    declaredInType: TypeSignature | undefined = undefined;
    fieldDecl: MemberFieldDecl | undefined = undefined;

    constructor(sinfo: SourceInfo, name: string) {
        super(sinfo, PostfixOpTag.PostfixAccessFromName);
        this.name = name;
    }

    emit(fmt: CodeFormatter): string {
        return `.${this.name}`;
    }
}

class PostfixProjectFromNames extends PostfixOperation {
    readonly names: string[];

    constructor(sinfo: SourceInfo, names: string[]) {
        super(sinfo, PostfixOpTag.PostfixProjectFromNames);
        this.names = names;
    }

    emit(fmt: CodeFormatter): string {
        return `.(|${this.names.join(", ")}|)`;
    }
}

class PostfixAccessFromIndex extends PostfixOperation {
    readonly idx: number;

    constructor(sinfo: SourceInfo, idx: number) {
        super(sinfo, PostfixOpTag.PostfixAccessFromIndex);
        this.idx = idx;
    }

    emit(fmt: CodeFormatter): string {
        return `.${this.idx}`;
    }
}

class PostfixIsTest extends PostfixOperation {
    readonly ttest: ITest;

    constructor(sinfo: SourceInfo, ttest: ITest) {
        super(sinfo, PostfixOpTag.PostfixIsTest);
        this.ttest = ttest;
    }

    emit(fmt: CodeFormatter): string {
        return "?" + this.ttest.emit(fmt);
    }
}

class PostfixAsConvert extends PostfixOperation {
    readonly ttest: ITest;

    constructor(sinfo: SourceInfo, ttest: ITest) {
        super(sinfo, PostfixOpTag.PostfixAsConvert);
        this.ttest = ttest;
    }

    emit(fmt: CodeFormatter): string {
        return "@" + this.ttest.emit(fmt);
    }
}

class PostfixAssignFields extends PostfixOperation {
    readonly updates: [string, Expression][];

    constructor(sinfo: SourceInfo, updates: [string, Expression][]) {
        super(sinfo, PostfixOpTag.PostfixAssignFields);
        this.updates = updates;
    }

    emit(fmt: CodeFormatter): string {
        const updates = this.updates.map(([name, exp]) => `${name} = ${exp.emit(true, fmt)}`).join(", ");
        return `[${updates}]`;
    }

    updatetype: TypeSignature | undefined = undefined;
    updateinfo: {fieldname: string, fieldtype: TypeSignature, etype: TypeSignature}[] = [];
    isdirect: boolean = false;
}

class PostfixInvoke extends PostfixOperation {
    readonly specificResolve: TypeSignature | undefined;
    readonly name: string;
    readonly rec: RecursiveAnnotation;
    readonly terms: TypeSignature[];
    readonly args: ArgumentList;

    shuffleinfo: [number, TypeSignature][] = [];
    resttype: TypeSignature | undefined = undefined;
    restinfo: [number, boolean, TypeSignature][] | undefined = undefined;
    resolvedTrgt: TypeSignature | undefined = undefined;
    resolvedMethod: MethodDecl | undefined = undefined;

    constructor(sinfo: SourceInfo, specificResolve: TypeSignature | undefined, name: string, terms: TypeSignature[], rec: RecursiveAnnotation, args: ArgumentList) {
        super(sinfo, PostfixOpTag.PostfixInvoke);
        this.specificResolve = specificResolve;
        this.name = name;
        this.rec = rec;
        this.terms = terms;
        this.args = args;
    }

    emit(fmt: CodeFormatter): string {
        let rec = "";
        if(this.rec !== "no") {
            rec = "[" + (this.rec === "yes" ? "recursive" : "recursive?") + "]";
        }

        let terms = "";
        if(this.terms.length !== 0) {
            terms = "<" + this.terms.map((tt) => tt.emit()).join(", ") + ">";
        }

        return `.${this.specificResolve ? this.specificResolve.emit() + "::" : ""}${this.name}${rec}${terms}${this.args.emit(fmt, "(", ")")}`;
    }
}

class PostfixLiteralKeyAccess extends PostfixOperation {
    readonly kexp: Expression;

    constructor(sinfo: SourceInfo, kexp: Expression) {
        super(sinfo, PostfixOpTag.PostfixLiteralKeyAccess);
        this.kexp = kexp;
    }

    emit(fmt: CodeFormatter): string {
        return `[${this.kexp.emit(true, fmt)}]`;
    }
}

abstract class UnaryExpression extends Expression {
    readonly exp: Expression;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, exp: Expression) {
        super(tag, sinfo);
        this.exp = exp;
    }

    uopEmit(toplevel: boolean, fmt: CodeFormatter, op: string): string {
        let ee = `${this.exp.emit(false, fmt)}`;
        if(op === "-" || op === "+") {
            ee = `(${ee})`;
        }
        ee = `${op}${ee}`;
        
        return toplevel ? ee : `(${ee})`;
    }
}

class PrefixNotOpExpression extends UnaryExpression {
    opertype: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, exp: Expression) {
        super(ExpressionTag.PrefixNotOpExpression, sinfo, exp);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.uopEmit(toplevel, fmt, "!");
    }
}

class PrefixNegateOrPlusOpExpression extends UnaryExpression {
    readonly op: "-" | "+";

    opertype: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, exp: Expression, op: "-" | "+") {
        super(ExpressionTag.PrefixNegateOrPlusOpExpression, sinfo, exp);
        this.op = op;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.uopEmit(toplevel, fmt, this.op);
    }
}

abstract class BinaryArithExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    opertype: TypeSignature | undefined = undefined;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(tag, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }

    baopEmit(toplevel: boolean, fmt: CodeFormatter, op: string): string {
        const ee = `${this.lhs.emit(false, fmt)} ${op} ${this.rhs.emit(false, fmt)}`;
        return toplevel ? ee : `(${ee})`;
    }
}

class BinAddExpression extends BinaryArithExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinAddExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.baopEmit(toplevel, fmt, "+");
    }
}

class BinSubExpression extends BinaryArithExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinSubExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.baopEmit(toplevel, fmt, "-");
    }
}

class BinMultExpression extends BinaryArithExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinMultExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.baopEmit(toplevel, fmt, "*");
    }
}

class BinDivExpression extends BinaryArithExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinDivExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.baopEmit(toplevel, fmt, "//");
    }
}

abstract class BinaryKeyExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    operkind: "err" | "lhsnone" | "rhsnone" | "stricteq" | "lhskeyeqoption" | "rhskeyeqoption" | undefined;
    opertype: TypeSignature | undefined = undefined;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(tag, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }

    bkopEmit(toplevel: boolean, fmt: CodeFormatter, op: string): string {
        const ee = `${this.lhs.emit(false, fmt)} ${op} ${this.rhs.emit(false, fmt)}`;
        return toplevel ? ee : `(${ee})`;
    }
}

class BinKeyEqExpression extends BinaryKeyExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinKeyEqExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.bkopEmit(toplevel, fmt, "===");
    }
}

class BinKeyNeqExpression extends BinaryKeyExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinKeyNeqExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.bkopEmit(toplevel, fmt, "!==");
    }
}

class KeyCompareEqExpression extends Expression {
    readonly ktype: TypeSignature;
    readonly lhs: Expression;
    readonly rhs: Expression;

    optype: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, ktype: TypeSignature, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.KeyCompareEqExpression, sinfo);
        this.ktype = ktype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `KeyComparator::equal<${this.ktype.emit()}>(${this.lhs.emit(false, fmt)}, ${this.rhs.emit(false, fmt)})`;
    }
}

class KeyCompareLessExpression extends Expression {
    readonly ktype: TypeSignature;
    readonly lhs: Expression;
    readonly rhs: Expression;

    optype: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, ktype: TypeSignature, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.KeyCompareLessExpression, sinfo);
        this.ktype = ktype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `KeyComparator::less<${this.ktype.emit()}>(${this.lhs.emit(false, fmt)}, ${this.rhs.emit(false, fmt)})`;
    }
}

abstract class BinaryNumericExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    opertype: TypeSignature | undefined = undefined;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(tag, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }

    bnopEmit(toplevel: boolean, fmt: CodeFormatter, op: string): string {
        const ee = `${this.lhs.emit(false, fmt)} ${op} ${this.rhs.emit(false, fmt)}`;
        return toplevel ? ee : `(${ee})`;
    }
}

class NumericEqExpression extends BinaryNumericExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericEqExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.bnopEmit(toplevel, fmt, "==");
    }
}

class NumericNeqExpression extends BinaryNumericExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericNeqExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.bnopEmit(toplevel, fmt, "!=");
    }
}

class NumericLessExpression extends BinaryNumericExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericLessExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.bnopEmit(toplevel, fmt, "<");
    }
}

class NumericLessEqExpression extends BinaryNumericExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericLessEqExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.bnopEmit(toplevel, fmt, "<=");
    }
}

class NumericGreaterExpression extends BinaryNumericExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericGreaterExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.bnopEmit(toplevel, fmt, ">");
    }
}

class NumericGreaterEqExpression extends BinaryNumericExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericGreaterEqExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.bnopEmit(toplevel, fmt, ">=");
    }
}

abstract class BinLogicExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    purebool: boolean = true;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(tag, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }

    blopEmit(toplevel: boolean, fmt: CodeFormatter, op: string): string {
        const ee = `${this.lhs.emit(false, fmt)} ${op} ${this.rhs.emit(false, fmt)}`;
        return toplevel ? ee : `(${ee})`;
    }
}

class BinLogicAndExpression extends BinLogicExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinLogicAndExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.blopEmit(toplevel, fmt, "&&");
    }
}

class BinLogicOrExpression extends BinLogicExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinLogicOrExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.blopEmit(toplevel, fmt, "||");
    }
}

class MapEntryConstructorExpression extends Expression {
    readonly kexp: Expression;
    readonly vexp: Expression;

    ctype: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, kexp: Expression, vexp: Expression) {
        super(ExpressionTag.MapEntryConstructorExpression, sinfo);
        this.kexp = kexp;
        this.vexp = vexp;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.kexp.emit(toplevel, fmt)} => ${this.vexp.emit(toplevel, fmt)}`;
    }
}

class IfTest {
    readonly exp: Expression;
    readonly itestopt: ITest | undefined;

    constructor(exp: Expression, itestopt: ITest | undefined) {
        this.exp = exp;
        this.itestopt = itestopt;
    }
}

class IfExpression extends Expression {
    readonly test: IfTest;
    readonly binder: BinderInfo | undefined;
    readonly trueValue: Expression
    readonly falseValue: Expression;

    trueBindType: TypeSignature | undefined = undefined;
    falseBindType: TypeSignature | undefined = undefined

    constructor(sinfo: SourceInfo, test: IfTest, binder: BinderInfo | undefined, trueValue: Expression, falseValue: Expression) {
        super(ExpressionTag.IfExpression, sinfo);
        this.test = test;
        this.binder = binder;
        this.trueValue = trueValue;
        this.falseValue = falseValue;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        let bexps: [string, string] = ["", ""];
        if(this.binder !== undefined) {
            bexps = this.binder.emit();
        }

        const itest = this.test.itestopt !== undefined ? `${this.test.itestopt.emit(fmt)}` : "";
        
        const ttest = `(${bexps[0]}${this.test.exp.emit(true, fmt)})${bexps[1]}${itest}`;
        const iif =  `if${ttest} then ${this.trueValue.emit(true, fmt)} else ${this.falseValue.emit(true, fmt)}`;

        return toplevel ? iif : `(${iif})`;
    }
}

enum ChkLogicExpressionTag {
    ChkLogicImpliesExpression = "ChkLogicImpliesExpression",
    ChkLogicBaseExpression = "ChkLogicBaseExpression"
}

abstract class ChkLogicExpression {
    readonly tag: ChkLogicExpressionTag;

    constructor(tag: ChkLogicExpressionTag) {
        this.tag = tag;
    }

    abstract emit(fmt: CodeFormatter): string;
}

class ChkLogicImpliesExpression extends ChkLogicExpression {
    readonly sinfo: SourceInfo;

    readonly lhs: ITestGuardSet;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: ITestGuardSet, rhs: Expression) {
        super(ChkLogicExpressionTag.ChkLogicImpliesExpression);

        this.sinfo = sinfo;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    emit(fmt: CodeFormatter): string {
        return `${this.lhs.emit(fmt)} ==> ${this.rhs.emit(true, fmt)}`;
    }
}

class ChkLogicBaseExpression extends ChkLogicExpression {
    readonly exp: Expression;
    
    constructor(exp: Expression) {
        super(ChkLogicExpressionTag.ChkLogicBaseExpression);

        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return this.exp.emit(true, fmt);
    }
}

enum RValueExpressionTag {
    ConditionalValueExpression = "ConditionalValueExpression",
    ShortCircuitAssignRHSExpressionFail = "ShortCircuitAssignRHSExpressionFail",
    ShortCircuitAssignRHSExpressionReturn = "ShortCircuitAssignRHSExpressionReturn",
    BaseExpression = "BaseExpression"
}

abstract class RValueExpression {
    readonly tag: RValueExpressionTag;

    constructor(tag: RValueExpressionTag) {
        this.tag = tag;
    }

    abstract emit(fmt: CodeFormatter): string;
}

abstract class ConditionalValueExpression extends RValueExpression {
    readonly sinfo: SourceInfo;

    readonly guardset: ITestGuardSet;

    readonly trueValue: Expression
    readonly falseValue: Expression;

    trueBindType: TypeSignature | undefined = undefined;
    falseBindType: TypeSignature | undefined = undefined

    constructor(sinfo: SourceInfo, guardset: ITestGuardSet, trueValue: Expression, falseValue: Expression) {
        super(RValueExpressionTag.ConditionalValueExpression);

        this.sinfo = sinfo;

        this.guardset = guardset;

        this.trueValue = trueValue;
        this.falseValue = falseValue;
    }

    emit(fmt: CodeFormatter): string {
        const ttest = this.guardset.emit(fmt);
        return `${ttest} ? ${this.trueValue.emit(true, fmt)} : ${this.falseValue.emit(true, fmt)}`;
    }
}

abstract class ShortCircuitAssignRHSITestExpression extends RValueExpression {
    readonly exp: Expression; //Can be a RHS expression too
    readonly itest: ITest;

    constructor(tag: RValueExpressionTag, exp: Expression, itest: ITest) {
        super(tag);

        this.exp = exp;
        this.itest = itest;
    }
}

class ShortCircuitAssignRHSExpressionFail extends ShortCircuitAssignRHSITestExpression {
    constructor(exp: Expression, itest: ITest) {
        super(RValueExpressionTag.ShortCircuitAssignRHSExpressionFail, exp, itest);
    }

    emit(fmt: CodeFormatter): string {
        return `${this.exp.emit(true, fmt)} @@${this.itest.emit(fmt)}`;
    }
}

class ShortCircuitAssignRHSExpressionReturn extends ShortCircuitAssignRHSITestExpression {
    readonly failexp: Expression | undefined;

    constructor(exp: Expression, itest: ITest, failexp: Expression | undefined) {
        super(RValueExpressionTag.ShortCircuitAssignRHSExpressionReturn, exp, itest);
        this.failexp = failexp;
    }

    emit(fmt: CodeFormatter): string {
        if(this.failexp === undefined) {
            return `${this.exp.emit(true, fmt)} ?@${this.itest.emit(fmt)}`;
        }
        else {
            return `${this.exp.emit(true, fmt)} ?@${this.itest.emit(fmt)} : ${this.failexp.emit(true, fmt)}`;
        }
    }
}

class BaseRValueExpression extends RValueExpression {
    readonly exp: Expression;

    constructor(exp: Expression) {
        super(RValueExpressionTag.BaseExpression);

        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return this.exp.emit(true, fmt);
    }
}

enum EnvironmentGenerationExpressionTag {
    ErrorEnvironmentExpresion = "ErrorEnvironmentExpresion",
    EmptyEnvironmentExpression = "EmptyEnvironmentExpression",
    InitializeEnvironmentExpression = "InitializeEnvironmentExpression",
    CurrentEnvironmentExpression = "CurrentEnvironmentExpression",
    PostfixEnvironmentOpExpression = "PostfixEnvironmentOpExpression"
}

abstract class EnvironmentGenerationExpression {
    readonly tag: EnvironmentGenerationExpressionTag;
    readonly sinfo: SourceInfo;

    constructor(tag: EnvironmentGenerationExpressionTag, sinfo: SourceInfo) {
        this.tag = tag;
        this.sinfo = sinfo;
    }

    abstract emit(fmt: CodeFormatter): string;
}

class ErrorEnvironmentExpression extends EnvironmentGenerationExpression {
    constructor(sinfo: SourceInfo) {
        super(EnvironmentGenerationExpressionTag.ErrorEnvironmentExpresion, sinfo);
    }

    emit(fmt: CodeFormatter): string {
        return "[!ERROR!]";
    }
}

abstract class BaseEnvironmentOpExpression extends EnvironmentGenerationExpression {
    constructor(tag: EnvironmentGenerationExpressionTag, sinfo: SourceInfo) {
        super(tag, sinfo);
    }
}

class EmptyEnvironmentExpression extends BaseEnvironmentOpExpression {
    constructor(sinfo: SourceInfo) {
        super(EnvironmentGenerationExpressionTag.EmptyEnvironmentExpression, sinfo);
    }

    emit(fmt: CodeFormatter): string {
        return "env{}";
    }
}

class InitializeEnvironmentExpression extends BaseEnvironmentOpExpression {
    readonly args: {envkey: Expression, value: Expression}[]; //literal is a cstring

    constructor(sinfo: SourceInfo, args: {envkey: Expression, value: Expression}[]) {
        super(EnvironmentGenerationExpressionTag.InitializeEnvironmentExpression, sinfo);
        this.args = args;
    }

    emit(fmt: CodeFormatter): string {
        const argl = this.args.map((arg) => `${arg.envkey.emit(true, fmt)} => ${arg.value.emit(true, fmt)}`).join(", ");
        return `env{ ${argl} }`;
    }
}

class CurrentEnvironmentExpression extends BaseEnvironmentOpExpression {
    constructor (sinfo: SourceInfo) {
        super(EnvironmentGenerationExpressionTag.CurrentEnvironmentExpression, sinfo);
    }

    emit(fmt: CodeFormatter): string {
        return "env";
    }
}

enum PostfixEnvironmentOpTag {
    PostfixEnvironmentOpError = "PostfixEnvironmentOpError",
    PostfixEnvironmentOpSet = "PostfixEnvironmentOpSet"
}

abstract class PostfixEnvironmentOp {
    readonly sinfo: SourceInfo;
    readonly op: PostfixEnvironmentOpTag;

    constructor(sinfo: SourceInfo, op: PostfixEnvironmentOpTag) {
        this.sinfo = sinfo;
        this.op = op;
    }

    abstract emit(fmt: CodeFormatter): string;
}

class PostFixEnvironmentOpError extends PostfixEnvironmentOp {
    constructor(sinfo: SourceInfo) {
        super(sinfo, PostfixEnvironmentOpTag.PostfixEnvironmentOpError);
    }

    emit(fmt: CodeFormatter): string {
        return "[!ERROR!]";
    }
}

class PostfixEnvironmentOpSet extends PostfixEnvironmentOp {
    readonly updates: {envkey: Expression, value: Expression}[]; //literal is a cstring

    constructor(sinfo: SourceInfo, updates: {envkey: Expression, value: Expression}[]) {
        super(sinfo, PostfixEnvironmentOpTag.PostfixEnvironmentOpSet);
        this.updates = updates;
    }

    emit(fmt: CodeFormatter): string {
        const updatel = this.updates.map((arg) => `${arg.envkey.emit(true, fmt)} => ${arg.value.emit(true, fmt)}`).join(", ");
        return `[| ${updatel} |]`;
    }
}

class PostfixEnvironmentOpExpression extends EnvironmentGenerationExpression {
    readonly baseenv: BaseEnvironmentOpExpression;
    readonly followop: PostfixEnvironmentOp;

    constructor(sinfo: SourceInfo, baseenv: BaseEnvironmentOpExpression, followop: PostfixEnvironmentOp) {
        super(EnvironmentGenerationExpressionTag.PostfixEnvironmentOpExpression, sinfo);
        this.baseenv = baseenv;
        this.followop = followop;
    }

    emit(fmt: CodeFormatter): string {
        return `${this.baseenv.emit(fmt)}${this.followop.emit(fmt)}`;
    }
}

class TaskRunExpression extends Expression {
    readonly task: TypeSignature;
    readonly args: ArgumentList;
    readonly envi: EnvironmentGenerationExpression | undefined;
    readonly enva: EnvironmentGenerationExpression;

    constructor(sinfo: SourceInfo, task: TypeSignature, args: ArgumentList, envi: EnvironmentGenerationExpression | undefined, enva: EnvironmentGenerationExpression) {
        super(ExpressionTag.TaskRunExpression, sinfo);
        this.task = task;
        this.args = args;
        this.envi = envi;
        this.enva = enva;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const argl = this.args.emit(fmt, "", "");
        return `Task::run<${this.task.emit() + (this.envi !== undefined ? ", " + this.envi.emit(fmt) : "")}>(${argl}, ${this.enva.emit(fmt)})`;
    }
}

class TaskMultiExpression extends Expression {
    readonly tasks: TypeSignature[];
    readonly args: [ArgumentList, EnvironmentGenerationExpression][];
    readonly envi: EnvironmentGenerationExpression | undefined;

    constructor(sinfo: SourceInfo, tasks: TypeSignature[], args: [ArgumentList, EnvironmentGenerationExpression][], envi: EnvironmentGenerationExpression | undefined) {
        super(ExpressionTag.TaskMultiExpression, sinfo);
        this.tasks = tasks;
        this.args = args;
        this.envi = envi;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const argl = this.args.map((arg) => `${arg[0].emit(fmt, "", "")}, ${arg[1].emit(fmt)}`);
        return `Task::run<${this.tasks.map((tt) => tt.emit()).join(", ") + (this.envi !== undefined ? ", " + this.envi.emit(fmt) : "")}>(${argl.join("; ")})`;
    }
}

class TaskDashExpression extends Expression {
    readonly tasks: TypeSignature[];
    readonly args: [ArgumentList, EnvironmentGenerationExpression][];
    readonly envi: EnvironmentGenerationExpression | undefined;

    constructor(sinfo: SourceInfo, tasks: TypeSignature[], args: [ArgumentList, EnvironmentGenerationExpression][], envi: EnvironmentGenerationExpression | undefined) {
        super(ExpressionTag.TaskDashExpression, sinfo);
        this.tasks = tasks;
        this.args = args;
        this.envi = envi;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const argl = this.args.map((arg) => `${arg[0].emit(fmt, "", "")}, ${arg[1].emit(fmt)}`);
        return `Task::dash<${this.tasks.map((tt) => tt.emit()).join(", ") + (this.envi !== undefined ? ", " + this.envi.emit(fmt) : "")}>(${argl.join("; ")})`;
    }
}

class TaskAllExpression extends Expression {
    readonly tasks: TypeSignature[];
    readonly args: [ArgumentList, EnvironmentGenerationExpression][];
    readonly envi: EnvironmentGenerationExpression | undefined;

    constructor(sinfo: SourceInfo, tasks: TypeSignature[], args: [ArgumentList, EnvironmentGenerationExpression][], envi: EnvironmentGenerationExpression | undefined) {
        super(ExpressionTag.TaskAllExpression, sinfo);
        this.tasks = tasks;
        this.args = args;
        this.envi = envi;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const argl = this.args.map((arg) => `${arg[0].emit(fmt, "", "")}, ${arg[1].emit(fmt)}`);
        return `Task::all<${this.tasks.map((tt) => tt.emit()).join(", ") + (this.envi !== undefined ? ", " + this.envi.emit(fmt) : "")}>(${argl.join("; ")})`;
    }
}

class TaskRaceExpression extends Expression {
    readonly tasks: TypeSignature[];
    readonly args: [ArgumentList, EnvironmentGenerationExpression][];
    readonly envi: EnvironmentGenerationExpression | undefined;

    constructor(sinfo: SourceInfo, tasks: TypeSignature[], args: [ArgumentList, EnvironmentGenerationExpression][], envi: EnvironmentGenerationExpression | undefined) {
        super(ExpressionTag.TaskRaceExpression, sinfo);
        this.tasks = tasks;
        this.args = args;
        this.envi = envi;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const argl = this.args.map((arg) => `${arg[0].emit(fmt, "", "")}, ${arg[1].emit(fmt)}`);
        return `Task::race<${this.tasks.map((tt) => tt.emit()).join(", ") + (this.envi !== undefined ? ", " + this.envi.emit(fmt) : "")}>(${argl.join("; ")})`;
    }
}

enum StatementTag {
    Clear = "[CLEAR]",
    ErrorStatement = "ErrorStatement",

    EmptyStatement = "EmptyStatement",

    VariableDeclarationStatement = "VariableDeclarationStatement",
    VariableMultiDeclarationStatement = "VariableMultiDeclarationStatement",
    VariableInitializationStatement = "VariableInitializationStatement",
    VariableMultiInitializationStatement = "VariableMultiInitializationStatement",
    VariableAssignmentStatement = "VariableAssignmentStatement",
    VariableMultiAssignmentStatement = "VariableMultiAssignmentStatement",

    VariableRetypeStatement = "VariableRetypeStatement",
    ReturnVoidStatement = "ReturnVoidStatement",
    ReturnSingleStatement = "ReturnSingleStatement",
    ReturnMultiStatement = "ReturnMultiStatement",

    IfStatement = "IfStatement",
    IfElseStatement = "IfElseStatement",
    IfElifElseStatement = "IfElifElseStatement",
    SwitchStatement = "SwitchStatement",
    MatchStatement = "MatchStatement",

    AbortStatement = "AbortStatement",
    AssertStatement = "AssertStatement", //assert(x > 0)
    ValidateStatement = "ValidateStatement", //assert(x > 0)

    DebugStatement = "DebugStatement", //print an arg or if empty attach debugger

    VoidRefCallStatement = "VoidRefCallStatement",
    VarUpdateStatement = "VarUpdateStatement",
    ThisUpdateStatement = "ThisUpdateStatement",
    SelfUpdateStatement = "SelfUpdateStatement",

    EnvironmentUpdateStatement = "EnvironmentUpdateStatement",
    EnvironmentBracketStatement = "EnvironmentBracketStatement",

    TaskStatusStatement = "TaskStatusStatement", //do a status emit Task::emitStatusUpdate(...)

    TaskYieldStatement = "TaskYieldStatement", //result exp (probably a do)

    BlockStatement = "BlockStatement"
}

abstract class Statement {
    readonly tag: StatementTag;
    readonly sinfo: SourceInfo;

    constructor(tag: StatementTag, sinfo: SourceInfo) {
        this.tag = tag;
        this.sinfo = sinfo;
    }

    abstract emit(fmt: CodeFormatter): string;
}

class ErrorStatement extends Statement {
    constructor(sinfo: SourceInfo) {
        super(StatementTag.ErrorStatement, sinfo);
    }

    emit(fmt: CodeFormatter): string {
        return `[error]`;
    }
}

class EmptyStatement extends Statement {
    constructor(sinfo: SourceInfo) {
        super(StatementTag.EmptyStatement, sinfo);
    }

    emit(fmt: CodeFormatter): string {
        return ";";
    }
}

class VariableDeclarationStatement extends Statement {
    readonly name: string;
    readonly vtype: TypeSignature;

    constructor(sinfo: SourceInfo, name: string, vtype: TypeSignature) {
        super(StatementTag.VariableDeclarationStatement, sinfo);
        this.name = name;
        this.vtype = vtype;
    }

    emit(fmt: CodeFormatter): string {
        return `var ${this.name}: ${this.vtype.emit()};`;
    }
}

class VariableMultiDeclarationStatement extends Statement {
    readonly decls: {name: string, vtype: TypeSignature}[];

    constructor(sinfo: SourceInfo, decls: {name: string, vtype: TypeSignature}[]) {
        super(StatementTag.VariableMultiDeclarationStatement, sinfo);
        this.decls = decls;
    }

    emit(fmt: CodeFormatter): string {
        return `var ${this.decls.map((dd) => `${dd.name}: ${dd.vtype.emit()}`).join(", ")};`;
    }
}

class VariableInitializationStatement extends Statement {
    readonly vkind: "var" | "ref" | "let";
    readonly name: string;
    readonly vtype: TypeSignature; //maybe Auto
    actualtype: TypeSignature | undefined = undefined;
    readonly exp: RValueExpression;

    constructor(sinfo: SourceInfo, vkind: "var" | "ref" | "let", name: string, vtype: TypeSignature, exp: RValueExpression) {
        super(StatementTag.VariableInitializationStatement, sinfo);
        this.vkind = vkind;
        this.name = name;
        this.vtype = vtype;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        const tt = this.vtype instanceof AutoTypeSignature ? "" : `: ${this.vtype.emit()}`;

        return `${this.vkind} ${this.name}${tt} = ${this.exp.emit(fmt)};`;
    }
}

class VariableMultiInitializationStatement extends Statement {
    readonly vkind: "var" | "ref" | "let";
    readonly decls: {name: string, vtype: TypeSignature}[]; //maybe Auto
    actualtypes: TypeSignature[] = [];
    readonly exp: Expression | Expression[]; //could be a single expression of type EList or multiple expressions

    constructor(sinfo: SourceInfo, vkind: "var" | "ref" | "let", decls: {name: string, vtype: TypeSignature}[], exp: Expression | Expression[]) {
        super(StatementTag.VariableMultiInitializationStatement, sinfo);
        this.vkind = vkind;
        this.decls = decls;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        const ttdecls = this.decls.map((dd) => dd.name + (dd.vtype instanceof AutoTypeSignature ? "" : `: ${dd.vtype.emit()}`));
        const ttexp = Array.isArray(this.exp) ? this.exp.map((ee) => ee.emit(true, fmt)).join(", ") : this.exp.emit(true, fmt);

        return `${this.vkind} ${ttdecls.join(", ")} = ${ttexp};`;
    }
}

class VariableAssignmentStatement extends Statement {
    readonly name: string;
    vtype: TypeSignature | undefined = undefined;
    readonly exp: RValueExpression;

    constructor(sinfo: SourceInfo, name: string, exp: RValueExpression) {
        super(StatementTag.VariableAssignmentStatement, sinfo);
        this.name = name;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return `${this.name} = ${this.exp.emit(fmt)};`;
    }
}

class VariableMultiAssignmentStatement extends Statement {
    readonly names: string[];
    vtypes: TypeSignature[] = [];
    readonly exp: Expression | Expression[]; //could be a single expression of type EList or multiple expressions

    constructor(sinfo: SourceInfo, names: string[], exp: Expression | Expression[]) {
        super(StatementTag.VariableMultiAssignmentStatement, sinfo);
        this.names = names;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        const ttname = this.names.join(", ");
        const ttexp = Array.isArray(this.exp) ? this.exp.map((ee) => ee.emit(true, fmt)).join(", ") : this.exp.emit(true, fmt);

        return `${ttname} = ${ttexp};`;
    }
}

class VariableRetypeStatement extends Statement {
    readonly name: string;
    vtype: TypeSignature | undefined = undefined;
    newvtype: TypeSignature | undefined = undefined;
    readonly ttest: ITest;

    constructor(sinfo: SourceInfo, name: string, ttest: ITest) {
        super(StatementTag.VariableRetypeStatement, sinfo);
        this.name = name;
        this.ttest = ttest;
    }

    emit(fmt: CodeFormatter): string {
        return `ref ${this.name}@${this.ttest.emit(fmt)};`;
    }
}

class ReturnVoidStatement extends Statement {
    constructor(sinfo: SourceInfo) {
        super(StatementTag.ReturnVoidStatement, sinfo);
    }

    emit(fmt: CodeFormatter): string {
        return `return;`;
    }
}

class ReturnSingleStatement extends Statement {
    readonly value: RValueExpression;
    rtype: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, value: RValueExpression) {
        super(StatementTag.ReturnSingleStatement, sinfo);
        this.value = value;
    }

    emit(fmt: CodeFormatter): string {
        return `return ${this.value.emit(fmt)};`;
    }
}

class ReturnMultiStatement extends Statement {
    readonly value: Expression[]; //array is implicitly converted to EList
    rtypes: TypeSignature[] = [];
    elsig: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, value: Expression[]) {
        super(StatementTag.ReturnMultiStatement, sinfo);
        this.value = value;
    }

    emit(fmt: CodeFormatter): string {
        return `return ${this.value.map((vv) => vv.emit(true, fmt)).join(", ")};`;
    }
}

class IfStatement extends Statement {
    readonly cond: IfTest;
    readonly binder: BinderInfo | undefined;
    readonly trueBlock: BlockStatement;
    
    trueBindType: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, cond: IfTest, binder: BinderInfo | undefined, trueBlock: BlockStatement) {
        super(StatementTag.IfStatement, sinfo);
        this.cond = cond;
        this.binder = binder;
        this.trueBlock = trueBlock;
    }

    emit(fmt: CodeFormatter): string {
        let bexps: [string, string] = ["", ""];
        if(this.binder !== undefined) {
            bexps = this.binder.emit();
        }

        const itest = this.cond.itestopt !== undefined ? `${this.cond.itestopt.emit(fmt)}` : "";
        
        const ttest = `(${bexps[0]}${this.cond.exp.emit(true, fmt)})${bexps[1]}${itest}`;
        return `if${ttest} ${this.trueBlock.emit(fmt)}`;
    }
}

class IfElseStatement extends Statement {
    readonly cond: IfTest;
    readonly binder: BinderInfo | undefined;
    readonly trueBlock: BlockStatement;
    readonly falseBlock: BlockStatement;

    trueBindType: TypeSignature | undefined = undefined;
    falseBindType: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, cond: IfTest, binder: BinderInfo | undefined, trueBlock: BlockStatement,falseBlock: BlockStatement) {
        super(StatementTag.IfElseStatement, sinfo);
        this.cond = cond;
        this.binder = binder;
        this.trueBlock = trueBlock;
        this.falseBlock = falseBlock;
    }

    emit(fmt: CodeFormatter): string {
        let bexps: [string, string] = ["", ""];
        if(this.binder !== undefined) {
            bexps = this.binder.emit();
        }

        const itest = this.cond.itestopt !== undefined ? `${this.cond.itestopt.emit(fmt)}` : "";
        
        const ttest = `(${bexps[0]}${this.cond.exp.emit(true, fmt)})${bexps[1]}${itest}`;
        
        const ttif = this.trueBlock.emit(fmt);
        const ttelse = this.falseBlock.emit(fmt);

        return [`if${ttest} ${ttif}`, `else ${ttelse}`].join("\n");
    }
}

class IfElifElseStatement extends Statement {
    readonly condflow: {cond: Expression, block: BlockStatement}[];
    readonly elseflow: BlockStatement;

    constructor(sinfo: SourceInfo, condflow: {cond: Expression, block: BlockStatement}[], elseflow: BlockStatement) {
        super(StatementTag.IfElifElseStatement, sinfo);
        this.condflow = condflow;
        this.elseflow = elseflow;
    }

    emit(fmt: CodeFormatter): string {
        const ttcond = this.condflow.map((cf) => `$(${cf.cond.emit(true, fmt)}) ${cf.block.emit(fmt)}`);
        const ttelse = this.elseflow.emit(fmt);

        const iif = `if${ttcond[0]}`;
        const ielifs = [...ttcond.slice(1).map((cc) => fmt.indent(`elif${cc}`)), fmt.indent(`else ${ttelse}`)];

        return [iif, ...ielifs].join("\n");
    }
}

class SwitchStatement extends Statement {
    readonly sval: Expression;
    readonly switchflow: {lval: Expression | undefined, value: BlockStatement}[];

    mustExhaustive: boolean = false;
    optypes: TypeSignature[] = [];

    constructor(sinfo: SourceInfo, sval: Expression, flow: {lval: Expression | undefined, value: BlockStatement}[]) {
        super(StatementTag.SwitchStatement, sinfo);
        this.sval = sval;
        this.switchflow = flow;
    }

    emit(fmt: CodeFormatter): string {
        const mheader = `switch(${this.sval.emit(true, fmt)})`;
        fmt.indentPush();
        const ttmf = this.switchflow.map((sf) => `${sf.lval ? sf.lval.emit(true, fmt) : "_"} => ${sf.value.emit(fmt)}`);
        fmt.indentPop();

        const iir = ttmf.map((cc) => fmt.indent("| " + cc));
        return `${mheader} {\n${iir.join("\n")}\n${fmt.indent("}")}`;
    }
}

class MatchStatement extends Statement {
    readonly sval: [Expression, BinderInfo | undefined];
    readonly matchflow: {mtype: TypeSignature | undefined, value: BlockStatement}[];

    mustExhaustive: boolean = false;
    implicitFinalType: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, sval: [Expression, BinderInfo | undefined], flow: {mtype: TypeSignature | undefined, value: BlockStatement}[]) {
        super(StatementTag.MatchStatement, sinfo);
        this.sval = sval;
        this.matchflow = flow;
    }

    emit(fmt: CodeFormatter): string {
        let bexps: [string, string] = ["", ""];
        if(this.sval[1] !== undefined) {
            bexps = this.sval[1].emit();
        }

        const mheader = `match(${bexps[0]}${this.sval[0].emit(true, fmt)})${bexps[1]}`;
        fmt.indentPush();
        const ttmf = this.matchflow.map((mf) => `${mf.mtype ? mf.mtype.emit() : "_"} => ${mf.value.emit(fmt)}`);
        fmt.indentPop();

        const iir = ttmf.map((cc) => fmt.indent("| " + cc));
        return `${mheader} {\n${iir.join("\n")}\n${fmt.indent("}")}`;
    }
}

class AbortStatement extends Statement {
    constructor(sinfo: SourceInfo) {
        super(StatementTag.AbortStatement, sinfo);
    }

    emit(fmt: CodeFormatter): string {
        return `abort;`;
    }
}

class AssertStatement extends Statement {
    readonly cond: ChkLogicExpression;
    readonly level: BuildLevel;

    constructor(sinfo: SourceInfo, cond: ChkLogicExpression, level: BuildLevel) {
        super(StatementTag.AssertStatement, sinfo);
        this.cond = cond;
        this.level = level;
    }

    emit(fmt: CodeFormatter): string {
        const level = (this.level !== "release") ? (" " + this.level) : "";
        return `assert${level} ${this.cond.emit(fmt)};`;
    }
}

class ValidateStatement extends Statement {
    readonly cond: ChkLogicExpression;
    readonly diagnosticTag: string | undefined

    constructor(sinfo: SourceInfo, cond: ChkLogicExpression, diagnosticTag: string | undefined) {
        super(StatementTag.ValidateStatement, sinfo);
        this.cond = cond;
        this.diagnosticTag = diagnosticTag;
    }

    emit(fmt: CodeFormatter): string {
        const ttg = (this.diagnosticTag !== undefined) ? `[${this.diagnosticTag}]` : "";
        return `validate${ttg} ${this.cond.emit(fmt)};`;
    }
}

class DebugStatement extends Statement {
    readonly value: Expression;

    constructor(sinfo: SourceInfo, value: Expression) {
        super(StatementTag.DebugStatement, sinfo);
        this.value = value;
    }

    emit(fmt: CodeFormatter): string {
        return `_debug ${this.value.emit(true, fmt)};`;
    }
}

class VoidRefCallStatement extends Statement {
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, exp: Expression) {
        super(StatementTag.VoidRefCallStatement, sinfo);
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return `${this.exp.emit(true, fmt)};`;
    }
}

abstract class UpdateStatement extends Statement {
    readonly vexp: AccessVariableExpression;
    readonly updates: [string, Expression][];

    constructor(sinfo: SourceInfo, tag: StatementTag, vexp: AccessVariableExpression, updates: [string, Expression][]) {
        super(tag, sinfo);

        this.vexp = vexp;
        this.updates = updates;
    }

    emit(fmt: CodeFormatter): string {
        const updates = this.updates.map(([name, exp]) => `${name} = ${exp.emit(true, fmt)}`).join(", ");
        return `ref ${this.vexp.emit(true, fmt)}[${updates}];`;
    }

    updatetype: TypeSignature | undefined = undefined;
    updateinfo: {fieldname: string, fieldtype: TypeSignature, etype: TypeSignature}[] = [];
    isdirect: boolean = false;
}

class VarUpdateStatement extends UpdateStatement {
    constructor(sinfo: SourceInfo, vexp: AccessVariableExpression, updates: [string, Expression][]) {
        super(sinfo, StatementTag.VarUpdateStatement, vexp, updates);
    }
}

class ThisUpdateStatement extends UpdateStatement {
    constructor(sinfo: SourceInfo, vexp: AccessVariableExpression, updates: [string, Expression][]) {
        super(sinfo, StatementTag.ThisUpdateStatement, vexp, updates);
    }
}

class SelfUpdateStatement extends Statement {
    readonly updates: [string, Expression][];

    constructor(sinfo: SourceInfo, updates: [string, Expression][]) {
        super(StatementTag.SelfUpdateStatement, sinfo);

        this.updates = updates;
    }

    emit(fmt: CodeFormatter): string {
        const updates = this.updates.map(([name, exp]) => `${name} = ${exp.emit(true, fmt)}`).join(", ");
        return `ref self[${updates}];`;
    }
}

class EnvironmentUpdateStatement extends Statement {
    readonly updates: [Expression, Expression][];

    constructor(sinfo: SourceInfo, updates: [Expression, Expression][]) {
        super(StatementTag.EnvironmentUpdateStatement, sinfo);
        this.updates = updates;
    }

    emit(fmt: CodeFormatter): string {
        const updates = this.updates.map(([name, exp]) => `${name.emit(true, fmt)} = ${exp.emit(true, fmt)}`).join(", ");
        return `env[|${updates}|];`;
    }
}

class EnvironmentBracketStatement extends Statement {
    readonly env: EnvironmentGenerationExpression;
    readonly block: BlockStatement;

    constructor(sinfo: SourceInfo, env: EnvironmentGenerationExpression, block: BlockStatement) {
        super(StatementTag.EnvironmentBracketStatement, sinfo);
        this.env = env;
        this.block = block;
    }

    emit(fmt: CodeFormatter): string {
        return `${this.env.emit(fmt)} ${this.block.emit(fmt)}`;
    }
}

class TaskStatusStatement extends Statement {
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, exp: Expression) {
        super(StatementTag.TaskStatusStatement, sinfo);
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return `Task::status(${this.exp.emit(true, fmt)});`;
    }
}

class TaskYieldStatement extends Statement {
    readonly name: string;
    readonly terms: TypeSignature[];
    readonly args: ArgumentList;

    constructor(sinfo: SourceInfo, name: string, terms: TypeSignature[], args: ArgumentList) {
        super(StatementTag.TaskYieldStatement, sinfo);
        this.name = name;
        this.terms = terms;
        this.args = args;
    }

    emit(fmt: CodeFormatter): string {
        let terms = "";
        if(this.terms.length !== 0) {
            terms = "<" + this.terms.map((tt) => tt.emit()).join(", ") + ">";
        }

        return `yield self.${this.name}${terms}${this.args.emit(fmt, "(", ")")};`;
    }
}

class BlockStatement extends Statement {
    readonly statements: Statement[];
    readonly isScoping: boolean;

    constructor(sinfo: SourceInfo, statements: Statement[], isScoping: boolean) {
        super(StatementTag.BlockStatement, sinfo);
        this.statements = statements;
        this.isScoping = isScoping;
    }

    emit(fmt: CodeFormatter): string {
        fmt.indentPush();
        const bb = this.statements.map((stmt) => fmt.indent(stmt.emit(fmt))).join("\n");
        fmt.indentPop();

        return this.isScoping ? `{${bb}${fmt.indent("}")}` : `{|${bb}${fmt.indent("|}")}`;
    }
}

abstract class BodyImplementation {
    readonly sinfo: SourceInfo;
    readonly file: string;

    constructor(sinfo: SourceInfo, file: string) {
        this.sinfo = sinfo;
        this.file = file;
    }

    abstract emit(fmt: CodeFormatter, headerstr: string | undefined): string;
}

class AbstractBodyImplementation extends BodyImplementation {
    constructor(sinfo: SourceInfo, file: string) {
        super(sinfo, file);
    }

    emit(fmt: CodeFormatter, headerstr: string | undefined): string {
        if(headerstr === undefined) {
            return ";";
        }
        else {
            return headerstr + ";";
        }
    }
}

class PredicateUFBodyImplementation extends BodyImplementation {
    constructor(sinfo: SourceInfo, file: string) {
        super(sinfo, file);
    }

    emit(fmt: CodeFormatter, headerstr: string | undefined): string {
        if(headerstr === undefined) {
            return "%* Uninterpreted Function as predicate for checking *%;";
        }
        else {
            return headerstr + "%* Uninterpreted Function as predicate for checking *%;";
        }
    }
}

class BuiltinBodyImplementation extends BodyImplementation {
    readonly builtin: string;

    constructor(sinfo: SourceInfo, file: string, builtin: string) {
        super(sinfo, file);

        this.builtin = builtin;
    }

    emit(fmt: CodeFormatter, headerstr: string | undefined): string {
        if(headerstr === undefined) {
            return ` = ${this.builtin};`;
        }
        else {
            return " = " + headerstr + this.builtin + ";";
        }
    }
}

class ExpressionBodyImplementation extends BodyImplementation {
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, file: string, exp: Expression) {
        super(sinfo, file);
        this.exp = exp;
    }

    emit(fmt: CodeFormatter, headerstr: string | undefined): string {
        let hstr = "";
        if(headerstr !== undefined) {
            hstr = " " + headerstr;
        }

        return `${hstr} ${this.exp.emit(true, fmt)}`;
    }
}

class StandardBodyImplementation extends BodyImplementation {
    readonly statements: Statement[];

    constructor(sinfo: SourceInfo, file: string, statements: Statement[]) {
        super(sinfo, file);
        this.statements = statements;
    }

    emit(fmt: CodeFormatter, headerstr: string | undefined): string {
        let hstr = "";
        if(headerstr !== undefined) {
            hstr = headerstr + "\n" + fmt.indent("");
        }

        fmt.indentPush();
        const bb = this.statements.map((stmt, i) => {
            let ss = stmt.emit(fmt);
            if(i !== this.statements.length - 1) {
                return ss;
            }
            else {
                if(stmt.tag === StatementTag.IfElseStatement || stmt.tag === StatementTag.SwitchStatement || stmt.tag === StatementTag.MatchStatement || stmt.tag === StatementTag.BlockStatement) {
                    return ss + "\n";
                }
                else {
                    return ss;
                }
            }
        }).join("\n");
        fmt.indentPop();

        return `${hstr}{\n${bb}\n${fmt.indent("}")}`;
    }
}

export {
    RecursiveAnnotation,
    BinderInfo, ITest, ITestType, ITestNone, ITestSome, ITestOk, ITestFail, ITestFailed, ITestRejected, ITestError, ITestSuccess,
    ITestGuard, ITestBinderGuard, ITestSimpleGuard, ITestGuardSet,
    ArgumentValue, RefArgumentValue, OutArgumentValue, OutCondArgumentValue, InOutArgumentValue, PositionalArgumentValue, NamedArgumentValue, SpreadArgumentValue, ArgumentList,
    ExpressionTag, Expression, ErrorExpression,
    LiteralNoneExpression, LiteralSimpleExpression, LiteralRegexExpression,
    LiteralTypeDeclValueExpression,
    AccessEnvValueExpression, TaskAccessInfoExpression,
    AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessEnumExpression, AccessVariableExpression,
    ConstructorExpression, ConstructorPrimaryExpression, ConstructorEListExpression,
    ConstructorLambdaExpression, SpecialConstructorExpression, SpecialConverterExpression,
    LambdaInvokeExpression,
    CallNamespaceFunctionExpression, CallTypeFunctionExpression, 
    CallRefInvokeExpression, CallRefVariableExpression, CallRefThisExpression, CallRefSelfExpression, 
    CallTaskActionExpression,
    ParseAsTypeExpression, SafeConvertExpression, CreateDirectExpression,
    PostfixOpTag, PostfixOperation, PostfixOp,
    PostfixError, PostfixAccessFromName, PostfixAccessFromIndex, PostfixProjectFromNames,
    PostfixIsTest, PostfixAsConvert,
    PostfixAssignFields,
    PostfixInvoke,
    PostfixLiteralKeyAccess,
    UnaryExpression, PrefixNotOpExpression, PrefixNegateOrPlusOpExpression,
    BinaryArithExpression, BinAddExpression, BinSubExpression, BinMultExpression, BinDivExpression,
    BinaryKeyExpression, BinKeyEqExpression, BinKeyNeqExpression, KeyCompareEqExpression, KeyCompareLessExpression,
    BinaryNumericExpression, NumericEqExpression, NumericNeqExpression, NumericLessExpression, NumericLessEqExpression, NumericGreaterExpression, NumericGreaterEqExpression,
    BinLogicExpression, BinLogicAndExpression, BinLogicOrExpression,
    MapEntryConstructorExpression,
    IfTest,
    IfExpression, 
    ChkLogicExpressionTag, ChkLogicExpression, ChkLogicImpliesExpression, ChkLogicBaseExpression,
    RValueExpressionTag, RValueExpression, ConditionalValueExpression, ShortCircuitAssignRHSITestExpression, ShortCircuitAssignRHSExpressionFail, ShortCircuitAssignRHSExpressionReturn, BaseRValueExpression,
    EnvironmentGenerationExpressionTag, EnvironmentGenerationExpression, ErrorEnvironmentExpression,
    TaskRunExpression, TaskMultiExpression, TaskDashExpression, TaskAllExpression, TaskRaceExpression,
    BaseEnvironmentOpExpression, EmptyEnvironmentExpression, InitializeEnvironmentExpression, CurrentEnvironmentExpression, 
    PostfixEnvironmentOpTag, PostfixEnvironmentOp, PostFixEnvironmentOpError, PostfixEnvironmentOpSet, PostfixEnvironmentOpExpression,
    StatementTag, Statement, ErrorStatement, EmptyStatement,
    VariableDeclarationStatement, VariableMultiDeclarationStatement, VariableInitializationStatement, VariableMultiInitializationStatement, VariableAssignmentStatement, VariableMultiAssignmentStatement,
    VariableRetypeStatement,
    ReturnVoidStatement, ReturnSingleStatement, ReturnMultiStatement,
    IfStatement, IfElseStatement, IfElifElseStatement, SwitchStatement, MatchStatement, AbortStatement, AssertStatement, ValidateStatement, DebugStatement,
    VoidRefCallStatement, UpdateStatement, VarUpdateStatement, ThisUpdateStatement, SelfUpdateStatement,
    EnvironmentUpdateStatement, EnvironmentBracketStatement,
    TaskStatusStatement,
    TaskYieldStatement,
    BlockStatement, 
    BodyImplementation, AbstractBodyImplementation, PredicateUFBodyImplementation, BuiltinBodyImplementation, ExpressionBodyImplementation, StandardBodyImplementation
};
