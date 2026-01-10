import assert from "node:assert";

import { FullyQualifiedNamespace, AutoTypeSignature, RecursiveAnnotation, TypeSignature, LambdaTypeSignature, NominalTypeSignature } from "./type.js";

import { BuildLevel, CodeFormatter, SourceInfo } from "./build_decls.js";
import { LambdaDecl, MemberFieldDecl, MethodDecl, NamespaceDeclaration, TaskConfiguration } from "./assembly.js";

class BinderInfo {
    readonly srcname: string; //the name in the source code
    readonly implicitdef: boolean;

    constructor(srcname: string, implicitdef: boolean) {
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

abstract class ITestGuard {
    readonly exp: Expression;
    
    constructor(exp: Expression) {
        this.exp = exp;
    }

    abstract emit(mustparens: boolean, fmt: CodeFormatter): string;
}

class ITestBinderGuard extends ITestGuard {
    readonly itest: ITest;
    readonly bindinfo: BinderInfo;

    constructor(exp: Expression, itest: ITest, bindinfo: BinderInfo ) {
        super(exp);
        this.itest = itest;
        this.bindinfo = bindinfo;
    }

    emit(mustparens: boolean, fmt: CodeFormatter): string {
        return `(${this.bindinfo.emitoptdef()}${this.exp.emit(true, fmt)})@${this.itest.emit(fmt)}`;
    }
}

class ITestTypeGuard extends ITestGuard {
    readonly itest: ITest;

    constructor(exp: Expression, itest: ITest) {
        super(exp);
        this.itest = itest;
    }

    emit(mustparens: boolean, fmt: CodeFormatter): string {
        return `(${this.exp.emit(true, fmt)})${this.itest.emit(fmt)}`;
    }
}

class ITestSimpleGuard extends ITestGuard {
    emit(mustparens: boolean, fmt: CodeFormatter): string {
        let ee = this.exp.emit(true, fmt);
        return mustparens ? `(${ee})` : ee;
    }
}

class ITestGuardSet {
    readonly guards: ITestGuard[];

    constructor(guards: ITestGuard[]) {
        this.guards = guards;
    }

    emit(fmt: CodeFormatter): string {
        if(this.guards.length === 1) {
            return this.guards[0].emit(true, fmt);
        }
        else {
            return this.guards.map((g) => g.emit(false, fmt)).join(" && ");
        }
    }
}

abstract class FormatStringComponent {
    abstract emit(): string;
}

class FormatStringTextComponent extends FormatStringComponent {
    readonly text: string;
    resolvedValue: string | undefined = undefined; //after unescaping

    constructor(text: string) {
        super();
        this.text = text;
    }

    emit(): string {
        return this.text;
    }
}

class FormatStringArgComponent extends FormatStringComponent {
    readonly argPos: string; //name
    readonly argType: TypeSignature; //can be AutoTypeSignature, string, or typed string
    resolvedType: TypeSignature | undefined; //after type checking

    constructor(argPos: string, argType: TypeSignature) {
        super();
        this.argPos = argPos;
        this.argType = argType;
    }

    emit(): string {
        return `%{${this.argPos}: ${this.argType.emit()}}`;
    }
}

abstract class ArgumentValue {
    readonly exp: Expression;

    constructor(exp: Expression) {
        this.exp = exp;
    }

    abstract emit(fmt: CodeFormatter): string;
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

class PassingArgumentValue extends ArgumentValue {
    readonly kind: "ref" | "out" | "out?" | "inout";

    constructor(kind: "ref" | "out" | "out?" | "inout", exp: Expression) {
        super(exp);
        this.kind = kind;
    }

    emit(fmt: CodeFormatter): string {
        return `${this.kind} ${this.exp.emit(true, fmt)}`;
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
    LiteralChkNatExpression = "LiteralChkNatExpression",
    LiteralChkIntExpression = "LiteralChkIntExpression",
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

    LiteralByteExpression = "LiteralByteExpression",
    LiteralCCharExpression = "LiteralCCharExpression",
    LiteralUnicodeCharExpression = "LiteralUnicodeCharExpression",

    LiteralStringExpression = "LiteralStringExpression",
    LiteralCStringExpression = "LiteralCStringExpression",
    LiteralFormatStringExpression = "LiteralFormatStringExpression",
    LiteralFormatCStringExpression = "LiteralFormatCStringExpression",

    LiteralPathExpression = "LiteralPathExpression",
    LiteralPathFragmentExpression = "LiteralPathFragmentExpression",
    LiteralGlobExpression = "LiteralGlobExpression",

    LiteralFormatPathExpression = "LiteralFormatPathExpression",
    LiteralFormatPathFragmentExpression = "LiteralFormatPathFragmentExpression",
    LiteralFormatGlobExpression = "LiteralFormatGlobExpression",

    LiteralTypeDeclValueExpression = "LiteralTypeDeclValueExpression",

    LiteralTypedStringExpression = "LiteralTypedStringExpression",
    LiteralTypedCStringExpression = "LiteralTypedCStringExpression",
    LiteralTypedFormatStringExpression = "LiteralTypedFormatStringExpression",
    LiteralTypedFormatCStringExpression = "LiteralTypedFormatCStringExpression",

    LiteralTypedPathExpression = "LiteralTypedPathExpression",
    LiteralTypedPathFormatExpression = "LiteralTypedPathFragmentExpression",
    
    AccessEnvValueExpression = "AccessEnvValueExpression",

    TaskAccessIDExpression = "TaskAccessIDExpression",
    TaskAccessParentIDExpression = "TaskAccessParentIDExpression",

    AccessNamespaceConstantExpression = "AccessNamespaceConstantExpression",
    AccessStaticFieldExpression = " AccessStaticFieldExpression",
    AccessEnumExpression = "AccessEnumExpression",
    AccessVariableExpression = "AccessVariableExpression",

    ConstructorPrimaryExpression = "ConstructorPrimaryExpression",
    ConstructorEListExpression = "ConstructorEListExpression",
    ConstructorLambdaExpression = "ConstructorLambdaExpression",

    LambdaInvokeExpression = "LambdaInvokeExpression",
    SpecialConstructorExpression = "SpecialConstructorExpression",
    CallNamespaceFunctionExpression = "CallNamespaceFunctionExpression",
    CallTypeFunctionExpression = "CallTypeFunctionExpression",
    CallRefVariableExpression = "CallRefVariableExpression",
    CallRefThisExpression = "CallRefThisExpression",
    CallRefSelfExpression = "CallRefSelfExpression",
    CallTaskActionExpression = "CallTaskActionExpression",

    ParseAsTypeExpression = "ParseAsTypeExpression",

    InterpolateFormatStringExpression = "InterpolateFormatStringExpression",

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

    LogicAndExpression = "LogicAndExpression",
    LogicOrExpression = "LogicOrExpression",

    HoleExpression = "HoleExpression",

    MapEntryConstructorExpression = "MapEntryConstructorExpression",

    TaskRunExpression = "TaskRunExpression", //run single task
    TaskMultiExpression = "TaskMultiExpression", //run multiple explicitly identified tasks -- complete all
    TaskAllExpression = "TaskAllExpression", //run the same task on all args in a list -- complete all
    TaskDashExpression = "TaskDashExpression", //run multiple explicitly identified tasks -- first (successful) completion wins
    TaskDashAnyExpression = "TaskDashAnyExpression", //run multiple explicitly identified tasks -- first completion (successful or failing) wins
    TaskRaceExpression = "TaskRaceExpression", //run the same task on all args in a list -- first (successful) completion wins
    TaskRaceAnyExpression = "TaskRaceAnyExpression", //run the same task on all args in a list -- first completion (successful or failing) wins

    APIInvokeExpression = "APIInvokeExpression",
    AgentInvokeExpression = "AgentInvokeExpression"
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

class LiteralStringExpression extends Expression {
    readonly value: string;
    resolvedValue: string | undefined = undefined; //e.g. for string types after unescaping

    constructor(sinfo: SourceInfo, value: string) {
        super(ExpressionTag.LiteralStringExpression, sinfo);
        this.value = value;
    }

    override isLiteralExpression(): boolean {
        return true;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.value;
    }
}

class LiteralCStringExpression extends Expression {
    readonly value: string;
    resolvedValue: string | undefined = undefined; //e.g. for string types after unescaping

    constructor(sinfo: SourceInfo, value: string) {
        super(ExpressionTag.LiteralCStringExpression, sinfo);
        this.value = value;
    }

    override isLiteralExpression(): boolean {
        return true;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.value;
    }
}

class LiteralFormatStringExpression extends Expression {
    readonly value: string;
    readonly fmts: FormatStringComponent[];

    constructor(sinfo: SourceInfo, value: string, fmts: FormatStringComponent[]) {
        super(ExpressionTag.LiteralFormatStringExpression, sinfo);
        this.value = value;
        this.fmts = fmts;
    }

    override isLiteralExpression(): boolean {
        return true;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.value
    }
}

class LiteralFormatCStringExpression extends Expression {
    readonly value: string;
    readonly fmts: FormatStringComponent[];

    constructor(sinfo: SourceInfo, value: string, fmts: FormatStringComponent[]) {
        super(ExpressionTag.LiteralFormatCStringExpression, sinfo);
        this.value = value;
        this.fmts = fmts;
    }

    override isLiteralExpression(): boolean {
        return true;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.value;
    }
}

class LiteralRegexExpression extends Expression {
    readonly inns: FullyQualifiedNamespace;
    readonly value: string;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, inns: FullyQualifiedNamespace, value: string) {
        super(tag, sinfo);
        this.inns = inns;
        this.value = value;
    }

    override isLiteralExpression(): boolean {
        return true;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.value;
    }
}

class LiteralPathItemExpression extends Expression {
    readonly value: string; //path, fragment, or glob (as in source)

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

class LiteralFormatPathItemExpression extends Expression {
    readonly value: string; //path, fragment, or glob (as in source)
    readonly fmts: FormatStringComponent[];

    constructor(tag: ExpressionTag, sinfo: SourceInfo, value: string, fmts: FormatStringComponent[]) {
        super(tag, sinfo);
        this.value = value;
        this.fmts = fmts;
    }

    override isLiteralExpression(): boolean {
        return true;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.value;
    }
}

class LiteralTypeDeclValueExpression extends Expression {
    readonly value: Expression;
    readonly constype: TypeSignature;

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

class LiteralTypedStringExpression extends Expression {
    readonly value: string;
    readonly constype: TypeSignature;

    resolvedValue: string | undefined = undefined; //e.g. for string types after unescaping

    constructor(sinfo: SourceInfo, value: string, constype: TypeSignature) {
        super(ExpressionTag.LiteralTypedStringExpression, sinfo);
        this.value = value;
        this.constype = constype;
    }

    override isLiteralExpression(): boolean {
        return true;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.value}<${this.constype.emit()}>`;
    }
}

class LiteralTypedCStringExpression extends Expression {
    readonly value: string;
    readonly constype: TypeSignature;

    resolvedValue: string | undefined = undefined; //e.g. for string types after unescaping

    constructor(sinfo: SourceInfo, value: string, constype: TypeSignature) {
        super(ExpressionTag.LiteralTypedCStringExpression, sinfo);
        this.value = value;
        this.constype = constype;
    }

    override isLiteralExpression(): boolean {
        return true;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.value}<${this.constype.emit()}>`;
    }
}

class LiteralTypedFormatStringExpression extends Expression {
    readonly value: string;
    readonly fmts: FormatStringComponent[];
    readonly constype: TypeSignature;

    constructor(sinfo: SourceInfo, value: string, fmts: FormatStringComponent[], constype: TypeSignature) {
        super(ExpressionTag.LiteralTypedFormatStringExpression, sinfo);
        this.value = value;
        this.fmts = fmts;
        this.constype = constype;
    }

    override isLiteralExpression(): boolean {
        return true;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.value}<${this.constype.emit()}>`;
    }
}

class LiteralTypedFormatCStringExpression extends Expression {
    readonly value: string;
    readonly fmts: FormatStringComponent[];
    readonly constype: TypeSignature;

    constructor(sinfo: SourceInfo, value: string, fmts: FormatStringComponent[], constype: TypeSignature) {
        super(ExpressionTag.LiteralTypedFormatCStringExpression, sinfo);
        this.value = value;
        this.fmts = fmts;
        this.constype = constype;
    }

    override isLiteralExpression(): boolean {
        return true;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `'${this.value}'<${this.constype.emit()}>`;
    }
}

class LiteralTypedPathExpression extends Expression {
    readonly value: string; //path (no fragments or globs)
    readonly constype: TypeSignature;

    constructor(sinfo: SourceInfo, value: string, constype: TypeSignature) {
        super(ExpressionTag.LiteralTypedPathExpression, sinfo);
        this.value = value;
        this.constype = constype;
    }

    override isLiteralExpression(): boolean {
        return true;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.value}<${this.constype.emit()}>`;
    }
}

class LiteralTypedPathFormatExpression extends Expression {
    readonly value: string; //path fragment
    readonly constype: TypeSignature;

    constructor(sinfo: SourceInfo, value: string, constype: TypeSignature) {
        super(ExpressionTag.LiteralTypedPathFormatExpression, sinfo);
        this.value = value;
        this.constype = constype;
    }

    override isLiteralExpression(): boolean {
        return true;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.value}<${this.constype.emit()}>`;
    }
}

class AccessEnvValueExpression extends Expression {
    readonly opname: "has" | "get" | "tryGet" | undefined;
    readonly keyname: string;

    resolvedkey: string | undefined = undefined;
    optoftype: TypeSignature | undefined = undefined;
    mustdefined: boolean = false;

    constructor(sinfo: SourceInfo, opname: "has" | "get" | "tryGet" | undefined, keyname: string) {
        super(ExpressionTag.AccessEnvValueExpression, sinfo);
        this.opname = opname;
        this.keyname = keyname;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        if(this.opname === undefined) {
            return `env.${this.keyname}`;
        }
        else {
            return `env.${this.opname}('${this.keyname}')`;
        }
    }
}

class TaskAccessInfoExpression extends Expression {
    readonly name: "currentID" | "parentID";

    constructor(tag: ExpressionTag, sinfo: SourceInfo, name: "currentID" | "parentID") {
        super(tag, sinfo);
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
    isParameter: boolean = false;
    isCaptured: boolean = false;
    scopeidx: number | undefined = undefined;

    constructor(sinfo: SourceInfo, srcname: string) {
        super(ExpressionTag.AccessVariableExpression, sinfo);
        this.srcname = srcname;
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

class InterpolateFormatExpression extends Expression {
    readonly kind: "string" | "cstring" | "path" | "fragment" | "glob";
    readonly decloftype: TypeSignature | undefined;
    readonly fmtString: Expression;
    readonly args: ArgumentValue[];
    
    actualoftype: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, kind: "string" | "cstring" | "path" | "fragment" | "glob", decloftype: TypeSignature | undefined, fmtString: Expression, args: ArgumentValue[]) {
        super(ExpressionTag.InterpolateFormatStringExpression, sinfo);
        this.kind = kind;
        this.decloftype = decloftype;
        this.fmtString = fmtString;
        this.args = args;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const fmtStr = this.fmtString.emit(true, fmt);
        const argsStr = this.args.map((a) => a.emit(fmt)).join(", ");
        return `Interpolate::${this.kind}${this.decloftype !== undefined ? `<${this.decloftype.emit()}>` : ""}(${fmtStr}, ${argsStr})`;
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

    PostfixOfOperator = "PostfixOfOperator",

    PostfixInvoke = "PostfixInvoke"
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

class PostfixOfOperator extends PostfixOperation {
    readonly args: ArgumentList;

    constructor(sinfo: SourceInfo, args: ArgumentList) {
        super(sinfo, PostfixOpTag.PostfixOfOperator);
        this.args = args;
    }

    emit(fmt: CodeFormatter): string {
        return `.of${this.args.emit(fmt, "(", ")")}`;
    }
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

abstract class UnaryExpression extends Expression {
    readonly exp: Expression;

    opertype: TypeSignature | undefined = undefined;

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
    constructor(sinfo: SourceInfo, exp: Expression) {
        super(ExpressionTag.PrefixNotOpExpression, sinfo, exp);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.uopEmit(toplevel, fmt, "!");
    }
}

class PrefixNegateOrPlusOpExpression extends UnaryExpression {
    readonly op: "-" | "+";

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

    operkind: "err" | "lhsnone" | "rhsnone" | "stricteq" | "lhskeyeqoption" | "rhskeyeqoption" | "lhskeyeqsome" | "rhskeyeqsome" | undefined;
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

abstract class LogicExpression extends Expression {
    readonly exps: Expression[];

    constructor(tag: ExpressionTag, sinfo: SourceInfo, exps: Expression[]) {
        super(tag, sinfo);
        this.exps = exps;
    }

    blopEmit(toplevel: boolean, fmt: CodeFormatter, op: string): string {
        const ee = this.exps.map((e) => e.emit(false, fmt)).join(` ${op} `);
        return toplevel ? ee : `(${ee})`;
    }
}

class LogicAndExpression extends LogicExpression {
    constructor(sinfo: SourceInfo, exps: Expression[]) {
        super(ExpressionTag.LogicAndExpression, sinfo, exps);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.blopEmit(toplevel, fmt, "&&");
    }
}

class LogicOrExpression extends LogicExpression {
    constructor(sinfo: SourceInfo, exps: Expression[]) {
        super(ExpressionTag.LogicOrExpression, sinfo, exps);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.blopEmit(toplevel, fmt, "||");
    }
}

class HoleExpression extends Expression {
    readonly hname: string | undefined;
    readonly captures: string[];
    readonly explicittype: TypeSignature | undefined;
    readonly doccomment: string | undefined;
    readonly samplesfile: Expression | undefined;
    
    constructor(sinfo: SourceInfo, hname: string | undefined, captures: string[], explicittype: TypeSignature | undefined, doccomment: string | undefined, samplesfile: Expression | undefined) {
        super(ExpressionTag.HoleExpression, sinfo);
        this.hname = hname;
        this.captures = captures;
        this.explicittype = explicittype;
        this.doccomment = doccomment;
        this.samplesfile = samplesfile;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const etype = this.explicittype ? ` -> ${this.explicittype.emit()}` : "";
        let ebody = "";
        if(this.doccomment !== undefined || this.samplesfile !== undefined) {
            const dcom = this.doccomment !== undefined ? `%** ${this.doccomment} **%` : "";
            const samplstr = this.samplesfile !== undefined ? ` of ${this.samplesfile.emit(false, fmt)}` : "";
            ebody = `(${dcom})${samplstr}`;
        }

        const hb = `?_${this.hname || ""}${this.captures.length !== 0 ? ("[" + this.captures.join(", ") + "]") : ""}${ebody}${etype}`;
        return toplevel ? hb : `(${hb})`;
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

enum EnvironmentGenerationExpressionTag {
    ErrorEnvironmentExpression = "ErrorEnvironmentExpression",
    EmptyEnvironmentExpression = "EmptyEnvironmentExpression",
    InitializeEnvironmentExpression = "InitializeEnvironmentExpression",
    CurrentEnvironmentExpression = "CurrentEnvironmentExpression"
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
        super(EnvironmentGenerationExpressionTag.ErrorEnvironmentExpression, sinfo);
    }

    emit(fmt: CodeFormatter): string {
        return "[!ERROR!]";
    }
}

class EmptyEnvironmentExpression extends EnvironmentGenerationExpression {
    constructor(sinfo: SourceInfo) {
        super(EnvironmentGenerationExpressionTag.EmptyEnvironmentExpression, sinfo);
    }

    emit(fmt: CodeFormatter): string {
        return "env{}";
    }
}

class InitializeEnvironmentExpression extends EnvironmentGenerationExpression {
    readonly args: {envkey: string, value: RValueExpression}[];

    constructor(sinfo: SourceInfo, args: {envkey: string, value: RValueExpression}[]) {
        super(EnvironmentGenerationExpressionTag.InitializeEnvironmentExpression, sinfo);
        this.args = args;
    }

    emit(fmt: CodeFormatter): string {
        const argl = this.args.map((arg) => `${arg.envkey} = ${arg.value.emit(true, fmt)}`).join(", ");
        return `env{ ${argl} }`;
    }
}

class CurrentEnvironmentExpression extends EnvironmentGenerationExpression {
    constructor (sinfo: SourceInfo) {
        super(EnvironmentGenerationExpressionTag.CurrentEnvironmentExpression, sinfo);
    }

    emit(fmt: CodeFormatter): string {
        return "env";
    }
}

abstract class TaskInvokeExpression extends Expression {
    constructor(tag: ExpressionTag, sinfo: SourceInfo) {
        super(tag, sinfo);
    }

    static emitconfigs(configs: TaskConfiguration, fmt: CodeFormatter): string {
        const ccf = configs.emit();
        
        if(ccf === undefined) {
            return "";
        }
        else {
            return `[${ccf}]`;
        }
    }
}

class TaskRunExpression extends TaskInvokeExpression {
    readonly task: TypeSignature;
    readonly configs: TaskConfiguration;
    readonly args: Expression[];
    readonly envexp: EnvironmentGenerationExpression;

    constructor(sinfo: SourceInfo, task: TypeSignature, args: Expression[], envexp: EnvironmentGenerationExpression, configs: TaskConfiguration) {
        super(ExpressionTag.TaskRunExpression, sinfo);
        this.task = task;
        this.configs = configs;
        this.args = args;
        this.envexp = envexp;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const configs = TaskInvokeExpression.emitconfigs(this.configs, fmt);
        const envexp = this.envexp.emit(fmt);
        const argl = this.args.map((arg) => arg.emit(true, fmt)).join(", ");

        return `Task::run<${this.task.emit()}${configs}>(${envexp}${argl !== "" ? (", " + argl) : ""})`;
    }
}

class TaskMultiExpression extends TaskInvokeExpression {
    readonly execmode: "parallel" | "sequential" | "std";
    readonly tasks: [TypeSignature, TaskConfiguration][];
    readonly args: [Expression[], EnvironmentGenerationExpression][];

    constructor(sinfo: SourceInfo, execmode: "parallel" | "sequential" | "std", tasks: [TypeSignature, TaskConfiguration][], args: [Expression[], EnvironmentGenerationExpression][]) {
        super(ExpressionTag.TaskMultiExpression, sinfo);
        this.execmode = execmode;
        this.tasks = tasks;
        this.args = args;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const taskstrs = this.tasks.map((tt) => {
            const configs = TaskInvokeExpression.emitconfigs(tt[1], fmt);
            return `${tt[0].emit()}${configs}`;
        });

        const argl = this.args.map((arg) => {
            const envexp = arg[1].emit(fmt);
            const argexp = arg[0].map((a) => a.emit(true, fmt)).join(", ");

            return `${envexp}${argexp !== "" ? (", " + argexp) : ""}`;
        });

        return `${this.execmode !== "std" ? `${this.execmode} ` : ""}Task::multi<${taskstrs.join(", ")}>(${argl.join("; ")})`;
    }
}

class TaskAllExpression extends TaskInvokeExpression {
    readonly execmode: "parallel" | "sequential" | "std";
    readonly task: TypeSignature;
    readonly configs: TaskConfiguration;
    readonly args: Expression;
    readonly envexp: EnvironmentGenerationExpression;

    constructor(sinfo: SourceInfo, execmode: "parallel" | "sequential" | "std", task: TypeSignature, args: Expression, envexp: EnvironmentGenerationExpression, configs: TaskConfiguration) {
        super(ExpressionTag.TaskAllExpression, sinfo);
        this.execmode = execmode;
        this.task = task;
        this.configs = configs;
        this.args = args;
        this.envexp = envexp;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const configs = TaskInvokeExpression.emitconfigs(this.configs, fmt);
        const envexp = this.envexp.emit(fmt);
        const argl = this.args.emit(true, fmt);

        return `${this.execmode !== "std" ? `${this.execmode} ` : ""}Task::all<${this.task.emit()}${configs}>(${envexp}, ${argl})`;
    }
}

class TaskDashExpression extends TaskInvokeExpression {
    readonly execmode: "parallel" | "sequential" | "std";
    readonly tasks: [TypeSignature, TaskConfiguration][];
    readonly args: [Expression[], EnvironmentGenerationExpression][];

    constructor(sinfo: SourceInfo, execmode: "parallel" | "sequential" | "std", tasks: [TypeSignature, TaskConfiguration][], args: [Expression[], EnvironmentGenerationExpression][]) {
        super(ExpressionTag.TaskDashExpression, sinfo);
        this.execmode = execmode;
        this.tasks = tasks;
        this.args = args;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const taskstrs = this.tasks.map((tt) => {
            const configs = TaskInvokeExpression.emitconfigs(tt[1], fmt);
            return `${tt[0].emit()}${configs}`;
        });

        const argl = this.args.map((arg) => {
            const envexp = arg[1].emit(fmt);
            const argexp = arg[0].map((a) => a.emit(true, fmt)).join(", ");

            return `${envexp}${argexp !== "" ? (", " + argexp) : ""}`;
        });

        return `${this.execmode !== "std" ? `${this.execmode} ` : ""}Task::dash<${taskstrs.join(", ")}>(${argl.join("; ")})`;
    }
}

class TaskDashAnyExpression extends TaskInvokeExpression {
    readonly execmode: "parallel" | "sequential" | "std";
    readonly tasks: [TypeSignature, TaskConfiguration][];
    readonly args: [Expression[], EnvironmentGenerationExpression][];

    constructor(sinfo: SourceInfo, execmode: "parallel" | "sequential" | "std", tasks: [TypeSignature, TaskConfiguration][], args: [Expression[], EnvironmentGenerationExpression][]) {
        super(ExpressionTag.TaskDashAnyExpression, sinfo);
        this.execmode = execmode;
        this.tasks = tasks;
        this.args = args;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const taskstrs = this.tasks.map((tt) => {
            const configs = TaskInvokeExpression.emitconfigs(tt[1], fmt);
            return `${tt[0].emit()}${configs}`;
        });

        const argl = this.args.map((arg) => {
            const envexp = arg[1].emit(fmt);
            const argexp = arg[0].map((a) => a.emit(true, fmt)).join(", ");

            return `${envexp}${argexp !== "" ? (", " + argexp) : ""}`;
        });

        return `${this.execmode !== "std" ? `${this.execmode} ` : ""}Task::dashAny<${taskstrs.join(", ")}>(${argl.join("; ")})`;
    }
}

class TaskRaceExpression extends TaskInvokeExpression {
    readonly execmode: "parallel" | "sequential" | "std";
    readonly task: TypeSignature;
    readonly configs: TaskConfiguration;
    readonly args: Expression;
    readonly envexp: EnvironmentGenerationExpression;

    constructor(sinfo: SourceInfo, execmode: "parallel" | "sequential" | "std", task: TypeSignature, args: Expression, envexp: EnvironmentGenerationExpression, configs: TaskConfiguration) {
        super(ExpressionTag.TaskRaceExpression, sinfo);
        this.execmode = execmode;
        this.task = task;
        this.configs = configs;
        this.args = args;
        this.envexp = envexp;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const configs = TaskInvokeExpression.emitconfigs(this.configs, fmt);
        const envexp = this.envexp.emit(fmt);
        const argl = this.args.emit(true, fmt);

        return `${this.execmode !== "std" ? `${this.execmode} ` : ""}Task::race<${this.task.emit()}${configs}>(${envexp}, ${argl})`;
    }
}

class TaskRaceAnyExpression extends TaskInvokeExpression {
    readonly execmode: "parallel" | "sequential" | "std";
    readonly task: TypeSignature;
    readonly configs: TaskConfiguration;
    readonly args: Expression;
    readonly envexp: EnvironmentGenerationExpression;

    constructor(sinfo: SourceInfo, execmode: "parallel" | "sequential" | "std", task: TypeSignature, args: Expression, envexp: EnvironmentGenerationExpression, configs: TaskConfiguration) {
        super(ExpressionTag.TaskRaceAnyExpression, sinfo);
        this.execmode = execmode;
        this.task = task;
        this.configs = configs;
        this.args = args;
        this.envexp = envexp;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const configs = TaskInvokeExpression.emitconfigs(this.configs, fmt);
        const envexp = this.envexp.emit(fmt);
        const argl = this.args.emit(true, fmt);

        return `${this.execmode !== "std" ? `${this.execmode} ` : ""}Task::raceAny<${this.task.emit()}${configs}>(${envexp}, ${argl})`;
    }
}

class APIInvokeExpression extends Expression {
    readonly ns: FullyQualifiedNamespace;
    readonly api: string;
    readonly args: Expression[];
    readonly configs: TaskConfiguration;
    readonly envexp: EnvironmentGenerationExpression;

    constructor(sinfo: SourceInfo, ns: FullyQualifiedNamespace, api: string, args: Expression[], envexp: EnvironmentGenerationExpression, configs: TaskConfiguration) {
        super(ExpressionTag.APIInvokeExpression, sinfo);
        this.ns = ns;
        this.api = api;
        this.args = args;
        this.envexp = envexp;
        this.configs = configs;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const nsstr = this.ns.emit() + "::";
        const configs = TaskInvokeExpression.emitconfigs(this.configs, fmt);
        const envexp = this.envexp.emit(fmt);
        const argl = this.args.map((arg) => arg.emit(true, fmt)).join(", ");

        return `api ${nsstr}${this.api}${configs}(${envexp}${argl !== "" ? (", " + argl) : ""})`;
    }
}

class AgentInvokeExpression extends Expression {
    readonly ns: FullyQualifiedNamespace;
    readonly agent: string;
    readonly optrestype: TypeSignature | undefined;
    readonly args: Expression[];
    readonly configs: TaskConfiguration;
    readonly envexp: EnvironmentGenerationExpression;

    constructor(sinfo: SourceInfo, ns: FullyQualifiedNamespace, agent: string, optrestype: TypeSignature | undefined, args: Expression[], envexp: EnvironmentGenerationExpression, configs: TaskConfiguration) {
        super(ExpressionTag.AgentInvokeExpression, sinfo);
        this.ns = ns;
        this.agent = agent;
        this.optrestype = optrestype;
        this.args = args;
        this.envexp = envexp;
        this.configs = configs;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const nsstr = this.ns.emit() + "::";
        const restypeStr = this.optrestype ? `<${this.optrestype.emit()}>` : "";
        const configs = TaskInvokeExpression.emitconfigs(this.configs, fmt);
        const envexp = this.envexp.emit(fmt);
        const argl = this.args.map((arg) => arg.emit(true, fmt)).join(", ");

        return `agent ${nsstr}${this.agent}${configs}${restypeStr}(${envexp}${argl !== "" ? (", " + argl) : ""})`;
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

    trueBinders: { gidx: number, bvname: string, tsig: TypeSignature }[] = [];

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
    
    rtype: TypeSignature | undefined = undefined;

    constructor(tag: RValueExpressionTag) {
        this.tag = tag;
    }

    abstract emit(toplevel: boolean, fmt: CodeFormatter): string;
}

class ConditionalValueExpression extends RValueExpression {
    readonly sinfo: SourceInfo;

    readonly guardset: ITestGuardSet;

    readonly trueValue: Expression
    readonly falseValue: Expression;

    trueBinders: { gidx: number, bvname: string, tsig: TypeSignature }[] = [];
    falseBinders: { gidx: number, bvname: string, tsig: TypeSignature }[] = [];

    constructor(sinfo: SourceInfo, guardset: ITestGuardSet, trueValue: Expression, falseValue: Expression) {
        super(RValueExpressionTag.ConditionalValueExpression);

        this.sinfo = sinfo;

        this.guardset = guardset;

        this.trueValue = trueValue;
        this.falseValue = falseValue;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
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

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.exp.emit(true, fmt)} @@ ${this.itest.emit(fmt)}`;
    }
}

class ShortCircuitAssignRHSExpressionReturn extends ShortCircuitAssignRHSITestExpression {
    readonly failexp: Expression | undefined;

    constructor(exp: Expression, itest: ITest, failexp: Expression | undefined) {
        super(RValueExpressionTag.ShortCircuitAssignRHSExpressionReturn, exp, itest);
        this.failexp = failexp;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        if(this.failexp === undefined) {
            return `${this.exp.emit(true, fmt)} ?@ ${this.itest.emit(fmt)}`;
        }
        else {
            return `${this.exp.emit(true, fmt)} ?@ ${this.itest.emit(fmt)} : ${this.failexp.emit(true, fmt)}`;
        }
    }
}

class BaseRValueExpression extends RValueExpression {
    readonly exp: Expression;

    constructor(exp: Expression) {
        super(RValueExpressionTag.BaseExpression);

        this.exp = exp;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.exp.emit(true, fmt);
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

    ReturnVoidStatement = "ReturnVoidStatement",
    ReturnSingleStatement = "ReturnSingleStatement",
    ReturnMultiStatement = "ReturnMultiStatement",

    IfStatement = "IfStatement",
    IfElseStatement = "IfElseStatement",
    IfElifElseStatement = "IfElifElseStatement",
    SwitchStatement = "SwitchStatement",
    MatchStatement = "MatchStatement",

    DispatchPatternStatement = "DispatchPatternStatement", //For handling regex/glob on strings!
    DispatchTaskStatement = "DispatchTaskStatement", //For handling Dash/Race return types, remember funny case of all failed -> _ where type of exp is Elist of failures

    AbortStatement = "AbortStatement",
    AssertStatement = "AssertStatement", //assert(x > 0)
    ValidateStatement = "ValidateStatement", //assert(x > 0)

    DebugStatement = "DebugStatement", //print an arg or if empty attach debugger

    VoidRefCallStatement = "VoidRefCallStatement",
    VarUpdateStatement = "VarUpdateStatement",
    ThisUpdateStatement = "ThisUpdateStatement",
    SelfUpdateStatement = "SelfUpdateStatement",

    TaskStatusStatement = "TaskStatusStatement", //do a status emit Task::emitStatusUpdate(...)
    TaskCheckAndHandleTerminationStatement = "TaskCheckAndHandleTerminationStatement", //check for termination signal and handle it appropriately
    TaskYieldStatement = "TaskYieldStatement", //result exp (probably a do but a regular expression returning APIResult is okay too)

    HoleStatement = "HoleStatement",

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

        return `${this.vkind} ${this.name}${tt} = ${this.exp.emit(true, fmt)};`;
    }
}

class VariableMultiInitializationStatement extends Statement {
    readonly vkind: "var" | "ref" | "let";
    readonly decls: {name: string, vtype: TypeSignature}[]; //maybe Auto
    actualtypes: TypeSignature[] = [];
    readonly exp: RValueExpression | Expression[]; //could be a single expression of type EList or multiple expressions

    constructor(sinfo: SourceInfo, vkind: "var" | "ref" | "let", decls: {name: string, vtype: TypeSignature}[], exp: RValueExpression | Expression[]) {
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
        return `${this.name} = ${this.exp.emit(true, fmt)};`;
    }
}

class VariableMultiAssignmentStatement extends Statement {
    readonly names: string[];
    vtypes: TypeSignature[] = [];
    readonly exp: RValueExpression | Expression[]; //could be a single expression of type EList or multiple expressions

    constructor(sinfo: SourceInfo, names: string[], exp: RValueExpression | Expression[]) {
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
        return `return ${this.value.emit(true, fmt)};`;
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
    readonly cond: ITestGuardSet;
    readonly trueBlock: BlockStatement;
    
    trueBindType: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, cond: ITestGuardSet, trueBlock: BlockStatement) {
        super(StatementTag.IfStatement, sinfo);
        this.cond = cond;
        this.trueBlock = trueBlock;
    }

    emit(fmt: CodeFormatter): string {    
        return `if ${this.cond.emit(fmt)} ${this.trueBlock.emit(fmt)}`;
    }
}

class IfElseStatement extends Statement {
    readonly cond: ITestGuardSet;
    readonly trueBlock: BlockStatement;
    readonly falseBlock: BlockStatement;

    trueBindType: TypeSignature | undefined = undefined;
    falseBindType: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, cond: ITestGuardSet, trueBlock: BlockStatement, falseBlock: BlockStatement) {
        super(StatementTag.IfElseStatement, sinfo);
        this.cond = cond;
        this.trueBlock = trueBlock;
        this.falseBlock = falseBlock;
    }

    emit(fmt: CodeFormatter): string {
        const ttif = this.trueBlock.emit(fmt);
        const ttelse = this.falseBlock.emit(fmt);

        return [`if ${this.cond.emit(fmt)} ${ttif}`, `else ${ttelse}`].join("\n");
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
    readonly sval: ITestGuard;
    readonly matchflow: {mtype: TypeSignature | undefined, value: BlockStatement}[];

    mustExhaustive: boolean = false;
    implicitFinalType: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, sval: ITestGuard, flow: {mtype: TypeSignature | undefined, value: BlockStatement}[]) {
        super(StatementTag.MatchStatement, sinfo);
        this.sval = sval;
        this.matchflow = flow;
    }

    emit(fmt: CodeFormatter): string {
        const mheader = `match${this.sval.emit(true, fmt)}`;
        fmt.indentPush();
        const ttmf = this.matchflow.map((mf) => `${mf.mtype ? mf.mtype.emit() : "_"} => ${mf.value.emit(fmt)}`);
        fmt.indentPop();

        const iir = ttmf.map((cc) => fmt.indent("| " + cc));
        return `${mheader} {\n${iir.join("\n")}\n${fmt.indent("}")}`;
    }
}

class DispatchPatternStatement extends Statement {
    readonly sval: ITestGuard;
    readonly dispatchflow: {kidx: Expression | undefined, value: BlockStatement}[];
    //always must exhaustive

    implicitFinalType: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, sval: ITestGuard, dispatchflow: {kidx: Expression | undefined, value: BlockStatement}[]) {
        super(StatementTag.DispatchPatternStatement, sinfo);
        this.sval = sval;
        this.dispatchflow = dispatchflow;
    }

    emit(fmt: CodeFormatter): string {
        const dheader = `dispatch${this.sval.emit(true, fmt)}`;
        fmt.indentPush();
        const ttdf = this.dispatchflow.map((df) => `${df.kidx ? df.kidx.emit(true, fmt) : "_"} => ${df.value.emit(fmt)}`);
        fmt.indentPop();

        const iir = ttdf.map((cc) => fmt.indent("| " + cc));
        return `${dheader} {\n${iir.join("\n")}\n${fmt.indent("}")}`;
    }
}

class DispatchTaskStatement extends Statement {
    readonly sval: ITestGuard;
    readonly dispatchflow: {kidx: string | undefined, value: BlockStatement}[];
    //always must exhaustive

    implicitFinalType: TypeSignature | undefined = undefined;

    constructor(sinfo: SourceInfo, sval: ITestGuard, dispatchflow: {kidx: string | undefined, value: BlockStatement}[]) {
        super(StatementTag.DispatchTaskStatement, sinfo);
        this.sval = sval;
        this.dispatchflow = dispatchflow;
    }

    emit(fmt: CodeFormatter): string {
        const dheader = `dispatch${this.sval.emit(true, fmt)}`;
        fmt.indentPush();
        const ttdf = this.dispatchflow.map((df) => `${df.kidx ? df.kidx : "_"} => ${df.value.emit(fmt)}`);
        fmt.indentPop();

        const iir = ttdf.map((cc) => fmt.indent("| " + cc));
        return `${dheader} {\n${iir.join("\n")}\n${fmt.indent("}")}`;
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

class HoleStatement extends Statement {
    readonly hname: string | undefined;
    readonly captures: string[];
    readonly doccomment: string | undefined;
    readonly samplesfile: Expression | undefined;
    
    readonly nvars: {name: string, tsig: TypeSignature}[];
    readonly ensures: ChkLogicExpression[];
    
    constructor(sinfo: SourceInfo, hname: string | undefined, captures: string[], doccomment: string | undefined, samplesfile: Expression | undefined, nvars: {name: string, tsig: TypeSignature}[], ensures: ChkLogicExpression[]) {
        super(StatementTag.HoleStatement, sinfo);
        this.hname = hname;
        this.captures = captures;
        this.doccomment = doccomment;
        this.samplesfile = samplesfile;

        this.nvars = nvars;
        this.ensures = ensures;
    }

    emit(fmt: CodeFormatter): string {
        let ebody = "";
        if(this.doccomment !== undefined || this.samplesfile !== undefined) {
            const dcom = this.doccomment !== undefined ? `%** ${this.doccomment} **%` : "";
            const samplstr = this.samplesfile !== undefined ? ` of ${this.samplesfile.emit(false, fmt)}` : "";
            ebody = `(${dcom})${samplstr}`;
        }

        let rbody = "";
        if(this.nvars.length === 0 || this.ensures.length === 0) {
            const nvars = this.nvars.map((nv) => `${nv.name}: ${nv.tsig.emit()}`).join(", ");
            const ensures = this.ensures.map((e) => `ensures ${e.emit(fmt)};`).join(" ");

            rbody = " ->" + (nvars !== "" ? (` [${nvars}]`) : "[]") + (ensures !== "" ? (` { ${ensures} }`) : "");
        }

        return `?_${this.hname || ""}${this.captures.length !== 0 ? ("[" + this.captures.join(", ") + "]") : ""}${ebody}${rbody}`;
    }
}

class TaskStatusStatement extends Statement {
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, exp: Expression) {
        super(StatementTag.TaskStatusStatement, sinfo);
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return `Task::emitStatusUpdate(${this.exp.emit(true, fmt)});`;
    }
}

class TaskCheckAndHandleTerminationStatement extends Statement {
    constructor(sinfo: SourceInfo) {
        super(StatementTag.TaskCheckAndHandleTerminationStatement, sinfo);
    }

    emit(fmt: CodeFormatter): string {
        return `Task::checkAndHandleTermination();`;
    }
}

class TaskYieldStatement extends Statement {
    readonly res: RValueExpression;

    constructor(sinfo: SourceInfo, res: RValueExpression) {
        super(StatementTag.TaskYieldStatement, sinfo);
        this.res = res;
    }

    emit(fmt: CodeFormatter): string {
        return `yield ${this.res.emit(true, fmt)};`;
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
        assert(headerstr === undefined);
       
        return ` = @${this.builtin};`;
    }
}

class HoleBodyImplementation extends BodyImplementation {
    readonly hname: string | undefined;
    readonly doccomment: string | undefined;
    readonly samplesfile: Expression | undefined;
    
    constructor(sinfo: SourceInfo, file: string, hname: string | undefined, doccomment: string | undefined, samplesfile: Expression | undefined) {
        super(sinfo, file);
        this.hname = hname;
        this.doccomment = doccomment;
        this.samplesfile = samplesfile;
    }

    emit(fmt: CodeFormatter, headerstr: string | undefined): string {
        let hstr = "";
        if(headerstr !== undefined) {
            hstr = " " + headerstr;
        }

        let ebody = "";
        if(this.doccomment !== undefined || this.samplesfile !== undefined) {
            const dcom = this.doccomment !== undefined ? `%** ${this.doccomment} **%` : "";
            const samplstr = this.samplesfile !== undefined ? ` of ${this.samplesfile.emit(false, fmt)}` : "";
            ebody = `(${dcom})${samplstr}`;
        }

        return hstr + `?_${this.hname || ""}${ebody}`;
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
    BinderInfo, ITest, ITestType, ITestNone, ITestSome, ITestOk, ITestFail,
    ITestGuard, ITestBinderGuard, ITestTypeGuard, ITestSimpleGuard, ITestGuardSet,
    FormatStringComponent, FormatStringTextComponent, FormatStringArgComponent,
    ArgumentValue, PositionalArgumentValue, NamedArgumentValue, SpreadArgumentValue, PassingArgumentValue, ArgumentList,
    ExpressionTag, Expression, ErrorExpression,
    LiteralNoneExpression, LiteralSimpleExpression, 
    LiteralStringExpression, LiteralCStringExpression, LiteralFormatStringExpression, LiteralFormatCStringExpression,
    LiteralRegexExpression,
    LiteralPathItemExpression, LiteralFormatPathItemExpression,
    LiteralTypeDeclValueExpression,
    LiteralTypedCStringExpression, LiteralTypedStringExpression, LiteralTypedFormatStringExpression, LiteralTypedFormatCStringExpression,
    LiteralTypedPathExpression, LiteralTypedPathFormatExpression,
    AccessEnvValueExpression, TaskAccessInfoExpression,
    AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessEnumExpression, AccessVariableExpression,
    ConstructorExpression, ConstructorPrimaryExpression, ConstructorEListExpression,
    ConstructorLambdaExpression, SpecialConstructorExpression,
    LambdaInvokeExpression,
    CallNamespaceFunctionExpression, CallTypeFunctionExpression, 
    CallRefInvokeExpression, CallRefVariableExpression, CallRefThisExpression, CallRefSelfExpression, 
    CallTaskActionExpression,
    ParseAsTypeExpression,
    InterpolateFormatExpression,
    PostfixOpTag, PostfixOperation, PostfixOp,
    PostfixError, PostfixAccessFromName, PostfixAccessFromIndex, PostfixProjectFromNames,
    PostfixIsTest, PostfixAsConvert,
    PostfixAssignFields,
    PostfixOfOperator,
    PostfixInvoke,
    UnaryExpression, PrefixNotOpExpression, PrefixNegateOrPlusOpExpression,
    BinaryArithExpression, BinAddExpression, BinSubExpression, BinMultExpression, BinDivExpression,
    BinaryKeyExpression, BinKeyEqExpression, BinKeyNeqExpression, KeyCompareEqExpression, KeyCompareLessExpression,
    BinaryNumericExpression, NumericEqExpression, NumericNeqExpression, NumericLessExpression, NumericLessEqExpression, NumericGreaterExpression, NumericGreaterEqExpression,
    LogicExpression, LogicAndExpression, LogicOrExpression,
    HoleExpression,
    MapEntryConstructorExpression,
    ChkLogicExpressionTag, ChkLogicExpression, ChkLogicImpliesExpression, ChkLogicBaseExpression,
    RValueExpressionTag, RValueExpression, ConditionalValueExpression, ShortCircuitAssignRHSITestExpression, ShortCircuitAssignRHSExpressionFail, ShortCircuitAssignRHSExpressionReturn, BaseRValueExpression,
    EnvironmentGenerationExpressionTag, EnvironmentGenerationExpression, ErrorEnvironmentExpression, EmptyEnvironmentExpression, InitializeEnvironmentExpression, CurrentEnvironmentExpression,
    TaskRunExpression, TaskMultiExpression, TaskDashExpression, TaskDashAnyExpression, TaskAllExpression, TaskRaceExpression, TaskRaceAnyExpression,
    APIInvokeExpression, AgentInvokeExpression,
    StatementTag, Statement, ErrorStatement, EmptyStatement,
    VariableDeclarationStatement, VariableMultiDeclarationStatement, VariableInitializationStatement, VariableMultiInitializationStatement, VariableAssignmentStatement, VariableMultiAssignmentStatement,
    ReturnVoidStatement, ReturnSingleStatement, ReturnMultiStatement,
    IfStatement, IfElseStatement, IfElifElseStatement, 
    SwitchStatement, MatchStatement, DispatchPatternStatement, DispatchTaskStatement,
    AbortStatement, AssertStatement, ValidateStatement, DebugStatement,
    VoidRefCallStatement, UpdateStatement, VarUpdateStatement, ThisUpdateStatement, SelfUpdateStatement,
    HoleStatement,
    TaskStatusStatement, TaskCheckAndHandleTerminationStatement,
    TaskYieldStatement,
    BlockStatement, 
    BodyImplementation, AbstractBodyImplementation, PredicateUFBodyImplementation, BuiltinBodyImplementation, HoleBodyImplementation, ExpressionBodyImplementation, StandardBodyImplementation
};
