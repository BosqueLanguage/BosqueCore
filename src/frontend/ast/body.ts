
import { RecursiveAnnotation, TypeSignature } from "./type";

import { BuildLevel, CodeFormatter, FullyQualifiedNamespace, SourceInfo } from "../build_decls";
import { LambdaDecl } from "./assembly";

abstract class ITest {
    readonly isnot: boolean;

    constructor(isnot: boolean) {
        this.isnot = isnot;
    }

    abstract emit(): string;
}

class ITestType extends ITest {
    readonly ttype: TypeSignature;
    
    constructor(isnot: boolean, ttype: TypeSignature) {
        super(isnot);
        this.ttype = ttype;
    }

    emit(): string {
        return `${this.isnot ? "!" : ""}<${this.ttype.emit()}>`;
    }
}

class ITestLiteral extends ITest {
    readonly literal: LiteralExpressionValue;
    
    constructor(isnot: boolean, literal: LiteralExpressionValue) {
        super(isnot);
        this.literal = literal;
    }

    emit(): string {
        return `${this.isnot ? "!" : ""}[${this.literal.emit(true)}]`;
    }
}

class ITestNone extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(): string {
        return `${this.isnot ? "!" : ""}none`;
    }
}

class ITestSome extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(): string {
        return `${this.isnot ? "!" : ""}some`;
    }
}

class ITestNothing extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(): string {
        return `${this.isnot ? "!" : ""}nothing`;
    }
}

class ITestSomething extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(): string {
        return `${this.isnot ? "!" : ""}something`;
    }
}

class ITestOk extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(): string {
        return `${this.isnot ? "!" : ""}ok`;
    }
}

class ITestErr extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(): string {
        return `${this.isnot ? "!" : ""}err`;
    }
}

abstract class ArgumentValue {
    readonly exp: Expression;

    constructor(exp: Expression) {
        this.exp = exp;
    }

    abstract emit(): string;
}

class PositionalArgumentValue extends ArgumentValue {
    constructor(exp: Expression) {
        super(exp);
    }

    emit(): string {
        return this.exp.emit(true);
    }
}

class NamedArgumentValue extends ArgumentValue {
    readonly name: string;

    constructor(name: string, exp: Expression) {
        super(exp);
        this.name = name;
    }

    emit(): string {
        return `${this.name} = ${this.exp.emit(true)}`;
    }
}

class SpreadArgumentValue extends ArgumentValue {
    constructor(exp: Expression) {
        super(exp);
    }

    emit(): string {
        return `...${this.exp.emit(true)}`;
    }
}

class ArgumentList {
    readonly args: ArgumentValue[];

    constructor(args: ArgumentValue[]) {
        this.args = args;
    }

    emit(lp: string, rp: string): string {
        return lp + this.args.map((arg) => arg.emit()).join(", ") + rp;
    }

    hasSpread(): boolean {
        return this.args.some((arg) => arg instanceof SpreadArgumentValue);
    }
}

enum ExpressionTag {
    Clear = "[CLEAR]",
    InvalidExpresion = "[INVALID]",

    LiteralNoneExpression = "LiteralNoneExpression",
    LiteralNothingExpression = "LiteralNothingExpression",
    LiteralBoolExpression = "LiteralBoolExpression",
    LiteralNatExpression = "LiteralNatExpression",
    LiteralIntExpression = "LiteralIntExpression",
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
    LiteralDateTimeExpression = "LiteralDateTimeExpression",
    LiteralUTCDateTimeExpression = "LiteralUTCDateTimeExpression",
    LiteralPlainDateExpression = "LiteralPlainDateExpression",
    LiteralPlainTimeExpression = "LiteralPlainTimeExpression",
    LiteralLogicalTimeExpression = "LiteralLogicalTimeExpression",
    LiteralTickTimeExpression = "LiteralTickTimeExpression",
    LiteralISOTimeStampExpression = "LiteralISOTimeStampExpression",
    LiteralDeltaDateTimeExpression = "LiteralDeltaDateTimeExpression",
    LiteralDeltaPlainDateExpression = "LiteralDeltaPlainDateExpression",
    LiteralDeltaPlainTimeExpression = "LiteralDeltaPlainTimeExpression",
    LiteralDeltaISOTimeStampExpression = "LiteralDeltaISOTimeStampExpression",
    LiteralDeltaSecondsExpression = "LiteralDeltaSecondsExpression",
    LiteralDeltaTickExpression = "LiteralDeltaTickExpression",
    LiteralDeltaLogicalExpression = "LiteralDeltaLogicalExpression",

    LiteralUnicodeRegexExpression = "LiteralUnicodeRegexExpression",
    LiteralASCIIRegexExpression = "LiteralASCIIRegexExpression",

    LiteralStringExpression = "LiteralStringExpression",
    LiteralASCIIStringExpression = "LiteralASCIIStringExpression",
    
    LiteralTypedStringExpression = "LiteralTypedStringExpression",
    LiteralASCIITypedStringExpression = "LiteralASCIITypedStringExpression",
    
    LiteralTemplateStringExpression = "LiteralTemplateStringExpression",
    LiteralASCIITemplateStringExpression = "LiteralASCIITemplateStringExpression",
    
    LiteralPathExpression = "LiteralPathExpression",
    LiteralPathFragmentExpression = "LiteralPathFragmentExpression",
    LiteralPathGlobExpression = "LiteralPathGlobExpression",

    LiteralTypeDeclValueExpression = "LiteralTypeDeclValueExpression",

    BSQONLiteralExpression = "BSQONLiteralExpression",

    StringSliceExpression = "StringSliceExpression",
    ASCIIStringSliceExpression = "ASCIIStringSliceExpression",

    HasEnvValueExpression = "HasEnvValueExpression",
    AccessEnvValueExpression = "AccessEnvValueExpression",
    TaskAccessInfoExpression = "TaskAccessInfoExpression",
    AccessNamespaceConstantExpression = "AccessNamespaceConstantExpression",
    AccessStaticFieldExpression = " AccessStaticFieldExpression",
    AccessVariableExpression = "AccessVariableExpression",

    ConstructorPrimaryExpression = "ConstructorPrimaryExpression",
    ConstructorTupleExpression = "ConstructorTupleExpression",
    ConstructorRecordExpression = "ConstructorRecordExpression",
    ConstructorEListExpression = "ConstructorEListExpression",
    ConstructorLambdaExpression = "ConstructorLambdaExpression",

    LambdaInvokeExpression = "LambdaInvokeExpression",
    SpecialConstructorExpression = "SpecialConstructorExpression",
    CallNamespaceFunctionExpression = "CallNamespaceFunctionExpression",
    CallTypeFunctionExpression = "CallTypeFunctionExpression",
    CallRefThisExpression = "CallRefThisExpression",
    
    LogicActionAndExpression = "LogicActionAndExpression",
    LogicActionOrExpression = "LogicActionOrExpression",

    PostfixOpExpression = "PostfixOpExpression",

    PrefixNotOpExpression = "PrefixNotOpExpression",
    PrefixNegateOpExpression = "PrefixNegateOpExpression",

    BinAddExpression = "BinAddExpression",
    BinSubExpression = "BinSubExpression",
    BinMultExpression = "BinMultExpression",
    BinDivExpression = "BinDivExpression",

    BinKeyEqExpression = "BinKeyEqExpression",
    BinKeyNeqExpression = "BinKeyNeqExpression",

    NumericEqExpression = "NumericEqExpression",
    NumericNeqExpression = "NumericNeqExpression",
    NumericLessExpression = "NumericLessExpression",
    NumericLessEqExpression = "NumericLessEqExpression",
    NumericGreaterExpression = "NumericGreaterExpression",
    NumericGreaterEqExpression = "NumericGreaterEqExpression",

    BinLogicAndExpression = "BinLogicAndExpression",
    BinLogicOrExpression = "BinLogicOrExpression",
    BinLogicImpliesExpression = "BinLogicImpliesExpression",
    BinLogicIFFExpression = "BinLogicIFFExpression",

    MapEntryConstructorExpression = "MapEntryConstructorExpression",

    IfExpression = "IfExpression"
}

abstract class Expression {
    readonly tag: ExpressionTag;
    readonly sinfo: SourceInfo;

    constructor(tag: ExpressionTag, sinfo: SourceInfo) {
        this.tag = tag;
        this.sinfo = sinfo;
    }

    abstract emit(toplevel: boolean): string;
}

//This just holds a constant expression that can be evaluated without any arguments but not a subtype of Expression so we can distinguish as types
class LiteralExpressionValue {
    readonly exp: Expression;

    constructor(exp: Expression) {
        this.exp = exp;
    }

    emit(toplevel: boolean): string {
        return this.exp.emit(toplevel);
    }
}

//This just holds a constant expression (for use where we expect a constant -- or restricted constant expression) but not a subtype of Expression so we can distinguish as types
class ConstantExpressionValue {
    readonly exp: Expression;
    readonly captured: Set<string>;

    constructor(exp: Expression, captured: Set<string>) {
        this.exp = exp;
        this.captured = captured;
    }

    emit(toplevel: boolean): string {
        return this.exp.emit(toplevel);
    }
}

class InvalidExpression extends Expression {
    constructor(sinfo: SourceInfo) {
        super(ExpressionTag.InvalidExpresion, sinfo);
    }

    emit(toplevel: boolean): string {
        return "[!ERROR_EXP!]";
    }
}

class LiteralSingletonExpression extends Expression {
    readonly value: string;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, value: "none" | "nothing") {
        super(tag, sinfo);

        this.value = value;
    }

    emit(toplevel: boolean): string {
        return this.value;
    }
}

class LiteralSimpleExpression extends Expression {
    readonly value: string;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, value: string) {
        super(tag, sinfo);
        this.value = value;
    }

    emit(toplevel: boolean): string {
        return this.value;
    }
}

class LiteralRegexExpression extends Expression {
    readonly value: string;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, value: string) {
        super(tag, sinfo);
        this.value = value;
    }

    emit(toplevel: boolean): string {
        return this.value;
    }
}

class LiteralTypedStringExpression extends Expression {
    readonly value: string;
    readonly stype: TypeSignature;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, value: string, stype: TypeSignature) {
        super(tag, sinfo);
        this.value = value;
        this.stype = stype;
    }

    emit(toplevel: boolean): string {
        return this.value + this.stype.emit();
    }
}

class LiteralTemplateStringExpression extends Expression {
    readonly value: string;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, value: string) {
        super(tag, sinfo);
        this.value = value;
    }

    emit(toplevel: boolean): string {
        return this.value;
    }
}

class LiteralPathExpression extends Expression {
    readonly value: string;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, value: string) {
        super(tag, sinfo);
        this.value = value;
    }

    emit(toplevel: boolean): string {
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

    emit(toplevel: boolean): string {
        return `${this.value.emit(toplevel)}_${this.constype.emit()}`;
    }
}

class BSQONLiteralExpression extends Expression {
    readonly bsqonstr: string;
    readonly bsqtype: TypeSignature;

    constructor(sinfo: SourceInfo, bsqonstr: string, bsqtype: TypeSignature) {
        super(ExpressionTag.BSQONLiteralExpression, sinfo);
        this.bsqonstr = bsqonstr;
        this.bsqtype = bsqtype;
    }

    emit(toplevel: boolean): string {
        return `bsqon<${this.bsqtype.emit()}>{| ${this.bsqonstr} |}`;
    }
}

class StringSliceExpression extends Expression {
    readonly str: Expression;
    readonly start: Expression | undefined;
    readonly end: Expression | undefined;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, str: Expression, start: Expression | undefined, end: Expression | undefined) {
        super(tag, sinfo);
        this.str = str;
        this.start = start;
        this.end = end;
    }

    emit(toplevel: boolean): string {
        return `${this.str.emit(toplevel)}[${this.start ? this.start.emit(toplevel) : ""}:${this.end ? this.end.emit(toplevel) : ""}]`;
    }
}

class AccessEnvValueExpression extends Expression {
    readonly keyname: string;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, keyname: string) {
        super(tag, sinfo);
        this.keyname = keyname;
    }

    emit(toplevel: boolean): string {
        return `env${this.tag === ExpressionTag.HasEnvValueExpression ? "?" : ""}[${this.keyname}]`;
    }
}

class TaskAccessInfoExpression extends Expression {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string) {
        super(ExpressionTag.TaskAccessInfoExpression, sinfo);
        this.name = name;
    }

    emit(toplevel: boolean): string {
        return `Task::${this.name}()`;
    }
}

class AccessNamespaceConstantExpression extends Expression {
    readonly ns: FullyQualifiedNamespace;
    readonly name: string;

    constructor(sinfo: SourceInfo, ns: FullyQualifiedNamespace, name: string) {
        super(ExpressionTag.AccessNamespaceConstantExpression, sinfo);
        this.ns = ns;
        this.name = name;
    }

    emit(toplevel: boolean): string {
        return `${this.ns}::${this.name}`;
    }
}

class AccessStaticFieldExpression extends Expression {
    readonly stype: TypeSignature;
    readonly name: string;

    constructor(sinfo: SourceInfo, stype: TypeSignature, name: string) {
        super(ExpressionTag.AccessStaticFieldExpression, sinfo);
        this.stype = stype;
        this.name = name;
    }

    emit(toplevel: boolean): string {
        return `${this.stype.emit()}::${this.name}`;
    }
}

class AccessVariableExpression extends Expression {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string) {
        super(ExpressionTag.AccessVariableExpression, sinfo);
        this.name = name;
    }

    emit(toplevel: boolean): string {
        return this.name;
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
    readonly ctype: TypeSignature;

    constructor(sinfo: SourceInfo, ctype: TypeSignature, args: ArgumentList) {
        super(ExpressionTag.ConstructorPrimaryExpression, sinfo, args);
        this.ctype = ctype;
    }

    emit(toplevel: boolean): string {
        return `${this.ctype.emit()}${this.args.emit("{", "}")}`;
    }
}

class ConstructorTupleExpression extends ConstructorExpression {
    constructor(sinfo: SourceInfo, args: ArgumentList) {
        super(ExpressionTag.ConstructorTupleExpression, sinfo, args);
    }

    emit(toplevel: boolean): string {
        return this.args.emit("[", "]");
    }
}

class ConstructorRecordExpression extends ConstructorExpression {
    constructor(sinfo: SourceInfo, args: ArgumentList) {
        super(ExpressionTag.ConstructorRecordExpression, sinfo, args);
    }

    emit(toplevel: boolean): string {
        return this.args.emit("{", "}");
    }
}

class ConstructorEListExpression extends ConstructorExpression {
    constructor(sinfo: SourceInfo, args: ArgumentList) {
        super(ExpressionTag.ConstructorEListExpression, sinfo, args);
    }

    emit(toplevel: boolean): string {
        return this.args.emit("(", ")");
    }
}

class ConstructorLambdaExpression extends Expression {
    readonly isAuto: boolean;
    readonly invoke: LambdaDecl;

    constructor(sinfo: SourceInfo, isAuto: boolean, invoke: LambdaDecl) {
        super(ExpressionTag.ConstructorLambdaExpression, sinfo);
        this.isAuto = isAuto;
        this.invoke = invoke;
    }

    emit(toplevel: boolean): string {
        return this.invoke.emitInlineLambda();
    }
}

class SpecialConstructorExpression extends Expression {
    readonly rop: "ok" | "err" | "something" | "result";
    readonly arg: Expression;

    constructor(sinfo: SourceInfo, rop: "ok" | "err" | "something" | "result", arg: Expression) {
        super(ExpressionTag.SpecialConstructorExpression, sinfo);
        this.rop = rop;
        this.arg = arg;
    }

    emit(toplevel: boolean): string {
        return `${this.rop}(${this.arg.emit(toplevel)})`;
    }
}

class LambdaInvokeExpression extends Expression {
    readonly name: string;
    readonly rec: RecursiveAnnotation;
    readonly args: ArgumentList;

    constructor(sinfo: SourceInfo, name: string, rec: RecursiveAnnotation, args: ArgumentList) {
        super(ExpressionTag.LambdaInvokeExpression, sinfo);
        this.name = name;
        this.rec = rec;
        this.args = args;
    }

    emit(toplevel: boolean): string {
        let rec = "";
        if(this.rec !== "no") {
            rec = "[" + (this.rec === "yes" ? "recursive" : "recursive?") + "]";
        }
        
        return `${this.name}${rec}${this.args.emit("(", ")")}`;
    }
}

class CallNamespaceFunctionExpression extends Expression {
    readonly ns: FullyQualifiedNamespace;
    readonly name: string;
    readonly rec: RecursiveAnnotation;
    readonly terms: TypeSignature[];
    readonly args: ArgumentList;

    constructor(sinfo: SourceInfo, ns: FullyQualifiedNamespace, name: string, terms: TypeSignature[], rec: RecursiveAnnotation, args: ArgumentList) {
        super(ExpressionTag.CallNamespaceFunctionExpression, sinfo);
        this.ns = ns;
        this.name = name;
        this.rec = rec;
        this.terms = terms;
        this.args = args;
    }

    emit(toplevel: boolean): string {
        let rec = "";
        if(this.rec !== "no") {
            rec = "[" + (this.rec === "yes" ? "recursive" : "recursive?") + "]";
        }
        
        let terms = "";
        if(this.terms.length !== 0) {
            terms = "<" + this.terms.map((tt) => tt.emit()).join(", ") + ">";
        }

        return `${this.ns}::${this.name}${rec}${terms}${this.args.emit("(", ")")}`;
    }
}

class CallTypeFunctionExpression extends Expression {
    readonly ttype: TypeSignature;
    readonly name: string;
    readonly rec: RecursiveAnnotation;
    readonly terms: TypeSignature[];
    readonly args: ArgumentList;

    constructor(sinfo: SourceInfo, ttype: TypeSignature, name: string, terms: TypeSignature[], rec: RecursiveAnnotation, args: ArgumentList) {
        super(ExpressionTag.CallTypeFunctionExpression, sinfo);
        this.ttype = ttype;
        this.name = name;
        this.rec = rec;
        this.terms = terms;
        this.args = args;
    }

    emit(toplevel: boolean): string {
        let rec = "";
        if(this.rec !== "no") {
            rec = "[" + (this.rec === "yes" ? "recursive" : "recursive?") + "]";
        }
        
        let terms = "";
        if(this.terms.length !== 0) {
            terms = "<" + this.terms.map((tt) => tt.emit()).join(", ") + ">";
        }

        return `${this.ttype.emit()}::${this.name}${rec}${terms}${this.args.emit("(", ")")}`;
    }
}

class CallRefThisExpression extends Expression {
    xxxx; //should also have special cases for this update and self update

    readonly name: string;
    readonly rec: RecursiveAnnotation;
    readonly terms: TypeSignature[];
    readonly args: ArgumentList;

    constructor(sinfo: SourceInfo, name: string, terms: TypeSignature[], rec: RecursiveAnnotation, args: ArgumentList) {
        super(ExpressionTag.CallRefThisExpression, sinfo);
        this.name = name;
        this.rec = rec;
        this.terms = terms;
        this.args = args;
    }

    emit(toplevel: boolean): string {
        let rec = "";
        if(this.rec !== "no") {
            rec = "[" + (this.rec === "yes" ? "recursive" : "recursive?") + "]";
        }
        
        let terms = "";
        if(this.terms.length !== 0) {
            terms = "<" + this.terms.map((tt) => tt.emit()).join(", ") + ">";
        }

        return `ref this.${this.name}${rec}${terms}${this.args.emit("(", ")")}`;
    }
}

class LogicActionAndExpression extends Expression {
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, args: Expression[]) {
        super(ExpressionTag.LogicActionAndExpression, sinfo);
        this.args = args;
    }

    emit(toplevel: boolean): string {
        return `/\\(${this.args.map((arg) => arg.emit(toplevel)).join(", ")})`;
    }
}

class LogicActionOrExpression extends Expression {
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, args: Expression[]) {
        super(ExpressionTag.LogicActionOrExpression, sinfo);
        this.args = args;
    }

    emit(toplevel: boolean): string {
        return `\\/(${this.args.map((arg) => arg.emit(toplevel)).join(", ")})`;
    }
}

enum PostfixOpTag {
    PostfixAccessFromIndex = "PostfixAccessFromIndex",
    PostfixProjectFromIndecies = "PostfixProjectFromIndecies",
    PostfixAccessFromName = "PostfixAccessFromName",
    PostfixProjectFromNames = "PostfixProjectFromNames",

    PostfixIsTest = "PostfixIsTest",
    PostfixAsConvert = "PostfixAsConvert",

    PostfixAssignFields = "PostfixAssignFields",

    PostfixInvoke = "PostfixInvoke"
}

abstract class PostfixOperation {
    readonly sinfo: SourceInfo;
    readonly op: PostfixOpTag;

    constructor(sinfo: SourceInfo, op: PostfixOpTag) {
        this.sinfo = sinfo;
        this.op = op;
    }

    abstract emit(): string;
}

class PostfixOp extends Expression {
    readonly rootExp: Expression;
    readonly ops: PostfixOperation[];

    constructor(sinfo: SourceInfo, root: Expression, ops: PostfixOperation[]) {
        super(ExpressionTag.PostfixOpExpression, sinfo);
        this.rootExp = root;
        this.ops = ops;
    }

    emit(toplevel: boolean): string {
        let res = this.rootExp.emit(false);
        for(let i = 0; i < this.ops.length; ++i) {
            res += this.ops[i].emit();
        }

        return res;
    }
}

class PostfixAccessFromIndex extends PostfixOperation {
    readonly index: number;

    constructor(sinfo: SourceInfo, index: number) {
        super(sinfo, PostfixOpTag.PostfixAccessFromIndex);
        this.index = index;
    }

    emit(): string {
        return `.${this.index}`;
    }
}

class PostfixProjectFromIndecies extends PostfixOperation {
    readonly indecies: number[];

    constructor(sinfo: SourceInfo, indecies: number[]) {
        super(sinfo, PostfixOpTag.PostfixProjectFromIndecies);
        this.indecies = indecies;
    }

    emit(): string {
        return `.(${this.indecies.join(", ")})`;
    }
}

class PostfixAccessFromName extends PostfixOperation {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string) {
        super(sinfo, PostfixOpTag.PostfixAccessFromName);
        this.name = name;
    }

    emit(): string {
        return `.${this.name}`;
    }
}

class PostfixProjectFromNames extends PostfixOperation {
    readonly names: string[];

    constructor(sinfo: SourceInfo, names: string[]) {
        super(sinfo, PostfixOpTag.PostfixProjectFromNames);
        this.names = names;
    }

    emit(): string {
        return `.(${this.names.join(", ")})`;
    }
}

class PostfixIsTest extends PostfixOperation {
    readonly ttest: ITest;

    constructor(sinfo: SourceInfo, ttest: ITest) {
        super(sinfo, PostfixOpTag.PostfixIsTest);
        this.ttest = ttest;
    }

    emit(): string {
        return "?" + this.ttest.emit();
    }
}

class PostfixAsConvert extends PostfixOperation {
    readonly ttest: ITest;

    constructor(sinfo: SourceInfo, ttest: ITest) {
        super(sinfo, PostfixOpTag.PostfixAsConvert);
        this.ttest = ttest;
    }

    emit(): string {
        return "!" + this.ttest.emit();
    }
}

class PostfixAssignFields extends PostfixOperation {
    readonly updates: ArgumentList;

    constructor(sinfo: SourceInfo, updates: ArgumentList) {
        super(sinfo, PostfixOpTag.PostfixAssignFields);
        this.updates = updates;
    }

    emit(): string {
        return `.${this.updates.emit("[", "]")}`;
    }
}

class PostfixInvoke extends PostfixOperation {
    readonly specificResolve: TypeSignature | undefined;
    readonly name: string;
    readonly rec: RecursiveAnnotation;
    readonly terms: TypeSignature[];
    readonly args: ArgumentList;

    constructor(sinfo: SourceInfo, specificResolve: TypeSignature | undefined, name: string, terms: TypeSignature[], rec: RecursiveAnnotation, args: ArgumentList) {
        super(sinfo, PostfixOpTag.PostfixInvoke);
        this.specificResolve = specificResolve;
        this.name = name;
        this.rec = rec;
        this.terms = terms;
        this.args = args;
    }

    emit(): string {
        let rec = "";
        if(this.rec !== "no") {
            rec = "[" + (this.rec === "yes" ? "recursive" : "recursive?") + "]";
        }

        return `${this.specificResolve ? this.specificResolve.emit() + "::" : ""}${this.name}${rec}${this.args.emit("(", ")")})`;
    }
}

abstract class UnaryExpression extends Expression {
    readonly exp: Expression;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, exp: Expression) {
        super(tag, sinfo);
        this.exp = exp;
    }

    uopEmit(toplevel: boolean, op: string): string {
        const ee = `${op}${this.exp.emit(false)}`;
        return toplevel ? ee : `(${ee})`;
    }
}

class PrefixNotOp extends UnaryExpression {
    constructor(sinfo: SourceInfo, exp: Expression) {
        super(ExpressionTag.PrefixNotOpExpression, sinfo, exp);
    }

    emit(toplevel: boolean): string {
        return this.uopEmit(toplevel, "!");
    }
}

class PrefixNegateOp extends UnaryExpression {
    constructor(sinfo: SourceInfo, exp: Expression) {
        super(ExpressionTag.PrefixNegateOpExpression, sinfo, exp);
    }

    emit(toplevel: boolean): string {
        return this.uopEmit(toplevel, "-");
    }
}

abstract class BinaryArithExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(tag, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }

    baopEmit(toplevel: boolean, op: string): string {
        const ee = `${this.lhs.emit(false)} ${op} ${this.rhs.emit(false)}`;
        return toplevel ? ee : `(${ee})`;
    }
}

class BinAddExpression extends BinaryArithExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinAddExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean): string {
        return this.baopEmit(toplevel, "+");
    }
}

class BinSubExpression extends BinaryArithExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinSubExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean): string {
        return this.baopEmit(toplevel, "-");
    }
}

class BinMultExpression extends BinaryArithExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinMultExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean): string {
        return this.baopEmit(toplevel, "*");
    }
}

class BinDivExpression extends BinaryArithExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinDivExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean): string {
        return this.baopEmit(toplevel, "//");
    }
}

abstract class BinaryKeyExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(tag, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }

    bkopEmit(toplevel: boolean, op: string): string {
        const ee = `${this.lhs.emit(false)} ${op} ${this.rhs.emit(false)}`;
        return toplevel ? ee : `(${ee})`;
    }
}

class BinKeyEqExpression extends BinaryKeyExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinKeyEqExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean): string {
        return this.bkopEmit(toplevel, "===");
    }
}

class BinKeyNeqExpression extends BinaryKeyExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinKeyNeqExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean): string {
        return this.bkopEmit(toplevel, "!==");
    }
}

abstract class BinaryNumericExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(tag, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }

    bnopEmit(toplevel: boolean, op: string): string {
        const ee = `${this.lhs.emit(false)} ${op} ${this.rhs.emit(false)}`;
        return toplevel ? ee : `(${ee})`;
    }
}

class NumericEqExpression extends BinaryNumericExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericEqExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean): string {
        return this.bnopEmit(toplevel, "==");
    }
}

class NumericNeqExpression extends BinaryNumericExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericNeqExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean): string {
        return this.bnopEmit(toplevel, "!=");
    }
}

class NumericLessExpression extends BinaryNumericExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericLessExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean): string {
        return this.bnopEmit(toplevel, "<");
    }
}

class NumericLessEqExpression extends BinaryNumericExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericLessEqExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean): string {
        return this.bnopEmit(toplevel, "<=");
    }
}

class NumericGreaterExpression extends BinaryNumericExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericGreaterExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean): string {
        return this.bnopEmit(toplevel, ">");
    }
}

class NumericGreaterEqExpression extends BinaryNumericExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericGreaterEqExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean): string {
        return this.bnopEmit(toplevel, ">=");
    }
}

abstract class BinLogicExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(tag, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }

    blopEmit(toplevel: boolean, op: string): string {
        const ee = `${this.lhs.emit(false)} ${op} ${this.rhs.emit(false)}`;
        return toplevel ? ee : `(${ee})`;
    }
}

class BinLogicAndxpression extends BinLogicExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinLogicAndExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean): string {
        return this.blopEmit(toplevel, "&&");
    }
}

class BinLogicOrExpression extends BinLogicExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinLogicOrExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean): string {
        return this.blopEmit(toplevel, "||");
    }
}

class BinLogicImpliesExpression extends BinLogicExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinLogicImpliesExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean): string {
        return this.blopEmit(toplevel, "==>");
    }
}

class BinLogicIFFExpression extends BinLogicExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinLogicIFFExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean): string {
        return this.blopEmit(toplevel, "<==>");
    }
}

class MapEntryConstructorExpression extends Expression {
    readonly kexp: Expression;
    readonly vexp: Expression;

    constructor(sinfo: SourceInfo, kexp: Expression, vexp: Expression) {
        super(ExpressionTag.MapEntryConstructorExpression, sinfo);
        this.kexp = kexp;
        this.vexp = vexp;
    }

    emit(toplevel: boolean): string {
        return `${this.kexp.emit(toplevel)} => ${this.vexp.emit(toplevel)}`;
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
    readonly trueValue: Expression
    readonly trueValueBinder: string | undefined;
    readonly falseValue: Expression;
    readonly falseValueBinder: string | undefined;

    constructor(sinfo: SourceInfo, test: IfTest, trueValue: Expression, trueValueBinder: string | undefined, falseValue: Expression, falseValueBinder: string | undefined) {
        super(ExpressionTag.IfExpression, sinfo);
        this.test = test;
        this.trueValue = trueValue;
        this.trueValueBinder = trueValueBinder;
        this.falseValue = falseValue;
        this.falseValueBinder = falseValueBinder;
    }

    emit(toplevel: boolean): string {
        const ttest = (this.test.itestopt !== undefined ? this.test.itestopt.emit() : "") + `(${this.test.exp.emit(true)})`;
        return `if ${ttest} then ${this.trueValue.emit(true)} else ${this.falseValue.emit(true)}`;
    }
}

enum EnvironmentGenerationExpressionTag {

}

abstract class EnvironmentGenerationExpression {

}

abstract class BaseEnvironmentOpExpression extends EnvironmentGenerationExpression {

}

class EmptyEnvironmentExpression extends BaseEnvironmentOpExpression {

}

class InitializeEnvironmentExpression extends BaseEnvironmentOpExpression {

}

class CurrentEnvironmentExpression extends BaseEnvironmentOpExpression {

}

enum PostfixEnvironmentOpTag {

}

abstract class PostfixEnvironmentOp {

}

class PostFixEnvironmentOpProject extends PostfixEnvironmentOp {

}

class PostfixEnvironmentOpSet extends PostfixEnvironmentOp {

}

class PostfixEnvironmentOpExpression extends EnvironmentGenerationExpression {
    readonly baseenv: BaseEnvironmentOpExpression;
    readonly ops: PostfixEnvironmentOp[];
}


enum StatementTag {
    Clear = "[CLEAR]",
    InvalidStatement = "[INVALID]",

    EmptyStatement = "EmptyStatement",

    VariableDeclarationStatement = "VariableDeclarationStatement",
    VariableAssignmentStatement = "VariableAssignmentStatement",

    VariableRetypeStatement = "VariableRetypeStatement",
    ReturnStatement = "ReturnStatement",

    IfElseStatement = "IfElseStatement",
    SwitchStatement = "SwitchStatement",
    MatchStatement = "MatchStatement",

    AbortStatement = "AbortStatement",
    AssertStatement = "AssertStatement", //assert(x > 0)

    DebugStatement = "DebugStatement", //print an arg or if empty attach debugger

    StandaloneExpressionStatement = "StandaloneExpressionStatement",

    EnvironmentStatement = "EnvironmentStatement",
    EnvironmentBracketStatement = "EnvironmentBracketStatement",

    TaskRunStatement = "TaskRunStatement", //run single task
    TaskMultiStatement = "TaskMultiStatement", //run multiple explicitly identified tasks -- complete all
    TaskDashStatement = "TaskDashStatement", //run multiple explicitly identified tasks -- first completion wins
    TaskAllStatement = "TaskAllStatement", //run the same task on all args in a list -- complete all
    TaskRaceStatement = "TaskRaceStatement", //run the same task on all args in a list -- first completion wins

    TaskStatusStatement = "TaskStatusStatement", //do a status emit Task::emitStatusUpdate(...)
    TaskEventEmitStatement = "TaskEventEmitStatement" //Task::event(...)
}

abstract class Statement {
    readonly tag: StatementTag;
    readonly sinfo: SourceInfo;

    constructor(tag: StatementTag, sinfo: SourceInfo) {
        this.tag = tag;
        this.sinfo = sinfo;
    }

    isTaskOperation(): boolean {
        return false;
    }
}

class InvalidStatement extends Statement {
    constructor(sinfo: SourceInfo) {
        super(StatementTag.InvalidStatement, sinfo);
    }
}

class EmptyStatement extends Statement {
    constructor(sinfo: SourceInfo) {
        super(StatementTag.EmptyStatement, sinfo);
    }
}

class VariableDeclarationStatement extends Statement {
    readonly name: string;
    readonly isConst: boolean;
    readonly vtype: TypeSignature; //may be auto
    readonly exp: Expression | undefined; //may be undef
    readonly scinfo: {sctest: ITest | Expression, scaction: Expression | undefined, binderinfo: string | undefined} | undefined;

    constructor(sinfo: SourceInfo, name: string, isConst: boolean, vtype: TypeSignature, exp: Expression | undefined, scinfo: {sctest: ITest | Expression, scaction: Expression | undefined, binderinfo: string | undefined} | undefined) {
        super(StatementTag.VariableDeclarationStatement, sinfo);
        this.name = name;
        this.isConst = isConst;
        this.vtype = vtype;
        this.exp = exp;
        this.scinfo = scinfo;
    }
}

class VariableAssignmentStatement extends Statement {
    readonly name: string;
    readonly exp: Expression;
    readonly scinfo: {sctest: ITest | Expression, scaction: Expression | undefined, binderinfo: string | undefined} | undefined;

    constructor(sinfo: SourceInfo, name: string, exp: Expression, scinfo: {sctest: ITest | Expression, scaction: Expression | undefined, binderinfo: string | undefined} | undefined) {
        super(StatementTag.VariableAssignmentStatement, sinfo);
        this.name = name;
        this.exp = exp;
        this.scinfo = scinfo;
    }
}

class VariableRetypeStatement extends Statement {
    readonly name: string;
    readonly ttest: ITest;

    constructor(sinfo: SourceInfo, name: string, ttest: ITest) {
        super(StatementTag.VariableRetypeStatement, sinfo);
        this.name = name;
        this.ttest = ttest;
    }
}

class ExpressionSCReturnStatement extends Statement {
    readonly exp: Expression;
    readonly ttest: ITest | Expression;
    readonly res: Expression | undefined;
    readonly binderinfo: string | undefined;

    constructor(sinfo: SourceInfo, exp: Expression, ttest: ITest | Expression, res: Expression | undefined, binderinfo: string | undefined) {
        super(StatementTag.ExpressionSCReturnStatement, sinfo);
        this.exp = exp;
        this.ttest = ttest;
        this.res = res;
        this.binderinfo = binderinfo;
    }
}

class VariableSCRetypeStatement extends Statement {
    readonly name: string;
    readonly ttest: ITest;
    readonly res: Expression | undefined;
    readonly binderinfo: string | undefined;

    constructor(sinfo: SourceInfo, name: string, ttest: ITest, res: Expression | undefined, binderinfo: string | undefined) {
        super(StatementTag.VariableSCRetypeStatement, sinfo);
        this.name = name;
        this.ttest = ttest;
        this.res = res;
        this.binderinfo = binderinfo;
    }
}

class ReturnStatement extends Statement {
    readonly value: Expression;

    constructor(sinfo: SourceInfo, value: Expression) {
        super(StatementTag.ReturnStatement, sinfo);
        this.value = value;
    }
}

class IfStatement extends Statement {
    readonly condflow: {cond: IfTest, value: ScopedBlockStatement, binderinfo: string | undefined}[];
    readonly elseflow: {value: ScopedBlockStatement, binderinfo: string | undefined} | undefined;

    constructor(sinfo: SourceInfo, condflow: {cond: IfTest, value: ScopedBlockStatement, binderinfo: string | undefined}[], elseflow: {value: ScopedBlockStatement, binderinfo: string | undefined} | undefined) {
        super(StatementTag.IfElseStatement, sinfo);
        this.condflow = condflow;
        this.elseflow = elseflow;
    }
}

class SwitchStatement extends Statement {
    readonly sval: Expression;
    readonly switchflow: {condlit: LiteralExpressionValue | undefined, value: ScopedBlockStatement, binderinfo: string | undefined}[];

    constructor(sinfo: SourceInfo, sval: Expression, switchflow: {condlit: LiteralExpressionValue | undefined, value: ScopedBlockStatement, binderinfo: string | undefined}[]) {
        super(StatementTag.SwitchStatement, sinfo);
        this.sval = sval;
        this.switchflow = switchflow;
    }
}

class MatchStatement extends Statement {
    readonly sval: Expression;
    readonly matchflow: {mtype: TypeSignature | undefined, value: ScopedBlockStatement, binderinfo: string | undefined}[];

    constructor(sinfo: SourceInfo, sval: Expression, flow: {mtype: TypeSignature | undefined, value: ScopedBlockStatement, binderinfo: string | undefined}[]) {
        super(StatementTag.MatchStatement, sinfo);
        this.sval = sval;
        this.matchflow = flow;
    }
}

class AbortStatement extends Statement {
    constructor(sinfo: SourceInfo) {
        super(StatementTag.AbortStatement, sinfo);
    }
}

class AssertStatement extends Statement {
    readonly cond: Expression;
    readonly level: BuildLevel;

    constructor(sinfo: SourceInfo, cond: Expression, level: BuildLevel) {
        super(StatementTag.AssertStatement, sinfo);
        this.cond = cond;
        this.level = level;
    }
}

class DebugStatement extends Statement {
    readonly value: Expression;

    constructor(sinfo: SourceInfo, value: Expression) {
        super(StatementTag.DebugStatement, sinfo);
        this.value = value;
    }
}

class RefCallStatement extends Statement {
    readonly call: PostfixOp | TaskSelfActionExpression;
    readonly optscinfo: {sctest: ITest | Expression, scaction: Expression | undefined} | undefined;

    constructor(sinfo: SourceInfo, call: PostfixOp | TaskSelfActionExpression, optscinfo: {sctest: ITest | Expression, scaction: Expression | undefined} | undefined) {
        super(StatementTag.RefCallStatement, sinfo);
        this.call = call;
        this.optscinfo = optscinfo;
    }
}

class EnvironmentFreshStatement extends Statement {
    readonly assigns: {keyname: string, valexp: [TypeSignature, Expression] | undefined}[];

    constructor(sinfo: SourceInfo, assigns: {keyname: string, valexp: [TypeSignature, Expression] | undefined}[]) {
        super(StatementTag.EnvironmentFreshStatement, sinfo);
        this.assigns = assigns;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class EnvironmentSetStatement extends Statement {
    readonly assigns: {keyname: string, valexp: [TypeSignature, Expression] | undefined}[];

    constructor(sinfo: SourceInfo, assigns: {keyname: string, valexp: [TypeSignature, Expression] | undefined}[]) {
        super(StatementTag.EnvironmentSetStatement, sinfo);
        this.assigns = assigns;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class EnvironmentSetStatementBracket extends Statement {
    readonly assigns: {keyname: string, valexp: [TypeSignature, Expression] | undefined}[];
    readonly block: UnscopedBlockStatement | ScopedBlockStatement;
    readonly isFresh: boolean;

    constructor(sinfo: SourceInfo, assigns: {keyname: string, valexp: [TypeSignature, Expression] | undefined}[], block: UnscopedBlockStatement | ScopedBlockStatement, isFresh: boolean) {
        super(StatementTag.EnvironmentSetStatementBracket, sinfo);
        this.assigns = assigns;
        this.block = block;
        this.isFresh = isFresh;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class TaskRunStatement extends Statement {
    readonly isdefine: boolean;
    readonly isconst: boolean;
    readonly vtrgt: {name: string, vtype: TypeSignature};
    readonly task: TypeSignature;
    readonly taskargs: {argn: string, argv: Expression}[];
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, isdefine: boolean, isconst: boolean, vtrgt: {name: string, vtype: TypeSignature}, task: TypeSignature, taskargs: {argn: string, argv: Expression}[], args: Expression[]) {
        super(StatementTag.TaskRunStatement, sinfo);
        this.isdefine = isdefine;
        this.isconst = isconst;
        this.vtrgt = vtrgt;
        this.task = task;
        this.taskargs = taskargs;
        this.args = args;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class TaskMultiStatement extends Statement {
    readonly isdefine: boolean;
    readonly isconst: boolean;
    readonly vtrgts: {name: string, vtype: TypeSignature}[];
    readonly tasks: TypeSignature[];
    readonly taskargs: {argn: string, argv: Expression}[];
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, isdefine: boolean, isconst: boolean, vtrgts: {name: string, vtype: TypeSignature}[], tasks: TypeSignature[], taskargs: {argn: string, argv: Expression}[], args: Expression[]) {
        super(StatementTag.TaskMultiStatement, sinfo);
        this.isdefine = isdefine;
        this.isconst = isconst;
        this.vtrgts = vtrgts;
        this.tasks = tasks;
        this.taskargs = taskargs;
        this.args = args;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class TaskDashStatement extends Statement {
    readonly isdefine: boolean;
    readonly isconst: boolean;
    readonly vtrgts: {name: string, vtype: TypeSignature}[];
    readonly tasks: TypeSignature[];
    readonly taskargs: {argn: string, argv: Expression}[];
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, isdefine: boolean, isconst: boolean, vtrgts: {name: string, vtype: TypeSignature}[], tasks: TypeSignature[], taskargs: {argn: string, argv: Expression}[], args: Expression[]) {
        super(StatementTag.TaskDashStatement, sinfo);
        this.isdefine = isdefine;
        this.isconst = isconst;
        this.vtrgts = vtrgts;
        this.tasks = tasks;
        this.taskargs = taskargs;
        this.args = args;
    }

    isTaskOperation(): boolean {
        return true;
    }
}


class TaskAllStatement extends Statement {
    readonly isdefine: boolean;
    readonly isconst: boolean;
    readonly vtrgt: {name: string, vtype: TypeSignature};
    readonly task: TypeSignature;
    readonly taskargs: {argn: string, argv: Expression}[];
    readonly arg: Expression;

    constructor(sinfo: SourceInfo, isdefine: boolean, isconst: boolean, vtrgt: {name: string, vtype: TypeSignature}, task: TypeSignature, taskargs: {argn: string, argv: Expression}[], arg: Expression) {
        super(StatementTag.TaskAllStatement, sinfo);
        this.isdefine = isdefine;
        this.isconst = isconst;
        this.vtrgt = vtrgt;
        this.task = task;
        this.taskargs = taskargs;
        this.arg = arg;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class TaskRaceStatement extends Statement {
    readonly isdefine: boolean;
    readonly isconst: boolean;
    readonly vtrgt: {name: string, vtype: TypeSignature};
    readonly task: TypeSignature;
    readonly taskargs: {argn: string, argv: Expression}[];
    readonly arg: Expression;

    constructor(sinfo: SourceInfo, isdefine: boolean, isconst: boolean, vtrgt: {name: string, vtype: TypeSignature}, task: TypeSignature, taskargs: {argn: string, argv: Expression}[], arg: Expression) {
        super(StatementTag.TaskRaceStatement, sinfo);
        this.isdefine = isdefine;
        this.isconst = isconst;
        this.vtrgt = vtrgt;
        this.task = task;
        this.taskargs = taskargs;
        this.arg = arg;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class TaskCallWithStatement extends Statement {
    readonly name: string;
    readonly terms: TypeSignature[];
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, name: string, terms: TypeSignature[], args: Expression[]) {
        super(StatementTag.TaskCallWithStatement, sinfo);
        this.name = name;
        this.terms = terms;
        this.args = args;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class TaskResultWithStatement extends Statement {
    readonly name: string;
    readonly terms: TypeSignature[];
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, name: string, terms: TypeSignature[], args: Expression[]) {
        super(StatementTag.TaskResultWithStatement, sinfo);
        this.name = name;
        this.terms = terms;
        this.args = args;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class TaskSetStatusStatement extends Statement {
    readonly arg: Expression;

    constructor(sinfo: SourceInfo, arg: Expression) {
        super(StatementTag.TaskSetStatusStatement, sinfo);
        this.arg = arg;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class TaskSetSelfFieldStatement extends Statement {
    readonly fname: string;
    readonly value: Expression;

    constructor(sinfo: SourceInfo, fname: string, value: Expression) {
        super(StatementTag.TaskSetSelfFieldStatement, sinfo);
        this.fname = fname;
        this.value = value;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class TaskEventEmitStatement extends Statement {
    readonly arg: Expression;

    constructor(sinfo: SourceInfo, arg: Expression) {
        super(StatementTag.TaskEventEmitStatement, sinfo);
        this.arg = arg;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class LoggerEmitStatement extends Statement {
    readonly level: LoggerLevel;
    readonly msg: AccessFormatInfoExpression;
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, level: LoggerLevel, msg: AccessFormatInfoExpression, args: Expression[]) {
        super(StatementTag.LoggerEmitStatement, sinfo);
        this.level = level;
        this.msg = msg;
        this.args = args;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class LoggerEmitConditionalStatement extends Statement {
    readonly level: LoggerLevel;
    readonly cond: Expression;
    readonly msg: AccessFormatInfoExpression;
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, level: LoggerLevel, cond: Expression, msg: AccessFormatInfoExpression, args: Expression[]) {
        super(StatementTag.LoggerEmitConditionalStatement, sinfo);
        this.level = level;
        this.cond = cond;
        this.msg = msg;
        this.args = args;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class LoggerLevelStatement extends Statement {
    readonly levels: {lname: string, lvalue: Expression}[];
    readonly block: UnscopedBlockStatement | ScopedBlockStatement;

    constructor(sinfo: SourceInfo, levels: {lname: string, lvalue: Expression}[], block: UnscopedBlockStatement | ScopedBlockStatement) {
        super(StatementTag.LoggerLevelStatement, sinfo);
        this.levels = levels;
        this.block = block;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class LoggerCategoryStatement extends Statement {
    readonly categories: {cname: string, cvalue: Expression}[];
    readonly block: UnscopedBlockStatement | ScopedBlockStatement;

    constructor(sinfo: SourceInfo, categories: {cname: string, cvalue: Expression}[], block: UnscopedBlockStatement | ScopedBlockStatement) {
        super(StatementTag.LoggerCategoryStatement, sinfo);
        this.categories = categories;
        this.block = block;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class LoggerPrefixStatement extends Statement {
    readonly msg: AccessFormatInfoExpression;
    readonly args: Expression[];
    readonly block: UnscopedBlockStatement | ScopedBlockStatement;

    constructor(sinfo: SourceInfo, msg: AccessFormatInfoExpression, args: Expression[], block: UnscopedBlockStatement | ScopedBlockStatement) {
        super(StatementTag.LoggerPrefixStatement, sinfo);
        this.msg = msg;
        this.args = args;
        this.block = block;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class UnscopedBlockStatement extends Statement {
    readonly statements: Statement[];

    constructor(sinfo: SourceInfo, statements: Statement[]) {
        super(StatementTag.UnscopedBlockStatement, sinfo);
        this.statements = statements;
    }
}

class ScopedBlockStatement extends Statement {
    readonly statements: Statement[];

    constructor(sinfo: SourceInfo, statements: Statement[]) {
        super(StatementTag.ScopedBlockStatement, sinfo);
        this.statements = statements;
    }
}

abstract class BodyImplementation {
    readonly sinfo: SourceInfo;
    readonly file: string;

    constructor(sinfo: SourceInfo, file: string) {
        this.sinfo = sinfo;
        this.file = file;
    }

    abstract emit(fmt: CodeFormatter | undefined, headerstr: string | undefined): string;
}

class AbstractBodyImplementation extends BodyImplementation {
    constructor(sinfo: SourceInfo, file: string) {
        super(sinfo, file);
    }

    emit(fmt: CodeFormatter | undefined, headerstr: string | undefined): string {
        if(headerstr === undefined) {
            return "";
        }
        else {
            return headerstr + ";";
        }
    }
}

class BuiltinBodyImplementation extends BodyImplementation {
    readonly builtin: string;

    constructor(sinfo: SourceInfo, file: string, builtin: string) {
        super(sinfo, file);

        this.builtin = builtin;
    }

    emit(fmt: CodeFormatter | undefined, headerstr: string | undefined): string {
        if(headerstr === undefined) {
            return ` = ${this.builtin};`;
        }
        else {
            return headerstr + " = " + this.builtin + ";";
        }
    }
}

class SynthesisBodyImplementation extends BodyImplementation {
    constructor(sinfo: SourceInfo, file: string) {
        super(sinfo, file);
    }

    emit(fmt: CodeFormatter | undefined, headerstr: string | undefined): string {
        let hstr = "";
        if(headerstr !== undefined) {
            hstr = " " + headerstr;
        }

        if(fmt === undefined) {
            return `{${hstr} defer; }`;
        }
        else {
            fmt.indentPush();
            const bb = fmt.indent("defer;");
            fmt.indentPop();

            return `{${hstr}\n${bb}\n${fmt.indent("}")}`;
        }
    }
}

class ExpressionBodyImplementation extends BodyImplementation {
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, file: string, exp: Expression) {
        super(sinfo, file);
        this.exp = exp;
    }

    emit(fmt: CodeFormatter | undefined, headerstr: string | undefined): string {
        let hstr = "";
        if(headerstr !== undefined) {
            hstr = " " + headerstr;
        }

        if(fmt === undefined) {
            return `{${hstr} return ${this.exp.emit()}; }`;
        }
        else {
            fmt.indentPush();
            const bb = fmt.indent("return " + this.exp.emit() + ";");
            fmt.indentPop();

            return `{${hstr}\n${bb}\n${fmt.indent("}")}`;
        }
    }
}

class StandardBodyImplementation extends BodyImplementation {
    readonly statements: Statement[];

    constructor(sinfo: SourceInfo, file: string, statements: Statement[]) {
        super(sinfo, file);
        this.statements = statements;
    }

    emit(fmt: CodeFormatter | undefined, headerstr: string | undefined): string {
        let hstr = "";
        if(headerstr !== undefined) {
            hstr = " " + headerstr;
        }

        if(fmt === undefined) {
            return `{${hstr} ${this.statements.map((stmt) => stmt.emit(undefined)).join(" ")} }`;
        }
        else {
            fmt.indentPush();
            const bb = this.statements.map((stmt) => stmt.emit(fmt)).join("\n");
            fmt.indentPop();

            return `{${hstr}\n${bb}\n${fmt.indent("}")}`;
        }
    }
}

export {
    RecursiveAnnotation,
    ITest, ITestType, ITestLiteral, ITestNone, ITestSome, ITestNothing, ITestSomething, ITestOk, ITestErr,
    ArgumentValue, PositionalArgumentValue, NamedArgumentValue, SpreadArgumentValue, ArgumentList,
    ExpressionTag, Expression, LiteralExpressionValue, ConstantExpressionValue, InvalidExpression,
    LiteralSingletonExpression, LiteralSimpleExpression, LiteralRegexExpression, LiteralTypedStringExpression, LiteralTemplateStringExpression, LiteralPathExpression,
    LiteralTypeDeclValueExpression,
    BSQONLiteralExpression,
    StringSliceExpression,
    AccessEnvValueExpression, TaskAccessInfoExpression,
    AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression,
    ConstructorExpression, ConstructorPrimaryExpression, ConstructorTupleExpression, ConstructorRecordExpression, ConstructorEListExpression,
    ConstructorLambdaExpression, SpecialConstructorExpression,
    LambdaInvokeExpression,
    CallNamespaceFunctionExpression, CallTypeFunctionExpression, CallRefThisExpression,
    LogicActionAndExpression, LogicActionOrExpression,
    PostfixOpTag, PostfixOperation, PostfixOp,
    PostfixAccessFromIndex, PostfixProjectFromIndecies, PostfixAccessFromName, PostfixProjectFromNames,
    PostfixIsTest, PostfixAsConvert,
    PostfixAssignFields,
    PostfixInvoke,
    UnaryExpression, PrefixNotOp, PrefixNegateOp,
    BinaryArithExpression, BinAddExpression, BinSubExpression, BinMultExpression, BinDivExpression,
    BinaryKeyExpression, BinKeyEqExpression, BinKeyNeqExpression,
    BinaryNumericExpression, NumericEqExpression, NumericNeqExpression, NumericLessExpression, NumericLessEqExpression, NumericGreaterExpression, NumericGreaterEqExpression,
    BinLogicExpression, BinLogicAndxpression, BinLogicOrExpression, BinLogicImpliesExpression, BinLogicIFFExpression,
    MapEntryConstructorExpression,
    IfTest,
    IfExpression,
    TaskSelfFieldExpression, TaskSelfControlExpression, TaskSelfActionExpression, TaskGetIDExpression, TaskCancelRequestedExpression,
    StatementTag, Statement, InvalidStatement, EmptyStatement,
    VariableDeclarationStatement, VariableAssignmentStatement,
    VariableRetypeStatement, ExpressionSCReturnStatement, VariableSCRetypeStatement,
    ReturnStatement,
    IfStatement, AbortStatement, AssertStatement, DebugStatement, RefCallStatement,
    SwitchStatement, MatchStatement,
    EnvironmentFreshStatement, EnvironmentSetStatement, EnvironmentSetStatementBracket,
    TaskRunStatement, TaskMultiStatement, TaskDashStatement, TaskAllStatement, TaskRaceStatement,
    TaskCallWithStatement, TaskResultWithStatement,
    TaskSetStatusStatement, TaskEventEmitStatement, TaskSetSelfFieldStatement, 
    LoggerLevel, LoggerEmitStatement, LoggerEmitConditionalStatement, LoggerLevelStatement, LoggerCategoryStatement, LoggerPrefixStatement,
    UnscopedBlockStatement, ScopedBlockStatement, 
    BodyImplementation, AbstractBodyImplementation, BuiltinBodyImplementation, SynthesisBodyImplementation, ExpressionBodyImplementation, StandardBodyImplementation
};
