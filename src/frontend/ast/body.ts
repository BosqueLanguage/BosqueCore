
import { FullyQualifiedNamespace, AutoTypeSignature, RecursiveAnnotation, TypeSignature } from "./type";

import { BuildLevel, CodeFormatter, SourceInfo } from "../build_decls";
import { LambdaDecl } from "./assembly";

class BinderInfo {
    readonly srcname: string; //the name in the source code
    readonly scopename: string;    //maybe a different name that gets used for shadowing binders
    readonly implicitdef: boolean;

    constructor(srcname: string, scopename: string, implicitdef: boolean) {
        this.srcname = srcname;
        this.scopename = scopename;
        this.implicitdef = implicitdef;
    }

    emit(): string {
        return !this.implicitdef ? `${this.srcname}${this.srcname !== this.scopename ? ("%*" + this.scopename + "*%") : ""}  = ` : "";
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
        return `${this.isnot ? "!" : ""}<${this.ttype.emit(true)}>`;
    }
}

class ITestLiteral extends ITest {
    readonly literal: LiteralExpressionValue;
    
    constructor(isnot: boolean, literal: LiteralExpressionValue) {
        super(isnot);
        this.literal = literal;
    }

    emit(fmt: CodeFormatter): string {
        return `${this.isnot ? "!" : ""}[${this.literal.emit(true, fmt)}]`;
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

class ITestNothing extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(fmt: CodeFormatter): string {
        return `${this.isnot ? "!" : ""}nothing`;
    }
}

class ITestSomething extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(fmt: CodeFormatter): string {
        return `${this.isnot ? "!" : ""}something`;
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

class ITestErr extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }

    emit(fmt: CodeFormatter): string {
        return `${this.isnot ? "!" : ""}err`;
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
    ErrorExpresion = "ErrorExpression",

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

    StringSliceExpression = "StringSliceExpression",
    ASCIIStringSliceExpression = "ASCIIStringSliceExpression",

    InterpolateExpression = "InterpolateExpression",

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

    LetExpression = "LetExpression",

    LambdaInvokeExpression = "LambdaInvokeExpression",
    SpecialConstructorExpression = "SpecialConstructorExpression",
    CallNamespaceFunctionExpression = "CallNamespaceFunctionExpression",
    CallTypeFunctionExpression = "CallTypeFunctionExpression",
    CallRefThisExpression = "CallRefThisExpression",
    CallRefSelfExpression = "CallRefSelfExpression",
    CallTaskActionExpression = "CallTaskActionExpression",
    
    LogicActionAndExpression = "LogicActionAndExpression",
    LogicActionOrExpression = "LogicActionOrExpression",

    ParseAsTypeExpression = "ParseAsTypeExpression",

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

    constructor(tag: ExpressionTag, sinfo: SourceInfo) {
        this.tag = tag;
        this.sinfo = sinfo;
    }

    abstract emit(toplevel: boolean, fmt: CodeFormatter): string;
}

class ErrorExpression extends Expression {
    constructor(sinfo: SourceInfo) {
        super(ExpressionTag.ErrorExpresion, sinfo);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return "[!ERROR_EXP!]";
    }
}

//This just holds a constant expression that can be evaluated without any arguments but not a subtype of Expression so we can distinguish as types
class LiteralExpressionValue {
    readonly exp: Expression;

    constructor(exp: Expression) {
        this.exp = exp;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.exp.emit(toplevel, fmt);
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

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.exp.emit(toplevel, fmt);
    }
}

class LiteralSingletonExpression extends Expression {
    readonly value: string;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, value: "none" | "nothing") {
        super(tag, sinfo);

        this.value = value;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.value;
    }
}

class LiteralSimpleExpression extends Expression {
    readonly value: string;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, value: string) {
        super(tag, sinfo);
        this.value = value;
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

class LiteralTypedStringExpression extends Expression {
    readonly value: string;
    readonly stype: TypeSignature;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, value: string, stype: TypeSignature) {
        super(tag, sinfo);
        this.value = value;
        this.stype = stype;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.value + this.stype.emit(true);
    }
}

class LiteralTemplateStringExpression extends Expression {
    readonly value: string;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, value: string) {
        super(tag, sinfo);
        this.value = value;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.value; //should be $"" for unicode and $'' for ascii
    }
}

class LiteralPathExpression extends Expression {
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

    constructor(sinfo: SourceInfo, value: Expression, constype: TypeSignature) {
        super(ExpressionTag.LiteralTypeDeclValueExpression, sinfo);
        this.value = value;
        this.constype = constype;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.value.emit(toplevel, fmt)}_${this.constype.emit(true)}`;
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

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.str.emit(toplevel, fmt)}[${this.start ? this.start.emit(toplevel, fmt) : ""}:${this.end ? this.end.emit(toplevel, fmt) : ""}]`;
    }
}

class InterpolateExpression extends Expression {
    readonly str: Expression;
    readonly args: ArgumentList;

    constructor(sinfo: SourceInfo, str: Expression, args: ArgumentList) {
        super(ExpressionTag.InterpolateExpression, sinfo);
        this.str = str;
        this.args = args;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `interpolate(${this.str.emit(toplevel, fmt)}, ${this.args.emit(fmt, ", ", "")}`;
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
    readonly name: string;

    constructor(sinfo: SourceInfo, ns: FullyQualifiedNamespace, name: string) {
        super(ExpressionTag.AccessNamespaceConstantExpression, sinfo);
        this.ns = ns;
        this.name = name;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.ns.emit()}::${this.name}`;
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

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.stype.emit(false)}::${this.name}`;
    }
}

class AccessVariableExpression extends Expression {
    readonly srcname: string; //the name in the source code
    readonly scopename: string;    //maybe a different name that gets used for shadowing binders

    constructor(sinfo: SourceInfo, srcname: string, scopename: string) {
        super(ExpressionTag.AccessVariableExpression, sinfo);
        this.srcname = srcname;
        this.scopename = scopename;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.srcname + (this.scopename !== this.srcname ? `%*${this.scopename}*%` : "");
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

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.ctype.emit(true)}${this.args.emit(fmt, "{", "}")}`;
    }
}

class ConstructorTupleExpression extends ConstructorExpression {
    constructor(sinfo: SourceInfo, args: ArgumentList) {
        super(ExpressionTag.ConstructorTupleExpression, sinfo, args);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.args.emit(fmt, "[", "]");
    }
}

class ConstructorRecordExpression extends ConstructorExpression {
    constructor(sinfo: SourceInfo, args: ArgumentList) {
        super(ExpressionTag.ConstructorRecordExpression, sinfo, args);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.args.emit(fmt, "{", "}");
    }
}

class ConstructorEListExpression extends ConstructorExpression {
    constructor(sinfo: SourceInfo, args: ArgumentList) {
        super(ExpressionTag.ConstructorEListExpression, sinfo, args);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.args.emit(fmt, "(", ")");
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

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.invoke.emit(fmt);
    }
}

class LetExpression extends Expression {
    readonly decls: {vname: string, vtype: TypeSignature | undefined, value: Expression}[];
    readonly body: Expression;

    constructor(sinfo: SourceInfo, decls: {vname: string, vtype: TypeSignature | undefined, value: Expression}[], body: Expression) {
        super(ExpressionTag.LetExpression, sinfo);
        this.decls = decls;
        this.body = body;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const dds = this.decls.map((dd) => `${dd.vname}${dd.vtype !== undefined ? ":" + dd.vtype.emit(true) : ""} = ${dd.value.emit(true, fmt)};`).join(", ");
        return `{| let ${dds} in ${this.body.emit(true, fmt)} |}`;
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

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `${this.rop}(${this.arg.emit(toplevel, fmt)})`;
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

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        let rec = "";
        if(this.rec !== "no") {
            rec = "[" + (this.rec === "yes" ? "recursive" : "recursive?") + "]";
        }
        
        let terms = "";
        if(this.terms.length !== 0) {
            terms = "<" + this.terms.map((tt) => tt.emit(true)).join(", ") + ">";
        }

        return `${this.ns.emit()}::${this.name}${rec}${terms}${this.args.emit(fmt, "(", ")")}`;
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

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        let rec = "";
        if(this.rec !== "no") {
            rec = "[" + (this.rec === "yes" ? "recursive" : "recursive?") + "]";
        }
        
        let terms = "";
        if(this.terms.length !== 0) {
            terms = "<" + this.terms.map((tt) => tt.emit(true)).join(", ") + ">";
        }

        return `${this.ttype.emit(false)}::${this.name}${rec}${terms}${this.args.emit(fmt, "(", ")")}`;
    }
}

class CallRefThisExpression extends Expression {
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

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        let rec = "";
        if(this.rec !== "no") {
            rec = "[" + (this.rec === "yes" ? "recursive" : "recursive?") + "]";
        }
        
        let terms = "";
        if(this.terms.length !== 0) {
            terms = "<" + this.terms.map((tt) => tt.emit(true)).join(", ") + ">";
        }

        return `ref this.${this.name}${rec}${terms}${this.args.emit(fmt, "(", ")")}`;
    }
}

class CallRefSelfExpression extends Expression {
    readonly name: string;
    readonly rec: RecursiveAnnotation;
    readonly terms: TypeSignature[];
    readonly args: ArgumentList;

    constructor(sinfo: SourceInfo, name: string, terms: TypeSignature[], rec: RecursiveAnnotation, args: ArgumentList) {
        super(ExpressionTag.CallRefSelfExpression, sinfo);
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
            terms = "<" + this.terms.map((tt) => tt.emit(true)).join(", ") + ">";
        }

        return `ref self.${this.name}${rec}${terms}${this.args.emit(fmt, "(", ")")}`;
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
            terms = "<" + this.terms.map((tt) => tt.emit(true)).join(", ") + ">";
        }

        return `do self.${this.name}${terms}${this.args.emit(fmt, "(", ")")}`;
    }
}

class LogicActionAndExpression extends Expression {
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, args: Expression[]) {
        super(ExpressionTag.LogicActionAndExpression, sinfo);
        this.args = args;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `/\\(${this.args.map((arg) => arg.emit(toplevel, fmt)).join(", ")})`;
    }
}

class LogicActionOrExpression extends Expression {
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, args: Expression[]) {
        super(ExpressionTag.LogicActionOrExpression, sinfo);
        this.args = args;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return `\\/(${this.args.map((arg) => arg.emit(toplevel, fmt)).join(", ")})`;
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
        return `<${this.ttype.emit(true)}>(${this.exp.emit(toplevel, fmt)})`;
    }
}

enum PostfixOpTag {
    PostfixError = "PostfixError",

    PostfixAccessFromIndex = "PostfixAccessFromIndex",
    PostfixProjectFromIndecies = "PostfixProjectFromIndecies",
    PostfixAccessFromName = "PostfixAccessFromName",
    PostfixProjectFromNames = "PostfixProjectFromNames",

    PostfixIsTest = "PostfixIsTest",
    PostfixAsConvert = "PostfixAsConvert",

    PostfixAssignFields = "PostfixAssignFields",

    PostfixInvoke = "PostfixInvoke",
    PostfixLiteralKeyAccess = "PostfixLiteralKeyAccess"
}

abstract class PostfixOperation {
    readonly sinfo: SourceInfo;
    readonly op: PostfixOpTag;

    constructor(sinfo: SourceInfo, op: PostfixOpTag) {
        this.sinfo = sinfo;
        this.op = op;
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

class PostfixAccessFromIndex extends PostfixOperation {
    readonly index: number;
    readonly isLiteralOp: boolean;

    constructor(sinfo: SourceInfo, index: number, isLiteralOp: boolean) {
        super(sinfo, PostfixOpTag.PostfixAccessFromIndex);
        this.index = index;
        this.isLiteralOp = isLiteralOp;
    }

    emit(fmt: CodeFormatter): string {
        return `${this.isLiteralOp ? "!" : ""}.${this.index}`;
    }
}

class PostfixProjectFromIndecies extends PostfixOperation {
    readonly indecies: number[];

    constructor(sinfo: SourceInfo, indecies: number[]) {
        super(sinfo, PostfixOpTag.PostfixProjectFromIndecies);
        this.indecies = indecies;
    }

    emit(fmt: CodeFormatter): string {
        return `.(${this.indecies.join(", ")})`;
    }
}

class PostfixAccessFromName extends PostfixOperation {
    readonly name: string;
    readonly isLiteralOp: boolean;

    constructor(sinfo: SourceInfo, name: string, isLiteralOp: boolean) {
        super(sinfo, PostfixOpTag.PostfixAccessFromName);
        this.name = name;
        this.isLiteralOp = isLiteralOp;
    }

    emit(fmt: CodeFormatter): string {
        return `${this.isLiteralOp ? "!" : ""}.${this.name}`;
    }
}

class PostfixProjectFromNames extends PostfixOperation {
    readonly names: string[];

    constructor(sinfo: SourceInfo, names: string[]) {
        super(sinfo, PostfixOpTag.PostfixProjectFromNames);
        this.names = names;
    }

    emit(fmt: CodeFormatter): string {
        return `.(${this.names.join(", ")})`;
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
    readonly updates: ArgumentList;

    constructor(sinfo: SourceInfo, updates: ArgumentList) {
        super(sinfo, PostfixOpTag.PostfixAssignFields);
        this.updates = updates;
    }

    emit(fmt: CodeFormatter): string {
        return `.${this.updates.emit(fmt, "[", "]")}`;
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

    emit(fmt: CodeFormatter): string {
        let rec = "";
        if(this.rec !== "no") {
            rec = "[" + (this.rec === "yes" ? "recursive" : "recursive?") + "]";
        }

        return `${this.specificResolve ? this.specificResolve.emit(false) + "::" : ""}${this.name}${rec}${this.args.emit(fmt, "(", ")")}`;
    }
}

class PostfixLiteralKeyAccess extends PostfixOperation {
    readonly kexp: Expression;

    constructor(sinfo: SourceInfo, kexp: Expression) {
        super(sinfo, PostfixOpTag.PostfixLiteralKeyAccess);
        this.kexp = kexp;
    }

    emit(fmt: CodeFormatter): string {
        return `![${this.kexp.emit}]`;
    }
}

abstract class UnaryExpression extends Expression {
    readonly exp: Expression;

    constructor(tag: ExpressionTag, sinfo: SourceInfo, exp: Expression) {
        super(tag, sinfo);
        this.exp = exp;
    }

    uopEmit(toplevel: boolean, fmt: CodeFormatter, op: string): string {
        const ee = `${op}${this.exp.emit(false, fmt)}`;
        return toplevel ? ee : `(${ee})`;
    }
}

class PrefixNotOp extends UnaryExpression {
    constructor(sinfo: SourceInfo, exp: Expression) {
        super(ExpressionTag.PrefixNotOpExpression, sinfo, exp);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.uopEmit(toplevel, fmt, "!");
    }
}

class PrefixNegateOp extends UnaryExpression {
    constructor(sinfo: SourceInfo, exp: Expression) {
        super(ExpressionTag.PrefixNegateOpExpression, sinfo, exp);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.uopEmit(toplevel, fmt, "-");
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

abstract class BinaryNumericExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

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

class BinLogicAndxpression extends BinLogicExpression {
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

class BinLogicImpliesExpression extends BinLogicExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinLogicImpliesExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.blopEmit(toplevel, fmt, "==>");
    }
}

class BinLogicIFFExpression extends BinLogicExpression {
    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinLogicIFFExpression, sinfo, lhs, rhs);
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        return this.blopEmit(toplevel, fmt, "<==>");
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
    readonly trueValue: Expression
    readonly trueValueBinder: BinderInfo | undefined;
    readonly falseValue: Expression;
    readonly falseValueBinder: BinderInfo | undefined;

    constructor(sinfo: SourceInfo, test: IfTest, trueValue: Expression, trueValueBinder: BinderInfo | undefined, falseValue: Expression, falseValueBinder: BinderInfo | undefined) {
        super(ExpressionTag.IfExpression, sinfo);
        this.test = test;
        this.trueValue = trueValue;
        this.trueValueBinder = trueValueBinder;
        this.falseValue = falseValue;
        this.falseValueBinder = falseValueBinder;
    }

    emit(toplevel: boolean, fmt: CodeFormatter): string {
        const ttest = (this.trueValueBinder !== undefined ? this.trueValueBinder.emit() : "") + (this.test.itestopt !== undefined ? this.test.itestopt.emit(fmt) : "") + `(${this.test.exp.emit(true, fmt)})`;
        return `if ${ttest} then ${this.trueValue.emit(true, fmt)} else ${this.falseValue.emit(true, fmt)}`;
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
    readonly args: ArgumentList;

    constructor(sinfo: SourceInfo, args: ArgumentList) {
        super(EnvironmentGenerationExpressionTag.InitializeEnvironmentExpression, sinfo);
        this.args = args;
    }

    emit(fmt: CodeFormatter): string {
        return `env${this.args.emit(fmt, "{", "}")}`;
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
    readonly updates: ArgumentList;

    constructor(sinfo: SourceInfo, updates: ArgumentList) {
        super(sinfo, PostfixEnvironmentOpTag.PostfixEnvironmentOpSet);
        this.updates = updates;
    }

    emit(fmt: CodeFormatter): string {
        return "." + this.updates.emit(fmt, "[", "]");
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
        return `Task::run<${this.task.emit(true) + (this.envi !== undefined ? ", " + this.envi.emit(fmt) : "")}>(this.args.emit("(", ")"), ${this.enva.emit(fmt)})`;
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
        return `Task::run<${this.tasks.map((tt) => tt.emit(true)).join(", ") + (this.envi !== undefined ? ", " + this.envi.emit(fmt) : "")}>(${argl.join("; ")})`;
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
        return `Task::dash<${this.tasks.map((tt) => tt.emit(true)).join(", ") + (this.envi !== undefined ? ", " + this.envi.emit(fmt) : "")}>(${argl.join("; ")})`;
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
        return `Task::all<${this.tasks.map((tt) => tt.emit(true)).join(", ") + (this.envi !== undefined ? ", " + this.envi.emit(fmt) : "")}>(${argl.join("; ")})`;
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
        return `Task::race<${this.tasks.map((tt) => tt.emit(true)).join(", ") + (this.envi !== undefined ? ", " + this.envi.emit(fmt) : "")}>(${argl.join("; ")})`;
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
    ReturnStatement = "ReturnStatement",

    IfElseStatement = "IfElseStatement",
    MatchStatement = "MatchStatement",

    AbortStatement = "AbortStatement",
    AssertStatement = "AssertStatement", //assert(x > 0)
    ValidateStatement = "ValidateStatement", //assert(x > 0)

    DebugStatement = "DebugStatement", //print an arg or if empty attach debugger

    StandaloneExpressionStatement = "StandaloneExpressionStatement",
    ThisUpdateStatement = "ThisUpdateStatement",
    SelfUpdateStatement = "SelfUpdateStatement",

    EnvironmentUpdateStatement = "EnvironmentUpdateStatement",
    EnvironmentBracketStatement = "EnvironmentBracketStatement",

    TaskStatusStatement = "TaskStatusStatement", //do a status emit Task::emitStatusUpdate(...)
    TaskEventEmitStatement = "TaskEventEmitStatement", //Task::event(...)

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
        return `error`;
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
        return `var ${this.name}: ${this.vtype.emit(true)}$;`;
    }
}

class VariableMultiDeclarationStatement extends Statement {
    readonly decls: [string, TypeSignature][];

    constructor(sinfo: SourceInfo, decls: [string, TypeSignature][]) {
        super(StatementTag.VariableMultiDeclarationStatement, sinfo);
        this.decls = decls;
    }

    emit(fmt: CodeFormatter): string {
        return `var ${this.decls.map(([name, vtype]) => `${name}: ${vtype.emit(true)}`).join(", ")};`;
    }
}

class VariableInitializationStatement extends Statement {
    readonly isConst: boolean;
    readonly name: string;
    readonly vtype: TypeSignature; //maybe Auto
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, isConst: boolean, name: string, vtype: TypeSignature, exp: Expression) {
        super(StatementTag.VariableInitializationStatement, sinfo);
        this.isConst = isConst;
        this.name = name;
        this.vtype = vtype;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        const dc = this.isConst ? "let" : "var";
        const tt = this.vtype instanceof AutoTypeSignature ? "" : `: ${this.vtype.emit(true)}`;

        return `${dc} ${this.name}${tt} = ${this.exp.emit(true, fmt)};`;
    }
}

class VariableMultiInitializationStatement extends Statement {
    readonly isConst: boolean;
    readonly decls: [string, TypeSignature][]; //maybe Auto
    readonly exp: Expression | Expression[]; //could be a single expression of type EList or multiple expressions

    constructor(sinfo: SourceInfo, isConst: boolean, decls: [string, TypeSignature][], exp: Expression | Expression[]) {
        super(StatementTag.VariableMultiInitializationStatement, sinfo);
        this.isConst = isConst;
        this.decls = decls;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        const dc = this.isConst ? "let" : "var";
        const ttdecls = this.decls.map((dd) => dd[0] + (dd[1] instanceof AutoTypeSignature ? "" : `: ${dd[1].emit(true)}`));
        const ttexp = Array.isArray(this.exp) ? this.exp.map((ee) => ee.emit(true, fmt)).join(", ") : this.exp.emit(true, fmt);

        return `${dc} ${ttdecls.join(", ")} = ${ttexp};`;
    }
}

class VariableAssignmentStatement extends Statement {
    readonly name: string;
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, name: string, exp: Expression) {
        super(StatementTag.VariableAssignmentStatement, sinfo);
        this.name = name;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return `${this.name} = ${this.exp.emit(true, fmt)};`;
    }
}

class VariableMultiAssignmentStatement extends Statement {
    readonly name: string[];
    readonly exp: Expression | Expression[]; //could be a single expression of type EList or multiple expressions

    constructor(sinfo: SourceInfo, name: string[], exp: Expression | Expression[]) {
        super(StatementTag.VariableAssignmentStatement, sinfo);
        this.name = name;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        const ttname = this.name.join(", ");
        const ttexp = Array.isArray(this.exp) ? this.exp.map((ee) => ee.emit(true, fmt)).join(", ") : this.exp.emit(true, fmt);

        return `${ttname} = ${ttexp};`;
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

    emit(fmt: CodeFormatter): string {
        return `ref ${this.name}@${this.ttest.emit(fmt)};`;
    }
}

class ReturnStatement extends Statement {
    readonly value: Expression | Expression[]; //array is implicitly converted to EList

    constructor(sinfo: SourceInfo, value: Expression | Expression[]) {
        super(StatementTag.ReturnStatement, sinfo);
        this.value = value;
    }

    emit(fmt: CodeFormatter): string {
        return `return ${Array.isArray(this.value) ? this.value.map((vv) => vv.emit(true, fmt)).join(", ") : this.value.emit(true, fmt)};`;
    }
}

class IfStatement extends Statement {
    readonly condflow: {cond: IfTest, value: BlockStatement, binderinfo: BinderInfo | undefined}[];
    readonly elseflow: {value: BlockStatement, binderinfo: BinderInfo | undefined} | undefined;

    constructor(sinfo: SourceInfo, condflow: {cond: IfTest, value: BlockStatement, binderinfo: BinderInfo | undefined}[], elseflow: {value: BlockStatement, binderinfo: BinderInfo | undefined} | undefined) {
        super(StatementTag.IfElseStatement, sinfo);
        this.condflow = condflow;
        this.elseflow = elseflow;
    }

    emit(fmt: CodeFormatter): string {
        const ttcond = this.condflow.map((cf) => `${cf.binderinfo !== undefined ? cf.binderinfo.emit() : ""}${cf.cond.itestopt !== undefined ? cf.cond.itestopt.emit(fmt) : ""}(${cf.cond.exp.emit(true, fmt)}) ${cf.value.emit(fmt)}`);
        const ttelse = this.elseflow !== undefined ? this.elseflow.value.emit(fmt) : undefined;

        const iif = `if ${ttcond[0]}`;
        const ielifs = ttcond.slice(1).map((cc) => fmt.indent(`elif ${cc}`));

        if(ttelse !== undefined) {
            ielifs.push(fmt.indent(`else ${ttelse}`));
        }

        return [iif, ...ielifs].join("\n");
    }
}

class MatchStatement extends Statement {
    readonly sval: [Expression, BinderInfo | undefined];
    readonly matchflow: {mtype: TypeSignature | undefined, value: BlockStatement, bindername: string | undefined}[];

    constructor(sinfo: SourceInfo, sval: [Expression, BinderInfo | undefined], flow: {mtype: TypeSignature | undefined, value: BlockStatement, bindername: string | undefined}[]) {
        super(StatementTag.MatchStatement, sinfo);
        this.sval = sval;
        this.matchflow = flow;
    }

    emit(fmt: CodeFormatter): string {
        const mheader = `match ${this.sval[1] !== undefined ? this.sval[1].emit() : ""}(${this.sval[0].emit(true, fmt)})`;
        fmt.indentPush();
        const ttmf = this.matchflow.map((mf) => `${mf.mtype ? mf.mtype.emit(true) : "_"} => ${mf.value.emit(fmt)}`);
        fmt.indentPop();

        const iil = fmt.indent(ttmf[0]);
        const iir = ttmf.slice(1).map((cc) => fmt.indent("| " + cc));

        return `${mheader}{\n${[iil, ...iir].join("\n")}\n${fmt.indent("}")}`;
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
    readonly cond: Expression;
    readonly level: BuildLevel;

    constructor(sinfo: SourceInfo, cond: Expression, level: BuildLevel) {
        super(StatementTag.AssertStatement, sinfo);
        this.cond = cond;
        this.level = level;
    }

    emit(fmt: CodeFormatter): string {
        const level = (this.level !== "release") ? (this.level + " ") : "";
        return `assert${level} ${this.cond.emit(true, fmt)};`;
    }
}


class ValidateStatement extends Statement {
    readonly cond: Expression;
    readonly diagnosticTag: string | undefined

    constructor(sinfo: SourceInfo, cond: Expression, diagnosticTag: string | undefined) {
        super(StatementTag.ValidateStatement, sinfo);
        this.cond = cond;
        this.diagnosticTag = diagnosticTag;
    }

    emit(fmt: CodeFormatter): string {
        const ttg = (this.tag !== undefined) ? "" : `[${this.diagnosticTag}]`;
        return `validate${ttg} ${this.cond.emit(true, fmt)};`;
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

class StandaloneExpressionStatement extends Statement {
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, exp: Expression) {
        super(StatementTag.StandaloneExpressionStatement, sinfo);
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return `${this.exp.emit(true, fmt)};`;
    }
}

class ThisUpdateStatement extends Statement {
    readonly updates: [string, Expression][];

    constructor(sinfo: SourceInfo, updates: [string, Expression][]) {
        super(StatementTag.ThisUpdateStatement, sinfo);
        this.updates = updates;
    }

    emit(fmt: CodeFormatter): string {
        const updates = this.updates.map(([name, exp]) => `${name} = ${exp.emit(true, fmt)}`).join(", ");
        return `ref this[${updates}];`;
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
    readonly updates: [LiteralExpressionValue, Expression][]; //ascii strings

    constructor(sinfo: SourceInfo, updates: [LiteralExpressionValue, Expression][]) {
        super(StatementTag.EnvironmentUpdateStatement, sinfo);
        this.updates = updates;
    }

    emit(fmt: CodeFormatter): string {
        const updates = this.updates.map(([name, exp]) => `${name.emit(true, fmt)} = ${exp.emit(true, fmt)}`).join(", ");
        return `env[${updates}];`;
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

class TaskEventEmitStatement extends Statement {
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, exp: Expression) {
        super(StatementTag.TaskEventEmitStatement, sinfo);
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return `Task::event(${this.exp.emit(true, fmt)});`;
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
            terms = "<" + this.terms.map((tt) => tt.emit(true)).join(", ") + ">";
        }

        return `yield self.${this.name}${terms}${this.args.emit(fmt, "(", ")")};`;
    }
}

class BlockStatement extends Statement {
    readonly statements: Statement[];

    constructor(sinfo: SourceInfo, statements: Statement[]) {
        super(StatementTag.BlockStatement, sinfo);
        this.statements = statements;
    }

    emit(fmt: CodeFormatter): string {
        fmt.indentPush();
        const bb = this.statements.map((stmt) => fmt.indent(stmt.emit(fmt))).join("\n");
        fmt.indentPop();

        return `{${bb}}`;
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

class SynthesisBodyImplementation extends BodyImplementation {
    constructor(sinfo: SourceInfo, file: string) {
        super(sinfo, file);
    }

    emit(fmt: CodeFormatter, headerstr: string | undefined): string {
        let hstr = "";
        if(headerstr !== undefined) {
            hstr = " " + headerstr;
        }

        if(fmt === undefined) {
            return `{${hstr} $?_; }`;
        }
        else {
            fmt.indentPush();
            const bb = fmt.indent("$?_;");
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
                if(stmt.tag === StatementTag.IfElseStatement || stmt.tag === StatementTag.MatchStatement || stmt.tag === StatementTag.BlockStatement) {
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
    BinderInfo, ITest, ITestType, ITestLiteral, ITestNone, ITestSome, ITestNothing, ITestSomething, ITestOk, ITestErr,
    ArgumentValue, PositionalArgumentValue, NamedArgumentValue, SpreadArgumentValue, ArgumentList,
    ExpressionTag, Expression, ErrorExpression, LiteralExpressionValue, ConstantExpressionValue,
    LiteralSingletonExpression, LiteralSimpleExpression, LiteralRegexExpression, LiteralTypedStringExpression, LiteralTemplateStringExpression, LiteralPathExpression,
    LiteralTypeDeclValueExpression,
    StringSliceExpression, InterpolateExpression,
    AccessEnvValueExpression, TaskAccessInfoExpression,
    AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression,
    ConstructorExpression, ConstructorPrimaryExpression, ConstructorTupleExpression, ConstructorRecordExpression, ConstructorEListExpression,
    ConstructorLambdaExpression, SpecialConstructorExpression,
    LetExpression,
    LambdaInvokeExpression,
    CallNamespaceFunctionExpression, CallTypeFunctionExpression, CallRefThisExpression,
    CallRefSelfExpression, CallTaskActionExpression,
    LogicActionAndExpression, LogicActionOrExpression,
    ParseAsTypeExpression,
    PostfixOpTag, PostfixOperation, PostfixOp,
    PostfixError, PostfixAccessFromIndex, PostfixProjectFromIndecies, PostfixAccessFromName, PostfixProjectFromNames,
    PostfixIsTest, PostfixAsConvert,
    PostfixAssignFields,
    PostfixInvoke,
    PostfixLiteralKeyAccess,
    UnaryExpression, PrefixNotOp, PrefixNegateOp,
    BinaryArithExpression, BinAddExpression, BinSubExpression, BinMultExpression, BinDivExpression,
    BinaryKeyExpression, BinKeyEqExpression, BinKeyNeqExpression,
    BinaryNumericExpression, NumericEqExpression, NumericNeqExpression, NumericLessExpression, NumericLessEqExpression, NumericGreaterExpression, NumericGreaterEqExpression,
    BinLogicExpression, BinLogicAndxpression, BinLogicOrExpression, BinLogicImpliesExpression, BinLogicIFFExpression,
    MapEntryConstructorExpression,
    IfTest,
    IfExpression,
    EnvironmentGenerationExpressionTag, EnvironmentGenerationExpression, ErrorEnvironmentExpression,
    TaskRunExpression, TaskMultiExpression, TaskDashExpression, TaskAllExpression, TaskRaceExpression,
    BaseEnvironmentOpExpression, EmptyEnvironmentExpression, InitializeEnvironmentExpression, CurrentEnvironmentExpression, 
    PostfixEnvironmentOpTag, PostfixEnvironmentOp, PostFixEnvironmentOpError, PostfixEnvironmentOpSet, PostfixEnvironmentOpExpression,
    StatementTag, Statement, ErrorStatement, EmptyStatement,
    VariableDeclarationStatement, VariableMultiDeclarationStatement, VariableInitializationStatement, VariableMultiInitializationStatement, VariableAssignmentStatement, VariableMultiAssignmentStatement,
    VariableRetypeStatement,
    ReturnStatement,
    IfStatement, MatchStatement, AbortStatement, AssertStatement, ValidateStatement, DebugStatement,
    StandaloneExpressionStatement, ThisUpdateStatement, SelfUpdateStatement,
    EnvironmentUpdateStatement, EnvironmentBracketStatement,
    TaskStatusStatement, TaskEventEmitStatement,
    TaskYieldStatement,
    BlockStatement, 
    BodyImplementation, AbstractBodyImplementation, PredicateUFBodyImplementation, BuiltinBodyImplementation, SynthesisBodyImplementation, ExpressionBodyImplementation, StandardBodyImplementation
};
