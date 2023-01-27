//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { RecursiveAnnotation, TypeSignature } from "./type";
import { InvokeDecl } from "./assembly";

import { BuildLevel, LoggerLevel, SourceInfo } from "../build_decls";
import { BSQRegex } from "../bsqregex";

abstract class ITest {
    readonly isnot: boolean;

    constructor(isnot: boolean) {
        this.isnot = isnot;
    }
}

class ITestType extends ITest {
    readonly ttype: TypeSignature;
    
    constructor(isnot: boolean, ttype: TypeSignature) {
        super(isnot);
        this.ttype = ttype;
    }
}

class ITestLiteral extends ITest {
    readonly literal: LiteralExpressionValue;
    
    constructor(isnot: boolean, literal: LiteralExpressionValue) {
        super(isnot);
        this.literal = literal;
    }
}

class ITestNone extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }
}

class ITestNothing extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }
}

class ITestSomething extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }
}

class ITestOk extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }
}

class ITestErr extends ITest {
    constructor(isnot: boolean) {
        super(isnot);
    }
}

enum ExpressionTag {
    Clear = "[CLEAR]",
    InvalidExpresion = "[INVALID]",

    LiteralNoneExpression = "LiteralNoneExpression",
    LiteralNothingExpression = "LiteralNothingExpression",
    LiteralBoolExpression = "LiteralBoolExpression",
    LiteralIntegralExpression = "LiteralIntegralExpression",
    LiteralRationalExpression = "LiteralRationalExpression",
    LiteralFloatPointExpression = "LiteralFloatExpression",
    LiteralRegexExpression = "LiteralRegexExpression",

    LiteralStringExpression = "LiteralStringExpression",
    LiteralASCIIStringExpression = "LiteralASCIIStringExpression",
    
    LiteralTypedStringExpression = "LiteralTypedStringExpression",
    LiteralASCIITypedStringExpression = "LiteralASCIITypedStringExpression",
    
    LiteralTemplateStringExpression = "LiteralTemplateStringExpression",
    LiteralASCIITemplateStringExpression = "LiteralASCIITemplateStringExpression",
    
    LiteralTypedPrimitiveConstructorExpression = "LiteralTypedPrimitiveConstructorExpression",

    AccessFormatInfoExpression = "AccessFormatInfoExpression",
    AccessEnvValueExpression = "AccessEnvValueExpression",

    AccessNamespaceConstantExpression = "AccessNamespaceConstantExpression",
    AccessStaticFieldExpression = " AccessStaticFieldExpression",
    AccessVariableExpression = "AccessVariableExpression",

    ConstructorPrimaryExpression = "ConstructorPrimaryExpression",
    ConstructorTupleExpression = "ConstructorTupleExpression",
    ConstructorRecordExpression = "ConstructorRecordExpression",
    ConstructorPCodeExpression = "ConstructorPCodeExpression",

    PCodeInvokeExpression = "PCodeInvokeExpression",
    SpecialConstructorExpression = "SpecialConstructorExpression",
    CallNamespaceFunctionOrOperatorExpression = "CallNamespaceFunctionOrOperatorExpression",
    CallStaticFunctionExpression = "CallStaticFunctionExpression",

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

    MapEntryConstructorExpression = "MapEntryConstructorExpression",

    IfExpression = "IfExpression",
    SwitchExpression = "SwitchExpression",
    MatchExpression = "MatchExpression",

    TaskSelfFieldExpression = "TaskSelfFieldExpression",
    TaskSelfControlExpression = "TaskSelfControlExpression",
    TaskSelfActionExpression = "TaskSelfActionExpression",
    TaskGetIDExpression = "TaskGetIDExpression",
    TaskIsCancelRequestedExpression = "TaskIsCancelRequestedExpression"
}

abstract class Expression {
    readonly tag: ExpressionTag;
    readonly sinfo: SourceInfo;

    constructor(tag: ExpressionTag, sinfo: SourceInfo) {
        this.tag = tag;
        this.sinfo = sinfo;
    }

    isCompileTimeInlineValue(): boolean {
        return false;
    }

    isLiteralValueExpression(): boolean {
        return false;
    }

    isTaskOperation(): boolean {
        return false;
    }
}

//This just holds a constant expression that can be evaluated without any arguments but not a subtype of Expression so we can distinguish as types
class LiteralExpressionValue {
    readonly exp: Expression;

    constructor(exp: Expression) {
        this.exp = exp;
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
}

class InvalidExpression extends Expression {
    constructor(sinfo: SourceInfo) {
        super(ExpressionTag.InvalidExpresion, sinfo);
    }
}

class LiteralNoneExpression extends Expression {
    constructor(sinfo: SourceInfo) {
        super(ExpressionTag.LiteralNoneExpression, sinfo);
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }

    isLiteralValueExpression(): boolean {
        return true;
    }
}

class LiteralNothingExpression extends Expression {
    constructor(sinfo: SourceInfo) {
        super(ExpressionTag.LiteralNothingExpression, sinfo);
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }

    isLiteralValueExpression(): boolean {
        return true;
    }
}

class LiteralBoolExpression extends Expression {
    readonly value: boolean;

    constructor(sinfo: SourceInfo, value: boolean) {
        super(ExpressionTag.LiteralBoolExpression, sinfo);
        this.value = value;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }

    isLiteralValueExpression(): boolean {
        return true;
    }
}

class LiteralIntegralExpression extends Expression {
    readonly value: string;
    readonly itype: TypeSignature;

    constructor(sinfo: SourceInfo, value: string, itype: TypeSignature) {
        super(ExpressionTag.LiteralIntegralExpression, sinfo);
        this.value = value;
        this.itype = itype;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }

    isLiteralValueExpression(): boolean {
        return true;
    }
}

class LiteralRationalExpression extends Expression {
    readonly value: string;
    readonly rtype: TypeSignature;

    constructor(sinfo: SourceInfo, value: string, rtype: TypeSignature) {
        super(ExpressionTag.LiteralRationalExpression, sinfo);
        this.value = value;
        this.rtype = rtype;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }
}

class LiteralFloatPointExpression extends Expression {
    readonly value: string;
    readonly fptype: TypeSignature;

    constructor(sinfo: SourceInfo, value: string, fptype: TypeSignature) {
        super(ExpressionTag.LiteralFloatPointExpression, sinfo);
        this.value = value;
        this.fptype = fptype;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }
}

class LiteralStringExpression extends Expression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(ExpressionTag.LiteralStringExpression, sinfo);
        this.value = value;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }

    isLiteralValueExpression(): boolean {
        return true;
    }
}

class LiteralRegexExpression extends Expression {
    readonly value: BSQRegex;

    constructor(sinfo: SourceInfo, value: BSQRegex) {
        super(ExpressionTag.LiteralRegexExpression, sinfo);
        this.value = value;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }
}

class LiteralASCIIStringExpression extends Expression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(ExpressionTag.LiteralASCIIStringExpression, sinfo);
        this.value = value;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }

    isLiteralValueExpression(): boolean {
        return true;
    }
}

class LiteralTypedStringExpression extends Expression {
    readonly value: string;
    readonly stype: TypeSignature;

    constructor(sinfo: SourceInfo, value: string, stype: TypeSignature) {
        super(ExpressionTag.LiteralTypedStringExpression, sinfo);
        this.value = value;
        this.stype = stype;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }

    isLiteralValueExpression(): boolean {
        return true;
    }
}

class LiteralASCIITypedStringExpression extends Expression {
    readonly value: string;
    readonly stype: TypeSignature;

    constructor(sinfo: SourceInfo, value: string, stype: TypeSignature) {
        super(ExpressionTag.LiteralASCIITypedStringExpression, sinfo);
        this.value = value;
        this.stype = stype;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }

    isLiteralValueExpression(): boolean {
        return true;
    }
}

class LiteralTemplateStringExpression extends Expression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(ExpressionTag.LiteralTemplateStringExpression, sinfo);
        this.value = value;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }
}

class LiteralASCIITemplateStringExpression extends Expression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(ExpressionTag.LiteralASCIITemplateStringExpression, sinfo);
        this.value = value;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }
}

class LiteralTypedPrimitiveConstructorExpression extends Expression {
    readonly value: Expression;
    readonly constype: TypeSignature;

    constructor(sinfo: SourceInfo, value: Expression, constype: TypeSignature) {
        super(ExpressionTag.LiteralTypedPrimitiveConstructorExpression, sinfo);
        this.value = value;
        this.constype = constype;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }

    isLiteralValueExpression(): boolean {
        return true;
    }
}

class AccessFormatInfoExpression extends Expression {
    readonly namespace: string;
    readonly keyname: string;

    constructor(sinfo: SourceInfo, namespace: string, keyname: string) {
        super(ExpressionTag.AccessFormatInfoExpression, sinfo);
        this.namespace = namespace;
        this.keyname = keyname;
    }
}

class AccessEnvValueExpression extends Expression {
    readonly keyname: string;
    readonly valtype: TypeSignature;
    readonly orNoneMode: boolean;

    constructor(sinfo: SourceInfo, keyname: string, valtype: TypeSignature, orNoneMode: boolean) {
        super(ExpressionTag.AccessEnvValueExpression, sinfo);
        this.keyname = keyname;
        this.valtype = valtype;
        this.orNoneMode = orNoneMode;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class AccessNamespaceConstantExpression extends Expression {
    readonly ns: string;
    readonly name: string;

    constructor(sinfo: SourceInfo, ns: string, name: string) {
        super(ExpressionTag.AccessNamespaceConstantExpression, sinfo);
        this.ns = ns;
        this.name = name;
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
}

class AccessVariableExpression extends Expression {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string) {
        super(ExpressionTag.AccessVariableExpression, sinfo);
        this.name = name;
    }
}

class ConstructorPrimaryExpression extends Expression {
    readonly ctype: TypeSignature;
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, ctype: TypeSignature, args: Expression[]) {
        super(ExpressionTag.ConstructorPrimaryExpression, sinfo);
        this.ctype = ctype;
        this.args = args;
    }
}

class ConstructorTupleExpression extends Expression {
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, args: Expression[]) {
        super(ExpressionTag.ConstructorTupleExpression, sinfo);
        this.args = args;
    }
}

class ConstructorRecordExpression extends Expression {
    readonly args: {property: string, value: Expression}[];

    constructor(sinfo: SourceInfo, args: {property: string, value: Expression}[]) {
        super(ExpressionTag.ConstructorRecordExpression, sinfo);
        this.args = args;
    }
}

class ConstructorPCodeExpression extends Expression {
    readonly isAuto: boolean;
    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, isAuto: boolean, invoke: InvokeDecl) {
        super(ExpressionTag.ConstructorPCodeExpression, sinfo);
        this.isAuto = isAuto;
        this.invoke = invoke;
    }
}

class PCodeInvokeExpression extends Expression {
    readonly pcode: string;
    readonly rec: RecursiveAnnotation;
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, pcode: string, rec: RecursiveAnnotation, args: Expression[]) {
        super(ExpressionTag.PCodeInvokeExpression, sinfo);
        this.pcode = pcode;
        this.rec = rec;
        this.args = args;
    }
}

class SpecialConstructorExpression extends Expression {
    readonly rop: "ok" | "err" | "something";
    readonly arg: Expression;

    constructor(sinfo: SourceInfo, rop: "ok" | "err" | "something", arg: Expression) {
        super(ExpressionTag.SpecialConstructorExpression, sinfo);
        this.rop = rop;
        this.arg = arg;
    }
}

class CallNamespaceFunctionOrOperatorExpression extends Expression {
    readonly ns: string;
    readonly name: string;
    readonly rec: RecursiveAnnotation;
    readonly terms: TypeSignature[];
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, ns: string, name: string, terms: TypeSignature[], rec: RecursiveAnnotation, args: Expression[]) {
        super(ExpressionTag.CallNamespaceFunctionOrOperatorExpression, sinfo);
        this.ns = ns;
        this.name = name;
        this.rec = rec;
        this.terms = terms;
        this.args = args;
    }
}

class CallStaticFunctionExpression extends Expression {
    readonly ttype: TypeSignature;
    readonly name: string;
    readonly rec: RecursiveAnnotation;
    readonly terms: TypeSignature[];
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, ttype: TypeSignature, name: string, terms: TypeSignature[], rec: RecursiveAnnotation, args: Expression[]) {
        super(ExpressionTag.CallStaticFunctionExpression, sinfo);
        this.ttype = ttype;
        this.name = name;
        this.rec = rec;
        this.terms = terms;
        this.args = args;
    }
}

class LogicActionAndExpression extends Expression {
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, args: Expression[]) {
        super(ExpressionTag.LogicActionAndExpression, sinfo);
        this.args = args;
    }
}

class LogicActionOrExpression extends Expression {
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, args: Expression[]) {
        super(ExpressionTag.LogicActionOrExpression, sinfo);
        this.args = args;
    }
}

enum PostfixOpTag {
    PostfixAccessFromIndex = "PostfixAccessFromIndex",
    PostfixAccessFromName = "PostfixAccessFromName",

    PostfixIsTest = "PostfixIsTest",
    PostfixAsConvert = "PostfixAsConvert",

    PostfixInvoke = "PostfixInvoke"
}

abstract class PostfixOperation {
    readonly sinfo: SourceInfo;
    readonly op: PostfixOpTag;

    constructor(sinfo: SourceInfo, op: PostfixOpTag) {
        this.sinfo = sinfo;
        this.op = op;
    }
}

class PostfixOp extends Expression {
    readonly rootExp: Expression;
    readonly ops: PostfixOperation[];

    constructor(sinfo: SourceInfo, root: Expression, ops: PostfixOperation[]) {
        super(ExpressionTag.PostfixOpExpression, sinfo);
        this.rootExp = root;
        this.ops = ops;
    }
}

class PostfixAccessFromIndex extends PostfixOperation {
    readonly index: number;

    constructor(sinfo: SourceInfo, index: number) {
        super(sinfo, PostfixOpTag.PostfixAccessFromIndex);
        this.index = index;
    }
}

class PostfixAccessFromName extends PostfixOperation {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string) {
        super(sinfo, PostfixOpTag.PostfixAccessFromName);
        this.name = name;
    }
}

class PostfixIsTest extends PostfixOperation {
    readonly ttest: ITest;

    constructor(sinfo: SourceInfo, ttest: ITest) {
        super(sinfo, PostfixOpTag.PostfixIsTest);
        this.ttest = ttest;
    }
}

class PostfixAsConvert extends PostfixOperation {
    readonly ttest: ITest;

    constructor(sinfo: SourceInfo, ttest: ITest) {
        super(sinfo, PostfixOpTag.PostfixAsConvert);
        this.ttest = ttest;
    }
}

class PostfixInvoke extends PostfixOperation {
    readonly specificResolve: TypeSignature | undefined;
    readonly isRefThis: boolean;
    readonly name: string;
    readonly rec: RecursiveAnnotation;
    readonly terms: TypeSignature[];
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, specificResolve: TypeSignature | undefined, isRefThis: boolean, name: string, terms: TypeSignature[], rec: RecursiveAnnotation, args: Expression[]) {
        super(sinfo, PostfixOpTag.PostfixInvoke);
        this.specificResolve = specificResolve;
        this.isRefThis = isRefThis;
        this.name = name;
        this.rec = rec;
        this.terms = terms;
        this.args = args;
    }
}

class PrefixNotOp extends Expression {
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, exp: Expression) {
        super(ExpressionTag.PrefixNotOpExpression, sinfo);
        this.exp = exp;
    }
}

class PrefixNegateOp extends Expression {
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, exp: Expression) {
        super(ExpressionTag.PrefixNegateOpExpression, sinfo);
        this.exp = exp;
    }
}

class BinAddExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinAddExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class BinSubExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinSubExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class BinMultExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinMultExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class BinDivExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinDivExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class BinKeyEqExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinKeyEqExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class BinKeyNeqExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinKeyNeqExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class NumericEqExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericEqExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class NumericNeqExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericNeqExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class NumericLessExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericLessExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class NumericLessEqExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericLessEqExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class NumericGreaterExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericGreaterExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class NumericGreaterEqExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericGreaterEqExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class BinLogicAndxpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinLogicAndExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class BinLogicOrExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinLogicOrExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class BinLogicImpliesExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinLogicImpliesExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
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
    readonly condflow: {cond: IfTest, value: Expression, binderinfo: string | undefined}[];
    readonly elseflow: { value: Expression, binderinfo: string | undefined };

    constructor(sinfo: SourceInfo, condflow: {cond: IfTest, value: Expression, binderinfo: string | undefined}[], elseflow: { value: Expression, binderinfo: string | undefined }) {
        super(ExpressionTag.IfExpression, sinfo);
        this.condflow = condflow;
        this.elseflow = elseflow;
    }
}

class SwitchExpression extends Expression {
    readonly sval: Expression;
    readonly switchflow: {condlit: LiteralExpressionValue | undefined, value: Expression, bindername: string | undefined}[];

    constructor(sinfo: SourceInfo, sval: Expression, switchflow: {condlit: LiteralExpressionValue | undefined, value: Expression, bindername: string | undefined}[]) {
        super(ExpressionTag.SwitchExpression, sinfo);
        this.sval = sval;
        this.switchflow = switchflow;
    }
}

class MatchExpression extends Expression {
    readonly sval: Expression;
    readonly matchflow: {mtype: TypeSignature | undefined, value: Expression, bindername: string | undefined}[];

    constructor(sinfo: SourceInfo, sval: Expression, flow: {mtype: TypeSignature | undefined, value: Expression, bindername: string | undefined}[]) {
        super(ExpressionTag.MatchExpression, sinfo);
        this.sval = sval;
        this.matchflow = flow;
    }
}

class TaskSelfFieldExpression extends Expression {
    readonly sfield: string;

    constructor(sinfo: SourceInfo, sfield: string) {
        super(ExpressionTag.TaskSelfFieldExpression, sinfo);
        this.sfield = sfield;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class TaskSelfControlExpression extends Expression {
    constructor(sinfo: SourceInfo) {
        super(ExpressionTag.TaskSelfControlExpression, sinfo);
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class TaskSelfActionExpression extends Expression {
    readonly name: string;
    readonly terms: TypeSignature[];
    readonly args: Expression[];
    readonly isSelfRef: boolean;

    constructor(sinfo: SourceInfo, name: string, terms: TypeSignature[], args: Expression[], isSelfRef: boolean) {
        super(ExpressionTag.TaskSelfActionExpression, sinfo);
        this.name = name;
        this.terms = terms;
        this.args = args;
        this.isSelfRef = isSelfRef;
    }
    
    isTaskOperation(): boolean {
        return true;
    }
}

class TaskGetIDExpression extends Expression {
    constructor(sinfo: SourceInfo) {
        super(ExpressionTag.TaskGetIDExpression, sinfo);
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class TaskCancelRequestedExpression extends Expression {
    constructor(sinfo: SourceInfo) {
        super(ExpressionTag.TaskIsCancelRequestedExpression, sinfo);
    }

    isTaskOperation(): boolean {
        return true;
    }
}

enum StatementTag {
    Clear = "[CLEAR]",
    InvalidStatement = "[INVALID]",

    EmptyStatement = "EmptyStatement",

    VariableDeclarationStatement = "VariableDeclarationStatement",
    VariableAssignmentStatement = "VariableAssignmentStatement",

    VariableRetypeStatement = "VariableRetypeStatement",
    ExpressionSCReturnStatement = "ExpressionSCReturnStatement",
    VariableSCRetypeStatement = "VariableSCRetypeStatement",

    ReturnStatement = "ReturnStatement",

    IfElseStatement = "IfElseStatement",
    SwitchStatement = "SwitchStatement",
    MatchStatement = "MatchStatement",

    AbortStatement = "AbortStatement",
    AssertStatement = "AssertStatement", //assert(x > 0)

    DebugStatement = "DebugStatement", //print an arg or if empty attach debugger
    RefCallStatement = "RefCallStatement",

    EnvironmentFreshStatement = "EnvironmentFreshStatement",
    EnvironmentSetStatement = "EnvironmentSetStatement",
    EnvironmentSetStatementBracket = "EnvironmentSetStatementBracket",

    TaskRunStatement = "TaskRunStatement", //run single task
    TaskMultiStatement = "TaskMultiStatement", //run multiple explicitly identified tasks -- complete all
    TaskDashStatement = "TaskDashStatement", //run multiple explicitly identified tasks -- first completion wins
    TaskAllStatement = "TaskAllStatement", //run the same task on all args in a list -- complete all
    TaskRaceStatement = "TaskRaceStatement", //run the same task on all args in a list -- first completion wins

    TaskCallWithStatement = "TaskCallWithStatement",
    TaskResultWithStatement = "TaskResultWithStatement",

    TaskSetStatusStatement = "TaskSetStatusStatement",

    TaskSetSelfFieldStatement = "TaskSetSelfFieldStatement",

    TaskEventEmitStatement = "TaskEventEmitStatement",

    LoggerEmitStatement = "LoggerEmitStatement",
    LoggerEmitConditionalStatement = "LoggerEmitConditionalStatement",

    LoggerLevelStatement = "LoggerLevelStatement",
    LoggerCategoryStatement = "LoggerCategoryStatement",
    LoggerPrefixStatement = "LoggerPrefixStatement",

    UnscopedBlockStatement = "UnscopedBlockStatement",
    ScopedBlockStatement = "ScopedBlockStatement"
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
        super(StatementTag.ScopedBlockStatement, sinfo);
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

class BodyImplementation {
    readonly file: string;
    readonly body: string | ScopedBlockStatement | Expression;

    constructor(file: string, body: string | ScopedBlockStatement | Expression) {
        this.file = file;
        this.body = body;
    }
}

export {
    RecursiveAnnotation,
    ITest, ITestType, ITestLiteral, ITestNone, ITestNothing, ITestSomething, ITestOk, ITestErr,
    ExpressionTag, Expression, LiteralExpressionValue, ConstantExpressionValue, InvalidExpression,
    LiteralNoneExpression, LiteralNothingExpression, LiteralBoolExpression, 
    LiteralIntegralExpression, LiteralFloatPointExpression, LiteralRationalExpression,
    LiteralRegexExpression, LiteralStringExpression, LiteralASCIIStringExpression, LiteralTypedStringExpression, LiteralASCIITypedStringExpression, LiteralTemplateStringExpression, LiteralASCIITemplateStringExpression,
    LiteralTypedPrimitiveConstructorExpression,
    AccessFormatInfoExpression, AccessEnvValueExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression,
    ConstructorPrimaryExpression, ConstructorTupleExpression, ConstructorRecordExpression, 
    ConstructorPCodeExpression, SpecialConstructorExpression,
    CallNamespaceFunctionOrOperatorExpression, CallStaticFunctionExpression,
    LogicActionAndExpression, LogicActionOrExpression,
    PostfixOpTag, PostfixOperation, PostfixOp,
    PostfixAccessFromIndex, PostfixAccessFromName,
    PostfixIsTest, PostfixAsConvert,
    PostfixInvoke, PCodeInvokeExpression,
    PrefixNotOp, PrefixNegateOp,
    BinAddExpression, BinSubExpression, BinMultExpression, BinDivExpression,
    BinKeyEqExpression, BinKeyNeqExpression,
    NumericEqExpression, NumericNeqExpression, NumericLessExpression, NumericLessEqExpression, NumericGreaterExpression, NumericGreaterEqExpression,
    BinLogicAndxpression, BinLogicOrExpression, BinLogicImpliesExpression,
    MapEntryConstructorExpression,
    IfTest,
    IfExpression, SwitchExpression, MatchExpression,
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
    BodyImplementation
};
