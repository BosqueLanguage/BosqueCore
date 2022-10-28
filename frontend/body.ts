//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo } from "./parser";
import { TypeSignature } from "./type_signature";
import { InvokeDecl, BuildLevel } from "./assembly";
import { BSQRegex } from "./bsqregex";

type RecursiveAnnotation = "yes" | "no" | "cond";

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
    
    LiteralTemplateStringExpression = "LiteralTemplateStringExpression",
    LiteralASCIITemplateStringExpression = "LiteralASCIITemplateStringExpression",
    
    LiteralTypedPrimitiveConstructorExpression = "LiteralTypedPrimitiveConstructorExpression",

    LiteralTypeValueExpression = "LiteralTypeValueExpression",

    AccessFormatInfo = "AccessFormatInfo",
    AccessEnvValue = "AccessEnvValue",
    HasEnvValue = "HasEnvValue",

    AccessNamespaceConstantExpression = "AccessNamespaceConstantExpression",
    AccessStaticFieldExpression = " AccessStaticFieldExpression",
    AccessVariableExpression = "AccessVariableExpression",

    ConstructorPrimaryExpression = "ConstructorPrimaryExpression",
    ConstructorTupleExpression = "ConstructorTupleExpression",
    ConstructorRecordExpression = "ConstructorRecordExpression",
    ConstructorEphemeralValueList = "ConstructorEphemeralValueList",
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
    TaskSelfActionExpression = "TaskSelfActionExpression",
    TaskGetIDExpression = "TaskGetIDExpression",
    TaskGetEventLogExpression = "TaskGetEventLogExpression", //Trim to when this task started
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

class LiteralTemplateStringExpression extends Expression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(ExpressionTag.LiteralTemplateStringExpression, sinfo);
        this.value = value;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }

    isLiteralValueExpression(): boolean {
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

    isLiteralValueExpression(): boolean {
        return true;
    }
}

class LiteralTypedPrimitiveConstructorExpression extends Expression {
    readonly value: string;
    readonly oftype: TypeSignature;
    readonly vtype: TypeSignature;

    constructor(sinfo: SourceInfo, value: string, oftype: TypeSignature, vtype: TypeSignature) {
        super(ExpressionTag.LiteralTypedPrimitiveConstructorExpression, sinfo);
        this.value = value;
        this.oftype = oftype;
        this.vtype = vtype;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }

    isLiteralValueExpression(): boolean {
        return true;
    }
}

class LiteralTypeValueExpression extends Expression {
    readonly vtype: TypeSignature;

    constructor(sinfo: SourceInfo, vtype: TypeSignature) {
        super(ExpressionTag.LiteralTypeValueExpression, sinfo);
        this.vtype = vtype;
    }

    isCompileTimeInlineValue(): boolean {
        return true;
    }

    isLiteralValueExpression(): boolean {
        return true;
    }
}

class AccessFormatInfo extends Expression {
    readonly namespace: string;
    readonly keyname: string;

    constructor(sinfo: SourceInfo, namespace: string, keyname: string) {
        super(ExpressionTag.AccessFormatInfo, sinfo);
        this.namespace = namespace;
        this.keyname = keyname;
    }
}

class AccessEnvValue extends Expression {
    readonly keyname: string;
    readonly valtype: TypeSignature;
    readonly orNoneMode: boolean;

    constructor(sinfo: SourceInfo, keyname: string, valtype: TypeSignature, orNoneMode: boolean) {
        super(ExpressionTag.AccessEnvValue, sinfo);
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
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, args: Expression[]) {
        super(ExpressionTag.ConstructorRecordExpression, sinfo);
        this.args = args;
    }
}

class ConstructorEphemeralValueList extends Expression {
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, args: Expression[]) {
        super(ExpressionTag.ConstructorEphemeralValueList, sinfo);
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

    PostfixIs = "PostfixIs",
    PostfixAs = "PostfixAs",
    PostfixHasIndex = "PostfixHasIndex",
    PostfixHasProperty = "PostfixHasProperty",
    PostfixGetIndexOrNone = "PostfixGetIndexOrNone",
    PostfixGetIndexOption = "PostfixGetIndexOption",
    PostfixGetPropertyOrNone = "PostfixGetPropertyOrNone",
    PostfixGetPropertyOption = "PostfixGetPropertyOption",
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

class PostfixIs extends PostfixOperation {
    readonly istype: TypeSignature;

    constructor(sinfo: SourceInfo, istype: TypeSignature) {
        super(sinfo, PostfixOpTag.PostfixIs);
        this.istype = istype;
    }
}

class PostfixAs extends PostfixOperation {
    readonly astype: TypeSignature;

    constructor(sinfo: SourceInfo, astype: TypeSignature) {
        super(sinfo, PostfixOpTag.PostfixAs);
        this.astype = astype;
    }
}

class PostfixHasIndex extends PostfixOperation {
    readonly idx: number;

    constructor(sinfo: SourceInfo, idx: number) {
        super(sinfo, PostfixOpTag.PostfixHasIndex);
        this.idx = idx;
    }
}

class PostfixHasProperty extends PostfixOperation {
    readonly pname: string;

    constructor(sinfo: SourceInfo, pname: string) {
        super(sinfo, PostfixOpTag.PostfixHasProperty);
        this.pname = pname;
    }
}

class PostfixGetIndexOrNone extends PostfixOperation {
    readonly idx: number;

    constructor(sinfo: SourceInfo, idx: number) {
        super(sinfo, PostfixOpTag.PostfixGetIndexOrNone);
        this.idx = idx;
    }
}

class PostfixGetIndexOption extends PostfixOperation {
    readonly idx: number;

    constructor(sinfo: SourceInfo, idx: number) {
        super(sinfo, PostfixOpTag.PostfixGetIndexOption);
        this.idx = idx;
    }
}

class PostfixGetPropertyOrNone extends PostfixOperation {
    readonly pname: string;

    constructor(sinfo: SourceInfo, pname: string) {
        super(sinfo, PostfixOpTag.PostfixGetPropertyOrNone);
        this.pname = pname;
    }
}

class PostfixGetPropertyOption extends PostfixOperation {
    readonly pname: string;

    constructor(sinfo: SourceInfo, pname: string) {
        super(sinfo, PostfixOpTag.PostfixGetPropertyOption);
        this.pname = pname;
    }
}

class PostfixInvoke extends PostfixOperation {
    readonly specificResolve: TypeSignature | undefined;
    readonly name: string;
    readonly rec: RecursiveAnnotation;
    readonly terms: TypeSignature[];
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, specificResolve: TypeSignature | undefined, name: string, terms: TypeSignature[], rec: RecursiveAnnotation, args: Expression[]) {
        super(sinfo, PostfixOpTag.PostfixInvoke);
        this.specificResolve = specificResolve;
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

class IfExpression extends Expression {
    readonly condflow: {cond: Expression, value: Expression}[];
    readonly elseflow: Expression;

    constructor(sinfo: SourceInfo, condflow: {cond: Expression, value: Expression}[], elseflow: Expression) {
        super(ExpressionTag.IfExpression, sinfo);
        this.condflow = condflow;
        this.elseflow = elseflow;
    }
}

class SwitchExpression extends Expression {
    readonly sval: Expression;
    readonly switchflow: {condlit: LiteralExpressionValue | undefined, value: Expression}[];

    constructor(sinfo: SourceInfo, sval: Expression, switchflow: {condlit: LiteralExpressionValue | undefined, value: Expression}[]) {
        super(ExpressionTag.SwitchExpression, sinfo);
        this.sval = sval;
        this.switchflow = switchflow;
    }
}

class MatchExpression extends Expression {
    readonly sval: Expression;
    readonly matchflow: {mtype: TypeSignature | undefined, value: Expression}[];

    constructor(sinfo: SourceInfo, sval: Expression, flow: {mtype: TypeSignature | undefined, value: Expression}[]) {
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

class TaskSelfActionExpression extends Expression {
    readonly name: string;
    readonly terms: TypeSignature[];
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, name: string, terms: TypeSignature[], args: Expression[]) {
        super(ExpressionTag.TaskSelfActionExpression, sinfo);
        this.name = name;
        this.terms = terms;
        this.args = args;
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

class TaskGetEventLogExpression extends Expression {
    constructor(sinfo: SourceInfo) {
        super(ExpressionTag.TaskGetEventLogExpression, sinfo);
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
    MultiReturnWithDeclarationStatement = "MultiReturnWithDeclarationStatement",
    VariableAssignmentStatement = "VariableAssignmentStatement",
    MultiReturnWithAssignmentStatement = "MultiReturnWithAssignmentStatement",

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

    EventsEmitStatement = "EventsEmitStatement",

    LoggerEmitStatement = "LoggerEmitStatement",
    LoggerEmitConditionalStatement = "LoggerEmitConditionalStatement",

    LoggerControlStatement = "LoggerControlStatement",
    LoggerControlBracketStatement = "LoggerControlBracketStatement",
    LoggerSubLoggerBracketStatement = "LoggerPushSubLoggerBracketStatement",

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

    constructor(sinfo: SourceInfo, name: string, isConst: boolean, vtype: TypeSignature, exp: Expression | undefined) {
        super(StatementTag.VariableDeclarationStatement, sinfo);
        this.name = name;
        this.isConst = isConst;
        this.vtype = vtype;
        this.exp = exp;
    }
}

class MultiReturnWithDeclarationStatement extends Statement {
    readonly isConst: boolean;
    readonly vars: {name: string, pos: number, vtype: TypeSignature /*may be auto*/}[];
    readonly exp: Expression | undefined; //may be undef -- or must be a invoke with a multi-return

    constructor(sinfo: SourceInfo, isConst: boolean, vars: {name: string, pos: number, vtype: TypeSignature /*may be auto*/}[], exp: Expression | undefined) {
        super(StatementTag.MultiReturnWithDeclarationStatement, sinfo);
        this.isConst = isConst;
        this.vars = vars;
        this.exp = exp;
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
}

class MultiReturnWithAssignmentStatement extends Statement {
    readonly vars: {name: string, pos: number}[];
    readonly exp: Expression; //must be an invoke with a multi-return

    constructor(sinfo: SourceInfo, vars: {name: string, pos: number}[], exp: Expression) {
        super(StatementTag.MultiReturnWithAssignmentStatement, sinfo);
        this.vars = vars;
        this.exp = exp;
    }
}

class ReturnStatement extends Statement {
    readonly values: Expression[];

    constructor(sinfo: SourceInfo, values: Expression[]) {
        super(StatementTag.ReturnStatement, sinfo);
        this.values = values;
    }
}

class IfElseStatement extends Statement {
    readonly condflow: {cond: Expression, value: ScopedBlockStatement}[];
    readonly elseflow: ScopedBlockStatement;

    constructor(sinfo: SourceInfo, condflow: {cond: Expression, value: ScopedBlockStatement}[], elseflow: ScopedBlockStatement) {
        super(StatementTag.IfElseStatement, sinfo);
        this.condflow = condflow;
        this.elseflow = elseflow;
    }
}

class SwitchStatement extends Statement {
    readonly sval: Expression;
    readonly switchflow: {condlit: LiteralExpressionValue | undefined, value: ScopedBlockStatement}[];

    constructor(sinfo: SourceInfo, sval: Expression, switchflow: {condlit: LiteralExpressionValue | undefined, value: ScopedBlockStatement}[]) {
        super(StatementTag.SwitchStatement, sinfo);
        this.sval = sval;
        this.switchflow = switchflow;
    }
}

class MatchStatement extends Statement {
    readonly sval: Expression;
    readonly matchflow: {mtype: TypeSignature | undefined, value: ScopedBlockStatement}[];

    constructor(sinfo: SourceInfo, sval: Expression, flow: {mtype: TypeSignature | undefined, value: ScopedBlockStatement}[]) {
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
    readonly value: Expression | undefined;

    constructor(sinfo: SourceInfo, value: Expression | undefined) {
        super(StatementTag.DebugStatement, sinfo);
        this.value = value;
    }
}

class RefCallStatement extends Statement {
    readonly call: PostfixOp;

    constructor(sinfo: SourceInfo, call: PostfixOp) {
        super(StatementTag.RefCallStatement, sinfo);
        this.call = call;
    }
}

class EnvironmentFreshStatement extends Statement {
    readonly assigns: {keyname: string, valexp: Expression}[];

    constructor(sinfo: SourceInfo, assigns: {keyname: string, valexp: Expression}[]) {
        super(StatementTag.EnvironmentFreshStatement, sinfo);
        this.assigns = assigns;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class EnvironmentSetStatement extends Statement {
    readonly assigns: {keyname: string, valexp: Expression | undefined}[];

    constructor(sinfo: SourceInfo, assigns: {keyname: string, valexp: Expression}[]) {
        super(StatementTag.EnvironmentSetStatement, sinfo);
        this.assigns = assigns;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class EnvironmentSetStatementBracket extends Statement {
    readonly assigns: {keyname: string, valexp: Expression}[];
    readonly block: UnscopedBlockStatement | ScopedBlockStatement;
    readonly isFresh: boolean;

    constructor(sinfo: SourceInfo, assigns: {keyname: string, valexp: Expression}[], block: UnscopedBlockStatement | ScopedBlockStatement, isFresh: boolean) {
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
    readonly vtrgt: string;
    readonly task: TypeSignature;
    readonly taskargs: {argn: string, argv: Expression}[];
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, vtrgt: string, task: TypeSignature, taskargs: {argn: string, argv: Expression}[], args: Expression[]) {
        super(StatementTag.TaskRunStatement, sinfo);
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
    readonly vtrgts: string[];
    readonly tasks: TypeSignature[];
    readonly taskargs: {argn: string, argv: Expression}[];
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, vtrgts: string[], tasks: TypeSignature[], taskargs: {argn: string, argv: Expression}[], args: Expression[]) {
        super(StatementTag.TaskMultiStatement, sinfo);
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
    readonly vtrgt: string;
    readonly task: TypeSignature[];
    readonly taskargs: {argn: string, argv: Expression}[];
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, vtrgt: string, task: TypeSignature[], taskargs: {argn: string, argv: Expression}[], args: Expression[]) {
        super(StatementTag.TaskDashStatement, sinfo);
        this.vtrgt = vtrgt;
        this.task = task;
        this.taskargs = taskargs;
        this.args = args;
    }

    isTaskOperation(): boolean {
        return true;
    }
}


class TaskAllStatement extends Statement {
    readonly vtrgt: string;
    readonly task: TypeSignature;
    readonly taskargs: {argn: string, argv: Expression}[];
    readonly arg: Expression;

    constructor(sinfo: SourceInfo, vtrgt: string, task: TypeSignature, taskargs: {argn: string, argv: Expression}[], arg: Expression) {
        super(StatementTag.TaskAllStatement, sinfo);
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
    readonly vtrgt: string;
    readonly task: TypeSignature;
    readonly taskargs: {argn: string, argv: Expression}[];
    readonly arg: Expression;

    constructor(sinfo: SourceInfo, vtrgt: string, task: TypeSignature, taskargs: {argn: string, argv: Expression}[], arg: Expression) {
        super(StatementTag.TaskRaceStatement, sinfo);
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

class EventsEmitStatement extends Statement {
    readonly arg: Expression;

    constructor(sinfo: SourceInfo, arg: Expression) {
        super(StatementTag.EventsEmitStatement, sinfo);
        this.arg = arg;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

enum LoggerLevel {
    fatal = "fatal",
    error = "error",
    warn = "Warn",
    info = "info",
    detail = "detail",
    debug = "debug",
    trace = "trace"
}

class LoggerEmitStatement extends Statement {
    readonly level: LoggerLevel;
    readonly msg: AccessFormatInfo;
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, level: LoggerLevel, msg: AccessFormatInfo, args: Expression[]) {
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
    readonly msg: AccessFormatInfo;
    readonly args: Expression[];

    constructor(sinfo: SourceInfo, level: LoggerLevel, cond: Expression, msg: AccessFormatInfo, args: Expression[]) {
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


class LoggerControlStatement extends Statement {
    constructor(sinfo: SourceInfo) {
        super(StatementTag.LoggerControlStatement, sinfo);
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class LoggerControlBracketStatement extends Statement {
    readonly block: UnscopedBlockStatement | ScopedBlockStatement;

    constructor(sinfo: SourceInfo, block: UnscopedBlockStatement | ScopedBlockStatement) {
        super(StatementTag.LoggerControlBracketStatement, sinfo);
        this.block = block;
    }

    isTaskOperation(): boolean {
        return true;
    }
}

class LoggerSubLoggerBracketStatement extends Statement {
    readonly msg: AccessFormatInfo;
    readonly block: UnscopedBlockStatement | ScopedBlockStatement;

    constructor(sinfo: SourceInfo, msg: AccessFormatInfo, block: UnscopedBlockStatement | ScopedBlockStatement) {
        super(StatementTag.LoggerSubLoggerBracketStatement, sinfo);
        this.msg = msg;
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
    readonly id: string;
    readonly file: string;
    readonly body: string | ScopedBlockStatement | Expression;

    constructor(bodyid: string, file: string, body: string | ScopedBlockStatement | Expression) {
        this.id = bodyid;
        this.file = file;
        this.body = body;
    }
}

export {
    RecursiveAnnotation,
    ExpressionTag, Expression, LiteralExpressionValue, ConstantExpressionValue, InvalidExpression,
    LiteralNoneExpression, LiteralNothingExpression, LiteralBoolExpression, 
    LiteralIntegralExpression, LiteralFloatPointExpression, LiteralRationalExpression,
    LiteralRegexExpression, LiteralStringExpression, LiteralASCIIStringExpression, LiteralTypedStringExpression, LiteralTemplateStringExpression, LiteralASCIITemplateStringExpression,
    LiteralTypedPrimitiveConstructorExpression, LiteralTypeValueExpression,
    AccessFormatInfo, AccessEnvValue, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression,
    ConstructorPrimaryExpression, ConstructorTupleExpression, ConstructorRecordExpression, ConstructorEphemeralValueList, 
    ConstructorPCodeExpression, SpecialConstructorExpression,
    CallNamespaceFunctionOrOperatorExpression, CallStaticFunctionExpression,
    LogicActionAndExpression, LogicActionOrExpression,
    PostfixOpTag, PostfixOperation, PostfixOp,
    PostfixAccessFromIndex, PostfixAccessFromName,
    PostfixIs, PostfixAs, PostfixHasIndex, PostfixHasProperty, PostfixGetIndexOrNone, PostfixGetIndexOption, PostfixGetPropertyOrNone, PostfixGetPropertyOption,
    PostfixInvoke, PCodeInvokeExpression,
    PrefixNotOp, PrefixNegateOp,
    BinAddExpression, BinSubExpression, BinMultExpression, BinDivExpression,
    BinKeyEqExpression, BinKeyNeqExpression,
    NumericEqExpression, NumericNeqExpression, NumericLessExpression, NumericLessEqExpression, NumericGreaterExpression, NumericGreaterEqExpression,
    BinLogicAndxpression, BinLogicOrExpression, BinLogicImpliesExpression,
    MapEntryConstructorExpression,
    IfExpression, SwitchExpression, MatchExpression,
    TaskSelfFieldExpression, TaskSelfActionExpression, TaskGetIDExpression, TaskGetEventLogExpression, TaskCancelRequestedExpression,
    StatementTag, Statement, InvalidStatement, EmptyStatement,
    VariableDeclarationStatement, MultiReturnWithDeclarationStatement, VariableAssignmentStatement, MultiReturnWithAssignmentStatement, 
    ReturnStatement,
    IfElseStatement, AbortStatement, AssertStatement, DebugStatement, RefCallStatement,
    SwitchStatement, MatchStatement,
    EnvironmentFreshStatement, EnvironmentSetStatement, EnvironmentSetStatementBracket,
    TaskRunStatement, TaskMultiStatement, TaskDashStatement, TaskAllStatement, TaskRaceStatement,
    TaskCallWithStatement, TaskResultWithStatement,
    TaskSetStatusStatement, TaskSetSelfFieldStatement,
    EventsEmitStatement, LoggerEmitStatement, LoggerEmitConditionalStatement, LoggerControlStatement, LoggerControlBracketStatement, LoggerSubLoggerBracketStatement,
    UnscopedBlockStatement, ScopedBlockStatement, 
    BodyImplementation
};
