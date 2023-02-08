# Bosque Language Expressions

Expressions are a key component in Bosque programming. Thus, Bosque provides a rich set of expressions that support compact data manipulation and expression of intent. A major theme of these operators is to provide simple to reason about semantics that capture common operations with the goal of improving productivity and code quality.


# Table of Contents

- [Pure Bosque Expressions](#pure-bosque-expressions)
    - [1.1 Literals](#1.1-Literals)
    - [1.2 Parameters/Variables/Captures](#1.2-Variables)
    - [1.3 Literal StringOf Expressions](#1.3-StringOf-Expressions)
    - [1.4 Literal Typed Expressions](#1.4-Typed-Expressions)
    - [1.5 Namespace Constants](#1.5-Namespace-Constants)
    - [1.5 Member Constants](#1.6-Member-Constants)
    - [1.7 Tuple Constructors](#1.7-Tuple-Constructors)
    - [1.8 Record Constructors](#1.8-Record-Constructors)
    - [1.9 Entity Constructors](#1.9-Entity-Constructors)
    - [1.10 Special Constructors](#1.10-Special-Constructors)
    - [1.11 Arguments](#1.11-Arguments)
    - [1.12 Namespace and Member Functions](#1.12-Namespace-and-Member-Functions)
    - [1.13 Namespace Operators](#1.13-Operators)
    - [1.14 Lambda Constructors](#1.14-Lambda-Constructors)
- [Bosque Task Expressions](#bosque-task-expressions)
    - [2.1 Format Arguments](#5.1-Arguments)
    - [2.2 Environment Variables](#5.1-Arguments)

# Pure Bosque Expressions

## <a name="1.1-Literals"></a>1.1 Literals
Constant value expressions include `none`, `nothing`, `true`, `false` _Integer_, and _String_:

```none
none     //special none value
nothing  //special nothing value

true     //true boolean literal
false    //false boolean literal

0n       //0 as a Nat
0i       //0 as an Int
-1I      //-1 as an BigInt
0.5f     //0.0 as a Float
5.2d     //5.0 as a Decimal
5/2R     //5/2 as a Rational

"ok"        //string literal
""          //empty string literal
ascii{"ok"} //ascii string literal
/a*b*/      //Regex
```

Most of these literal expressions are familiar from other languages. The numeric literals are strongly typed for each of the numeric types in the language (including BigInt/BigNat and Rationals). Bosque also differentiates string types and literals with the String type and regular quoted strings representing unicode strings. The ASCIIString type and `ascii{...}` enclosed literals are for strings made of only ASCII characters.

# Bosque Task Expressions

