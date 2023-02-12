# Bosque Language Expressions

Expressions are a key component in Bosque programming. Thus, Bosque provides a rich set of expressions that support compact data manipulation and expression of intent. A major theme of these operators is to provide simple to reason about semantics that capture common operations with the goal of improving productivity and code quality.

# Table of Contents

- Pure Bosque Expressions
    1. Literals
    2. Parameters/Variables/Captures
    3. Literal StringOf Expressions
    4. Literal Typed Expressions
    5. Namespace Constants
    6. Member Constants
    7. Tuple Constructors
    8. Record Constructors
    9. Entity Constructors
    10. Special Constructors
    11. Collection Constructors
    12. Namespace and Member Functions
    13. Namespace Operators
    14. Logical And/Or 
    15. Tuple Index Access
    16. Record Property Access
    17. Field Access
    18. ITest Check
    19. ITest As and Conversion
    20. Method Call
    21. Method Call with Ref
    22. Method Call Virtual
    23. Prefix Boolean Not
    24. Prefix Negation
- Bosque Expression Components
    1. ITests
    2. Arguments
    3. Binders
    4. Lambdas
    5. Direct Literals
- Bosque Task Expressions
    1. Format Arguments
    2. Environment Variables

# Pure Bosque Expressions

## Literals
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


## Parameters/Variables/Captures
Variables in Bosque are of the form `[_a-z][_a-zA-Z0-9]`. Local variables can be declared using a `let` for immutable bindings or `var` for mutable bindings. Parameters are 
always immutable -- except for `this` in a `ref` method and `self` in a `ref` method or `action`. Variables and parameters can be captured by lambda constructors and are immutable within the lambda scope. As Bosque is _referentially transparent_ there are no modes that are needed for the lambda captures. See also [let/var bindings](statements.md).

## Literal StringOf Expressions
Typed strings provide a direct way to expose otherwise latent information about the data that is stored in a string -- e.g. a zipcode, CSS attribute, part ID, etc. The format information is given by a `Validator` type (see [Validator Types](types.md)) and a conforming string literal.

```none
typedecl ZipcodeUS = /[0-9]{5}(-[0-9]{4})?/;
...
"98052"ZipcodeUS
"98052-0001"ZipcodeUS

"abc123"ZipcodeUS //type error
```

## Literal Typed Expressions
Typed literals provide a way to express structured information on other primitive data types, such as Bool, Int, Decimal, String, StringOf, UUID, DateTime, etc. These types are created using `typedecl` syntax (see [Type Aliases](types.md)) and literal values are constructed with the form `<literal>_<Type>`. Examples include:

```none
```

## Namespace Constants
Constant values can be declared in `namespace` scopes (see [Namespaces](structures.md)). These constants can be used in expressions with the syntax `<namespace>::<constant>` and, when they refer to `literal` values they are then valid `literal` expressions as well (so can be used in switch statements etc.).

```none
namespace Ns;

const c1: Int = 1i;
const c2: Int = 2i + Ns::c1;

Ns::c1 //1i and is a literal expression
Ns::c2 //3i but not a literal expression
```

## Member Constants
Constant values can be declared in Object-Oriented scopes as well (see [types](types.md)). These constants can be used in expressions with the syntax `<typename>::<constant>` and, when they refer to `literal` values they are then valid `literal` expressions as well (so can be used in switch statements etc.).

In contrast to many languages `const` declarations are dynamically resolved. Thus, any subtype will also have access to the `const` declarations of the supertype. This allows for a more flexible and natural way to define common constants for a set of types.

```none
concept Foo {
    const c1: Int = 1i;
}

entity Bar provides Foo {
    const c2: Int = 3i + Bar::c1;
    const c3: Int = Foo::c1;
}

Foo::c1 //1i and is a literal expression
Bar::c1 //1i as well

Bar::c2 //3i but not a literal expression
Bar::c3 //1i and a literal expression as well (transitively)
```

## Tuple Constructors
Bosque tuples are constructed using a basic syntax of `[e1, e2, ..., em]` where the `ei` are expressions. The type of the tuple is implied by the types of the `ei` expressions. Tuples cannot be subtypes of each other (see [tuple types](types.md)). Instead the [type inference system](types.md) will coerce the individual `ei` expressions to the needed types before constructing the tuple if it can.

Basic Tuples:
```none
[] //empty tuple
[1i, 2i, 3i] //tuple of 3 Ints
[1i, [true]] //tuple of Int and another tuple
```

Tuple with Inference:
```none
function foo(): [Int, Boolean?] {
    return [3, true]; //expression types are Int and Boolean but inference converts to Int and Boolean?
}
```

## Record Constructors
Bosque records are constructed using a basic syntax of `{p1=e1, p2=e2, ..., pm=em}` where the `pi=ei` are property/expression bindings. The type of the record is implied by the types of the `pi=ei` expressions. Records cannot be subtypes of each other (see [record types](types.md)). Instead the [type inference system](types.md) will coerce the individual `ei` expressions to the needed types before constructing the record if it can.

Basic Records:
```none
{} //empty record
{f=1i, g=2i} //record of 2 Ints (f and g)
{f=1i, g={h=true}} //record of Int and another record
```

Record with Inference:
```none
function foo(): {f: Int, g: Boolean?} {
    return {f=3, g=true}; //expression types are Int and Boolean but inference converts to Int and Boolean?
}
```

## Entity Constructors
Object-oriented programming in Bosque is centered around _Concepts_ and _Entities_ (see [Types](types.md)) which roughly correspond to objects and abstract classes/interfaces in other languages. These types can be defined explicitly using `entity` or `concept` declarations and are also implicitly created via `typedecl` or `datatype` declarations. Examples of simple OO construction are:
```none
entity Foo {
    field f: Int;
}
Foo{3i} //constructs a Foo where field f has value 3i

concept Bar {
    field g: Int;
}
entity Baz provides Bar {
    field h: Nat;
}
Baz{3i, 4n} //constructs a Baz where field g has value 3i and field h has value 4n

concept Named {
    field name: String;
}
entity Qux provides Named, Bar {
}
Qux{"bob", 3i} //constructs a Qux where field name has value "bob" and field g has value 3i
```

Similarly object-oriented types can be defined as `typedecls` or `datatypes` and constructed using the same syntax. For example:
```none
typedecl Fahrenheit = Int;
Fahrenheit{32i} //constructs a Fahrenheit value for freezing

typedecl SystemID = /[A-Z]{3}-[0-9]+/;
typedecl PartID = StringOf<SystemID>;

"X-52"_PartID    //fails the invariant on the string
"ABC-123"_PartID //constructs a literal PartID value with the value ABC-123
PartID{SystemID::from("ABC-123")} //constructs a PartID value with the value ABC-123

datatype BoolOp using {
    line: Nat
} of
LConst { val: Bool }
| NotOp { arg: BoolOp }
| AndOp { larg: BoolOp, rarg: BoolOp }
| OrOp { larg: BoolOp, rarg: BoolOp }
;

NotOp{5n LConst{1n, false}} //constructs a NotOp value
```

In all cases they support the use of _data invariants_ of various types (mostly using the `invariant` [member](types.md)). The invariants are checked on construction and result in an error when violated.
```none
concept Bar {
    field g: Int;

    invariant $g > 0i;
}
concept Named {
    field name: String;

    invariant $name !== "";
}
entity Qux provides Named, Bar {
    field h: Int;

    invariant $g < $h;
}
Qux{"", 3i, 10i} //fails invariant $name !== ""
Qux{"bob", 0i, 10i} //fails invariant $g > 0
Qux{"bob", 4i, 2i} //fails invariant $g < $h
Qux{"bob", 4i, 10i} //ok

typedecl Percentage = Nat & {
    invariant $value <= 100n;
}
Percentage{101n} //fails invariant $value <= 100n
Percentage{99n}  //ok
``` 

## Special Constructors
The `Option<T>` and `Result<T, E>` types have special constructor support. In addition to the regular `Something<Int>{3i}` constructor forms they provide short and type inferred forms with the syntax `some(e)`, `ok(e)`, `err(e)` and `result(e)` where `e` is an expression. These forms will infer the appropriate template types and convert the expressions as needed. The `result(e)` type will also insert conversions between compatible result types and construction of result objects from values (see issue #1).

Examples of these special forms include:
```none
let x: Option<Int> = some(3i); //x is a Some<Int> with value 3i
let y: Option<Int?> = some(5i); //y is a Some<Int?> with value 5i

function foo(): Result<Int, String> {
    return ok(3i); //returns a Result<Int, String> with value 3i
}

function bar(): Result<Int, String> {
    return err("error"); //returns a Result<Int, String> with error "error"
}
function baz(): Result<Int, String?> {
    return result(bar()); //returns a Result<Int, String?> by converting the return of bar into the correct type
}
```

## Collection Constructors
Bosque provides a range of standard collections, including `List<T>`, `Stack<T>`, `Queue<T>`, `Set<T>`, and `Map<K, V>` (more details are available in the collections docs).These collections can be constructed using syntax similar to the entity constructors (but generalized since they may have many elements). For example:
```none
List<Bool>{} //constructs an empty List<Bool>
List<Int>{1i, 2i, 3i} //constructs a List<Int> with values 1i, 2i, 3i

Map<Int, String>{} //constructs an empty Map<Int, String>
Map<Int, String>{MapEntry<Int, String>{1i, "one"}, MapEntry<Int, String>{2i, "two"}} //constructs a Map<Int, String> with entries 1i->"one" and 2i->"two"
```

Map (Set) constructors must have `KeyType` values as keys (see [types](types.md)) also do validity checking that there are no duplicate keys. Maps also provide a shorthand syntax for constructing `MapEntry` values:
```none
Map<[Int, Int], String>{} //Type error [Int, Int] is not a KeyType
Map<Int, String>{MapEntry<Int, String>{1i, "one"}, MapEntry<Int, String>{1i, "two"}} //Error duplicate key values

Map<Int, String>{1i => "one", 2i => "two"} //constructs a Map<Int, String> with entries 1i->"one" and 2i->"two"
```

## Namespace and Member Functions
Bosque supports simple functions defined at a namespace scope or within a type scope. Namespace functions can be called with or without a namespace qualifier (for functions defined in ths same namespace where they are use). Functions defined in a type scope must always be called with the type qualifier (even within the same type scope).

```none
namespace Main;

function f(x: Int, y: Int): Int {
    return x + y;
}

f(1i, 2i) //returns 3i
Main::f(1i, 2i) //returns 3i

entity Foo {
    function f(x: Int, y: Int): Int {
        return x - y;
    }
}

Foo::f(1i, 2i) //returns -1i
```

## Namespace Operators
[TODO] Operators allow multiple dynamic dispatch functions to be defined. They are currently partially implemented (see issue #13). 

The declaration of an operator is a virtual or abstract definition which may have Concept or Union typed arguments. Each dispatch implementation must have only unique (non-entity and non-union) typed arguments and must be defined in the same namespace as the operator (this prevents resolution ambiguity and accidental overloading). Arguments may also use literal value dispatch on one argument in the operator. If these are used then each dispatch implementation must provide a literal value for this argument.

## Logical And/Or 
Bosque provides pure logical and/or as expressions of the form `/\(e1, ..., ek)` and `\/(e1, ..., ek)`. These evaluate all arguments *before* computing the logical result, e.g. they do not short circuit evaluation. 

Examples include:
```none
/\(true) //error -- should not be empty or have single argument
/\(true, 1i == 1i, 2i == 2i) //returns true
/\(true, false) //returns false

\/(true) //error -- should not be empty or have single argument
\/(false, 1i == 1i, 2i == 3i) //returns true
\/(false, 2i == 3i) //returns false
```

## Tuple Index Access
Tuples are indexed using the syntax `e.i` where `i` is a literal integer value. 

[TODO] Currently only expressions with a unique tuple type can be accessed. Adding virtual tuple access is an open issue and also impacts spread arguments.

Examples of tuple access include:
```none
[1n, 2i].0 //returns 1n
[1n, 2i].1 //returns 2i
[[1n, 2i], 3i].0.1 //returns 2i

[1n, 2i].2 //error tuple has no index 2
```

## Record Property Access
Records properties are accessed using the syntax `e.p` where `p` is a property name. 

[TODO] Currently only expressions with a unique record type can be accessed. Adding virtual record access is an open issue and also impacts spread arguments.

Examples of record access include:
```none
{f=1n, g=2i}.f //returns 1n
{f=1n, g=2i}.g //returns 2i
{f={g=1n, h=2i}, q=3i}.f.h //returns 2i

{f=1n, g=2i}.h //error record has no property h
```

## Field Access
## ITest Check
## ITest As and Conversion
## Method Call
## Method Call with Ref
## Method Call Virtual
## Prefix Boolean Not
## Prefix Negation

# Bosque Expression Components

## ITests

# Bosque Task Expressions

