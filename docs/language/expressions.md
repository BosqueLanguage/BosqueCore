# Bosque Language Expressions

Expressions are a key component in Bosque programming. Thus, Bosque provides a rich set of expressions that support compact data manipulation and expression of intent. A major theme of these operators is to provide simple to reason about semantics that capture common operations with the goal of improving productivity and code quality.

# Table of Contents

- Pure Bosque Expressions
    1. Literals
      - None
      - Boolean
      - Int/Nat and BigInt/BigNat
      - Float, Decimal, Rational, and Complex
      - Decimal Degree and Latitude/Longitude
      - Byte, CChar, and UnicodeChar
      - UUIDv4 and UUIDv7
      - SHAHash
      - TZDateTime, TAIDateTime, PlainDate, and PlainTime
      - LogicalTime
      - ISOTimeStamp
      - DeltaDataTime, DeltaISOTimeStamp, DeltaSeconds, DeltaLogicalTime
      - ByteBuffer
      - String and CString
      - Regex and CRegex
      - Path, PathFragment, and Glob
    2. Literal StringOf Expressions
    2. Literal Format String Expressions
    3. Literal Typed Expressions
    4. Parameters/Variables/Captures
    5. Namespace and Member Constants
    6. Enumerations
    8. Entity Constructors
    7. EList Constructors
    10. Special Constructors
    11. Collection Constructors
    12. Namespace and Member Functions
    13. Namespace Operators
    14. EList Index Access
    16. Field Access
    18. ITest Check
    19. ITest As and Conversion
    20. Method Call
    21. Method Call Virtual
    22. Prefix `!` operator
    23. Prefix `-` operator
    24. Binary arithmetic, `+`/`-`/`*`/`/` operators
    25. Binary comparison `==`/`!=`/`<`/`<=`/`>`/`>=` operators
    26. Binary KeyType equality `===`/`!==` operators
    27. Logic `&&`/`||` operators
    28. MapEntry Constructor `=>` operator
- Bosque Expression Components
    1. ITests
      - negation and binding
      - Option -> none & some
      - Result -> ok & fail
      - APIResult -> success, error, rejected, failed
      - Concept Type
      - Datatype
    2. Arguments
    3. Binders
    4. Lambdas
    5. Direct Literals
    6. Regular Expressions
    7. Path Expressions
- Bosque Task Expressions
    1. Environment Variables
    2. Task Information

# Pure Bosque Expressions

## Literals

### Unique Values
The keywords `none`, `true`, `false` are the unique literal representations for the `None`, and `Boolean` types. 

```none
none     %%special none value

true     %%true boolean literal
false    %%false boolean literal
```

### Integral Numbers
The literals for `Nat`, `Int`, `ChkNat`, `ChkInt` are of the form `[+-][0-9]+[n|i|N|I]`. The `n`/`i` suffix is used for `Nat` and `Int` values, the `N`/`I` suffix is used for `ChkNat` and `ChkInt` values. Some examples include:

```none
0n       %%0 as a Nat
0i       %%0 as an Int
-1I      %%-1 as an ChkInt
100N     %%100 as a ChkNat
```

Nat and ChkNat represent non-negative numbers only -- thus leading `-` signs are an error. Int and Nat represent numbers in the range from -(2^62 - 1) to (2^62 - 1) and 0 to (2^62 - 1). As these ranges are symmetric,  negation and Nat -> Int conversion is always safe. All operations on these types are checked for overflow/underflow and division by zero.

ChkInt and ChkNat have 2x the range of the standard Int and Nat types -- from -(2^124 - 1) to (2^124 - 1) and 0 to (2^126 - 1). As with Int/Nat these ranges are symmetric, negation and ChkNat -> ChkInt conversion is always safe. All operations on these types are saturating to a invalid flag `ChkInt::npos` (`ChkNat::npos`) for overflowing calculations. As opposed to traditional NaN values these can be compared for equality and ordering (with `npos` being larger than all valid values). However, division by zero and `ChkNat` underflow are still errors.

For literals duplicate signs are an error, and the sign is _explicitly_ part of the number literal -- thus `-2i` and `-(2i)` are not the same semantically which is important for literal typedecl values such as `-2i<Fo>` where this is the literal `-2i` as a `Foo` _not_ the value `2i<Foo>` negated. 

### Real Approximation Numbers
-- In Progress --
The literals for `Float` and `Decimal` are of the form `[+-][0-9]+[.][0-9]+[f|d]`. The `f` suffix is used for `Float` values, which are 64bit IEEE values (excluding NaN and Infinities), the `d` suffix is used for base-10 `Decimal` floating point values (also excluding NaN and Infinities). Literal `Rational` values are of the form `[+-][0-9]+(/[0-9]?R` and 
represent approximate rational values -- with a `BigInt` numerator and a `Nat` denominator. So infinite range and precision of up to 1/(2^63) which is rounded (TODO: what mode).

Some examples include:
```none
0.5f     %%0.0 as a Float
5.2d     %%5.0 as a Decimal
5/2R     %%5/2 as a Rational
```

### Common Special Numerics
-- In Progress --
A `DecimalDegree` literal is of the form `[+-][0-9]+[.][0-9]+dd` and represents a decimal degree value in the range [-180.0, 180.0]. A `LatLongCoordinate` literal is of the form `[+-]DDlatDDlong` and represents a pair of decimal degree values for latitude and longitude in the form `<latitude><longitude>` where latitude is in the range [-90.0, 90.0] and longitude is in the range [-180.0, 180.0]. 

Some examples include:
```none
40.42dd               %%40.42 as a DecimalDegree
-3.7dd                %%-3.7 as a DecimalDegree
38.03lat-84.49long    %%LatLongCoordinate for Lexington, KY
```

### Raw Data Literals
-- In Progress --
The literals for `Byte` and `ByteBuffer` are based on `Byte` values. A `Byte` literal is of the form `0x[a-zA-Z0-9]{1,2}b` and represents an 8-bit unsigned integer value in the range [0, 255]. A `ByteBuffer` literal is a sequence of hexidecimal values separated by commas. 

Some examples include:
```none
0x0                        %%0 as a Byte
0xFF                       %%255 as a Byte
0x{0x0,0x1,0x2,0x3,0x4,0x5,0x6,0x7,0x8,0x9,0xA}  %%ByteBuffer with 11 bytes
```

### UUIDv4 and UUIDv7 Literals
-- In Progress --
UUIDv4 literals are of the form `uuid4{xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx}` where `x` is a hexidecimal digit and `y` is one of `8`, `9`, `A`, or `B`. UUIDv7 literals are of the form `uuid7{xxxxxxxx-xxxx-7xxx-yxxx-xxxxxxxxxxxx}` where `x` is a hexidecimal digit and `y` is one of `8`, `9`, `A`, or `B`. 

Some examples include:
```none
uuid4{550e8400-e29b-41d4-a716-446655440000}  %%UUIDv4
uuid7{550e8400-e29b-71d4-a716-446655440000}  %%UUIDv7
```

### SHAHash Literals
-- In Progress --
SHAHash literals are of the form `sha3{<hexstring>}` where the hash function use to compute the value is SHA3 256 with  and `<hexstring>` is the hexidecimal representation of the hash value.


### Data and Time Literals
-- In Progress --
Time and time values are complex, as such, Bosque provides a number of representations designed to appropriately capture common use cases. These include:
- `TZDateTime` literals of the form `YYYY-MM-DDTHH:MM:SS[Zone]` representing a date/time with a timezone in ISO 8601 format where timezone is a string enclosed in `{...}` or is a standard `[A-Z]+` timezone abbreviation.
- `TAIDateTime` literals of the form `YYYY-MM-DDTHH:MM:SS` representing a TAI (International Atomic Time) date/time at UTC.
- `PlainDate` literals of the form `YYYY-MM-DD` representing a calendar date without any time (or timezone) information.
- `PlainTime` literals of the form `HH:MM:SS` representing a time without any date (or timezone) information.
- `ISOTimeStamp` literals of the form `YYYY-MM-DDTHH:MM:SS.sssZ` an ISO 8601 timestamp (including milliseconds).

In addition, Bosque provides a logical tick-time representation as a monotonic counter:
- `LogicalTime` literals of the form `Tl` where `T` is a positive numeric value.

### Time and Date Delta Literals
-- In Progress --
In addition to providing support for date/time instant literals, Bosque also provides delta representations for expressing time differences (or intervals) by adding a 
sign `[+-]` specifier to indicate the direction of the delta. 

These include:
- `DeltaDateTime` literals of the form `[+-]YYYY-MM-DDTHH:MM:SS` representing a date/time delta with a timezone in ISO 8601 format and can be computed/applied to both timezone and TAI representations -- there are also date and time only variants of `[+-]YYYY-MM-DD` and `[+-]HH:MM:SS`.
- `DeltaISOTimeStamp` literals of the form `[+-]YYYY-MM-DDTHH:MM:SS.sssZ` an ISO 8601 timestamp delta (including milliseconds).
- `DeltaSeconds` literals of the form `[+-]N.sss` representing a delta in seconds (including milliseconds).
- `DeltaLogicalTime` literals of the form `[+-]Nl` where `N` is a positive numeric value representing a delta in logical time ticks.

### String Literals
Bosque provides both explicitly Unicode `String` values (and chars `UnicodeChar`) and C-style `CString` values (and corresponding `CChar` values) which are limited to printable ASCII values. Unicode string literals are enclosed in double quotes `"` and support numeric escape sequences of the form `%xYY;` where YY is the codepoint value in hexidecimal. Special named escapes are supported as well as described in the [BREX](https://github.com/BosqueLanguage/BREX) library. `CString` literals are enclosed in single quotes `'` and support escape sequences as well.

String literals by default can be multi-line and preserve whitespace using trailing backslashes `\` to indicate line continuation -- see [BREX](https://github.com/BosqueLanguage/BREX) for more details.

## Regular Expression Literals
To match strings Bosque provides regular expression literals for both Unicode strings and C-style strings. These literals are enclosed in slashes `/.../` for Unicode regular expressions, `/.../c` for regular expressions over `CString` values, and support the regex syntax described in [BREX](https://github.com/BosqueLanguage/BREX).

## Path Literals
-- In Progress --
In addition to string literals Bosque also provides path, path fragment, and glob literals for working with URI style resource paths. These literals are enclosed in backslashres `\...\`. They support arbitrary resource types and standard URI path syntax. 

Examples include:
```none
\file:/path/to/resource
f\resource/fragment\
g\file:/path/**/glob/*.ext\

\customresource:resource/path\
```

## Format String and Path Literals
-- In Progress --
Strings and paths can be format literals as well. These are prefixed with a `$` and support embedded typed format components enclosed in `${...}`. These components include an argument index (starting at `0`) and the types of the format components can be specialized with an optional type after a colon `:`.

```none
$"Hello ${0}"
$"Value is ${0:CStringOf<Temperature>}"
$\file:/path/to/${0}/resource
```

## Literal Typed Expressions
Typed literals provide a way to express structured information on other primitive data types, such as `Bool`, `Int`, `ChkInt`, `Decimal`, `UUIDv4`, `DateTime`, etc. These types are created using `type` syntax and literal values are constructed with the form `literal<Type>`. 

An example of a simple type alias creation is:
```none
type Fahrenheit = Int;
123i<Fahrenheit>

type UserID = UUIDv4;
uuid4{4f63660e-e0ad-4d18-93c6-f684faf11e65}<UserID>
```

These typed literals are strongly typed and do *not* auto-decay to their underlying primitive types. The underlying values can be accessed using the `.value` member. Additionally, invariants, methods, etc. can be associated with the new types via the `& { ... }` syntax. For example:
```none
type Percentage = Float & { 
    invariant 0.0f <= $value && $value <= 100.0f;
}

## Literal Typed String/Path Expressions
-- In Progress --
Typed strings provide a direct way to expose otherwise latent information about the data that is stored in a string -- e.g. a zipcode, CSS attribute, part ID, etc. The format information is given by a `Validator` type (see [Validator Types](types.md)) and a conforming string literal.

```none
typedecl ZipcodeUS = /[0-9]{5}(-[0-9]{4})?/;
...
"98052"ZipcodeUS
"98052-0001"ZipcodeUS

"abc123"ZipcodeUS %%type error
```

## Parameters/Variables/Captures
-- In Progress --
Variables in Bosque are of the form `[_a-z][_a-zA-Z0-9]`. Local variables can be declared using a `let` for immutable bindings or `var` for mutable bindings. Parameters are always immutable -- except for `this` in a `ref` method and `self` in a `ref` method or `action`. Variables and parameters can be captured by lambda constructors and are immutable within the lambda scope. As Bosque is _referentially transparent_ there are no modes that are needed for the lambda captures. See also [let/var bindings](statements.md).

## Namespace Constants
-- In Progress --
Constant values can be declared in `namespace` scopes (see [Namespaces](structures.md)). These constants can be used in expressions with the syntax `<namespace>::<constant>` and, when they refer to `literal` values they are then valid `literal` expressions as well (so can be used in switch statements etc.).

```none
namespace Ns;

const c1: Int = 1i;
const c2: Int = 2i + Ns::c1;

Ns::c1 %%1i and is a literal expression
Ns::c2 %%3i but not a literal expression
```

## Member Constants
-- In Progress --
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

Foo::c1 %%1i and is a literal expression
Bar::c1 %%1i as well

Bar::c2 %%3i but not a literal expression
Bar::c3 %%1i and a literal expression as well (transitively)
```

## Entity Constructors
-- In Progress --
Object-oriented programming in Bosque is centered around _Concepts_ and _Entities_ (see [Types](types.md)) which roughly correspond to objects and abstract classes/interfaces in other languages. These types can be defined explicitly using `entity` or `concept` declarations and are also implicitly created via `typedecl` or `datatype` declarations. Examples of simple OO construction are:
```none
entity Foo {
    field f: Int;
}
Foo{3i} %%constructs a Foo where field f has value 3i

concept Bar {
    field g: Int;
}
entity Baz provides Bar {
    field h: Nat;
}
Baz{3i, 4n} %%constructs a Baz where field g has value 3i and field h has value 4n

concept Named {
    field name: String;
}
entity Qux provides Named, Bar {
}
Qux{"bob", 3i} %%constructs a Qux where field name has value "bob" and field g has value 3i
```

Similarly object-oriented types can be defined as `typedecls` or `datatypes` and constructed using the same syntax. For example:
```none
typedecl Fahrenheit = Int;
Fahrenheit{32i} %%constructs a Fahrenheit value for freezing

typedecl SystemID = /[A-Z]{3}"-"[0-9]+/;
typedecl PartID = StringOf<SystemID>;

"X-52"_PartID    %%fails the invariant on the string
"ABC-123"_PartID %%constructs a literal PartID value with the value ABC-123
PartID{SystemID::from("ABC-123")} %%constructs a PartID value with the value ABC-123

datatype BoolOp using {
    line: Nat
} of
| LConst { val: Bool }
| NotOp { arg: BoolOp }
| AndOp { larg: BoolOp, rarg: BoolOp }
| OrOp { larg: BoolOp, rarg: BoolOp }
;

NotOp{5n LConst{1n, false}} %%constructs a NotOp value
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
Qux{"", 3i, 10i} %%fails invariant $name !== ""
Qux{"bob", 0i, 10i} %%fails invariant $g > 0
Qux{"bob", 4i, 2i} %%fails invariant $g < $h
Qux{"bob", 4i, 10i} %%ok

typedecl Percentage = Nat & {
    invariant $value <= 100n;
}
Percentage{101n} %%fails invariant $value <= 100n
Percentage{99n}  %%ok
``` 

## Special Constructors
-- In Progress --
The `Option<T>` and `Result<T, E>` types have special constructor support. In addition to the regular `Something<Int>{3i}` constructor forms they provide short and type inferred forms with the syntax `some(e)`, `ok(e)`, `err(e)` and `result(e)` where `e` is an expression. These forms will infer the appropriate template types and convert the expressions as needed. The `result(e)` type will also insert conversions between compatible result types and construction of result objects from values (see issue #1).

Examples of these special forms include:
```none
let x: Option<Int> = some(3i); %%x is a Some<Int> with value 3i
let y: Option<Int?> = some(5i); %%y is a Some<Int?> with value 5i

function foo(): Result<Int, String> {
    return ok(3i); %%returns a Result<Int, String> with value 3i
}

function bar(): Result<Int, String> {
    return err("error"); %%returns a Result<Int, String> with error "error"
}
function baz(): Result<Int, String?> {
    return result(bar()); %%returns a Result<Int, String?> by converting the return of bar into the correct type
}
```

## Collection Constructors
-- In Progress --
Bosque provides a range of standard collections, including `List<T>`, `Stack<T>`, `Queue<T>`, `Set<T>`, and `Map<K, V>` (more details are available in the collections docs).These collections can be constructed using syntax similar to the entity constructors (but generalized since they may have many elements). For example:
```none
List<Bool>{} %%constructs an empty List<Bool>
List<Int>{1i, 2i, 3i} %%constructs a List<Int> with values 1i, 2i, 3i

Map<Int, String>{} %%constructs an empty Map<Int, String>
Map<Int, String>{MapEntry<Int, String>{1i, "one"}, MapEntry<Int, String>{2i, "two"}} %%constructs a Map<Int, String> with entries 1i->"one" and 2i->"two"
```

Map (Set) constructors must have `KeyType` values as keys (see [types](types.md)) also do validity checking that there are no duplicate keys. Maps also provide a shorthand syntax for constructing `MapEntry` values:
```none
Map<[Int, Int], String>{} %%Type error [Int, Int] is not a KeyType
Map<Int, String>{MapEntry<Int, String>{1i, "one"}, MapEntry<Int, String>{1i, "two"}} %%Error duplicate key values

Map<Int, String>{1i => "one", 2i => "two"} %%constructs a Map<Int, String> with entries 1i->"one" and 2i->"two"
```

## Namespace and Member Functions
-- In Progress --
Bosque supports simple functions defined at a namespace scope or within a type scope. Namespace functions can be called with or without a namespace qualifier (for functions defined in ths same namespace where they are use). Functions defined in a type scope must always be called with the type qualifier (even within the same type scope).

```none
namespace Main;

function f(x: Int, y: Int): Int {
    return x + y;
}

f(1i, 2i) %%returns 3i
Main::f(1i, 2i) %%returns 3i

entity Foo {
    function f(x: Int, y: Int): Int {
        return x - y;
    }
}

Foo::f(1i, 2i) %%returns -1i
```

## Namespace Operators
-- In Progress --
[TODO] Operators allow multiple dynamic dispatch functions to be defined. They are currently partially implemented (see issue #13). 

The declaration of an operator is a virtual or abstract definition which may have Concept or Union typed arguments. Each dispatch implementation must have only unique (non-entity and non-union) typed arguments and must be defined in the same namespace as the operator (this prevents resolution ambiguity and accidental overloading). Arguments may also use literal value dispatch on one argument in the operator. If these are used then each dispatch implementation must provide a literal value for this argument.

## Field Access
-- In Progress --
Fields in Object-Oriented types are accessed using the notation `e.f` where `f` is a field name. Fields accesses can be done on expressions of concrete and abstract types (virtual accesses). These virtual accesses can be on Concepts or Unions -- however all possible resolutions must be to the same definition!

Examples of field access include:
```none
concept Bar {
    field g: Int;
}
concept Named {
    field name: String;
}

entity Qux provides Named, Bar {
    field h: Int;
}
entity Qaz provides Named, Bar {
    field h: Int;
}

let v1 = Qux{"bob", 1i, 2i};
let v2 = Qaz{"alice", 3i, 4i};

v1.g %%concrete field lookup -- 1i
v2.g %%concrete field lookup -- 3i

let x: Named = ...;
x.name %%virtual field lookup
x.h %%error -- Named does not have field h

let y: Qux | Qaz = ...;
y.g %%virtual field lookup
y.h %%error -- Qux, Qaz both have h fields but different declarations
```

## ITest Check
-- In Progress --
Bosque provides a unique form of test operators for types/values that generalizes simple type-relations checks. These operators are also used to implement the explicit flow-typing and binding in the language. The full syntax/semantics for these operators are covered in the *ITests* section. Their use for postfix tests uses the following syntax `e?ITest` where `ITest` is an ITest expression. 

Some examples of these tests include:
```none
concept Bar {
    field g: Int;
}
concept Named {
    field name: String;
}

entity Qux provides Named, Bar {
    field h: Int;
}
entity Qaz provides Named, Bar {
    field h: Int;
}

let x: Named = ...;
x?<Qux> %%true if x is a Qux
x?!<Qux> %%true if x is a not a Qux

let y: Qux | Qaz | None = ...;
y?<Qux | Qaz> %%true if y is a Qux or Qaz
y?<None> %%true if y is None
y?none %%true y is none
y?!none %%true if y is none
y?some %%true if y is a subtype of Some
```
 
## ITest As and Conversion
-- In Progress --
Bosque provides a unique form of conversion operators for types/values that generalizes simple type-relations checks. These operators are also used to implement the explicit flow-typing and binding in the language. The full syntax/semantics for these operators are covered in the *ITests* section. Their use for postfix tests uses the following syntax `e@ITest` where `ITest` is an ITest expression. 

Some examples of these tests include:
```none
concept Bar {
    field g: Int;
}
concept Named {
    field name: String;
}

entity Qux provides Named, Bar {
    field h: Int;
}
entity Qaz provides Named, Bar {
    field h: Int;
}

let x: Named = ...;
x@<Qux> %%fails if x is not a Qux and result type is Qux
x@!<Qux> %%fail if x is a not a Qux and result type is Named

let y: Qux | Qaz | None = ...;
y@<Qux | Qaz> %%fails if y is not a Qux or Qaz and result type is Qux | Qaz
y@!<Qux> %%fails if y is a Qux and result type is Qaz | None
y@!<None> %%fails if y is None and result type is Qux | Qaz
y@some %%fails if y is none and result type is Qux | Qaz

let z: Result<Int, String> = ...;
z@ok %%fails if z is err and result type is Int
z@err %%fails if z is ok and result type is String
```

## Method Call
-- In Progress --
Bosque Object-Oriented types support member method definitions. These may be direct (no virtual definitions or dispatch) or virtual. Direct methods are defined on a single type and called directly when the receiver is of that type or a subtype. As with field accesses, if there are multiple types in a union, a method may be invoked provided all possible resolutions are to the same definition.

Examples of direct method calls include:
```none
concept Bar {
    field g: Int;

    method get_g(): Int {
        return this.g;
    }
}
entity Qux provides Bar {
    field h: Int;

    method get_h(): Int {
        return this.h;
    }
}
entity Qaz provides Bar {
    field h: Int;

    method get_h(): Int {
        return this.h;
    }
}

let v1 = Qux{"bob", 1i, 2i};
let v2 = Qaz{"alice", 3i, 4i};

v1.get_h() %%1i
v2.get_h() %%3i

let x: Bar = ...;
x.get_g() %%call to Bar get_g
x.get_h() %%error -- Bar does not have method get_h

let y: Qux | Qaz = ...;
y.get_g() %%call to Bar get_g
y.get_h() %%error -- differing declarations of get_h
```

## Method Call Virtual
-- In Progress --
Bosque Object-Oriented types support virtual methods are defined on a single `concept` type using the `abstract` or `virtual` attribute. A virtual method may be defined again in subtypes using the `override` attribute. Virtual methods are dispatched based on the type of the receiver. However, if the receiver is a union type, all the possible resolutions must be to the same definition (although the implementations may differ).

Examples of virtual method calls include:
```none
concept Bar {
    field g: Int;

    virtual method get_g(): Int {
        return this.g;
    }

    abstract method get_h(): Int;
}
entity Qux provides Bar {
    field h: Int;

    override method get_h(): Int {
        return this.h;
    }
}
entity Qaz provides Bar {
    field h: Int;

    override method get_h(): Int {
        return this.h;
    }

    override method get_g(): Int {
        return this.g + 1i;
    }
}

let x: Bar = ...;
x.get_g() %%call to Qux get_g (goes to Bar impl) or Qaz get_g (goes to Qaz override impl)
x.get_h() %%abstract in Bar so dispatches to Qux or Qaz

let y: Qux | Qaz = ...;
y.get_g() %%call to Qux get_g (goes to Bar impl) or Qaz get_g (goes to Qaz override impl)
y.get_h() %%abstract in Bar so dispatches to Qux or Qaz
```

## Prefix Boolean Not
The `!` operator is used to perform a boolean _not_ operation on a boolean expression. This operator is defined for regular `Boolean` types and `type` aliases _but_ does not apply to other types (e.g. None and there is not notion of falsy conversion as in JavaScript or C style languages).

```none
!true  %%false
!false %%true

type IsOpEnabled = Boolean;
!(true<IsOpEnabled>) %%false<IsOpEnabled>
```

## Prefix Negation
In Bosque the `+` and `-` operators are used to perform a unary sign operation on a numeric expression. In contrast to most languages the `-` operator is _safe_ for all numeric types. Specifically, as the valid range for `Int`/`ChkInt` is symmetric! For `Int`/`ChkInt` negation is always valid and for `Nat`/`ChkNat` negation results in a conversion to the corresponding `Int`/`ChkInt` type. The `+` operator is effectively a no-op for the primitive types (but may function differently if/when operator overloading is added).

```none 
-(1i)  %% -1i
+(1i)  %% 1i

-ChkInt::npos  %% ChkInt::npos (still npos)
```

We distinguish between the following cases `-(5<Foo>)` and `-5<Foo>` -- the former is negating the typed literal value while the latter is negating the underlying value and then constructing a new typed literal value.

## Binary numeric arithmetic operators
Bosque supports the standard set of binary numeric arithmetic operators of `+`, `-`, `*`, and `//`. These are defined for all numeric types and automatically for any `type` alias of a numeric type. The fixed size `Int` and `Nat` types are checked for overflows while the `ChkNat` and `ChkInt` types are checked for underflow on subtraction and division-by-zero (all other overflow types saturate to `ChkInt::npos`/`ChkNat::npos`). All types are checked for division by zero. 

Types are not implicitly converted for arithmetic operations and, if needed, must be explicitly coerced to the same types.

```none
1i + 2i     %% 3i
3.5f + 2.5f %% 6.0f
1i + 2.0f   %% type error -- no implicit conversion

2n - 1n      %% 1n
2n - 3n      %% error Nat underflow
3.0f // 0.0f %% error division by zero (for all types)
```

In addition to standard numeric types Bosque also supports `type` aliases of numeric types. These aliases support all the same arithmetic operations as their underlying types for basic well-formed (closed) operations. In the case of addition and subtraction this means that both arguments must be of the same `type` alias. For multiplication one argument may be of the `type` alias and the other of the underlying numeric type and for division the numerator must be of the `type` alias while the divisor can be of the `type` alias (yielding a result of the underlying type) or of the underlying type (yielding a result of the `type` alias). 

```none
typedecl Foo = Int;

2i<Foo> + 1i<Foo>  %% 3i<Foo>

2i<Foo> * 3i<Foo>  %% error Foo^2 is not well defined
2i<Foo> * 3i       %% 6i<Foo>

4i<Foo> // 2i      %% 2i<Foo>
4i<Foo> // 2i<Foo> %% 2i
```

## Binary numeric comparison operators
-- In Progress --
Bosque supports the standard set of binary numeric comparison operators of `==`, `!=`, `<`, `<=`, `>`, and `>=`. These are defined for all numeric types and automatically for any `typedecl` of a numeric type. 

Types are not implicitly converted for comparison operations and, if needed, must be explicitly coerced to the same types.

```none
typedecl Foo = Nat;

1i == 2i %%false
1i != 2i %%true
3.5f <= 2.5f %%false

2/3R == 4/6R %%true
1/3R < 1/2R %%true

2n_Foo > 1n_Foo %%true
2n_Foo !== 3n_Foo %%true
```

## Binary KeyType equality operators
`KeyType` values play a critical role in Bosque. They are used as keys in `Set<T>` and `Map<K, V>` containers and they are also used for strong equality testing with the `===` and `!==` operators. These operators allow for testing of values when (at least) one of the arguments is a `KeyType` value. The types on the two sides of the operator do not need to be the same but one must be a subtype of the other.

Examples of `KeyType` equality operator usage includes:

```none 
1i === 1i %%true (identical to 1i == 1i)
"hello" !== "goodbye" %%false
true === none %%false

let x: Int | None = 1i;
x === none %%false
x === 1i %%true
x === 2i %%false

let y: Option<String> = some("hello");
y === none %%error types don't overlap
y === nothing %%true

let p: String | Int = "hello";
let q: String | Int | None = "hello";
p === q %%true

entity Foo {}
let f: Foo? = Foo{};
let g: Foo? = none;

f === g %%error at least one type must be a KeyType
f === none %%false
g === none %%true
```

## Binary Logic `&&`/`||`/`==>` operators
Bosque provides the standard short-circuiting boolean operators of `&&` and `||`. Bosque also has a logical implication operator `==>` which is short-circuited on the left side when it is `false`. 

```none
true && true %%true
true && false %%false
false && (1i / 0i == 1i) %%false -- short-circuited

true || false %%true -- short-circuited
false || false %%false

true ==> true %%true
true ==> false %%false
false ==> (1i / 0i == 1i) %%true -- short-circuited
```

## MapEntry Constructor `=>` operator
The `Map<K, V>` container in Bosque holds values of type `MapEntry<K, V>`. The Map entry constructor `=>` is a shorthand notation for creating `MapEntry` values from a key and value expression. The type of the entry is inferred from the context. 

```none
1i => 2i; %%MapEntry<Int, Int>{1i, 2i}
Map<Int, String>{1i => "one", 2i => "two"}; %%Map<Int, String>{MapEntry<Int, String>{1i, "one"}, MapEntry<Int, String>{2i, "two"}}
```

## If-Then-Else Expression
Bosque supports _if-then-elif*-else_ syntax for expressions. The type of the expression is the union of all the branch expressions (and type inference is applied to each expression if possible). The test conditions include the standard boolean expression form _and_ any _ITest_ expression! When using the ITest expression form it is also possible to use _Binder_ syntax (the `$` variable) in the branch expression which is bound to the value of the expression if the test passes. 

Examples of simple if-then-else expressions:
```none
if (x < 0i) then -x else x %%Int
if (x == 0i) then 0i elif (x < 0i) then -1i else 1i %%Int

let yy: Int? = if (x == 0i) then none else x %%Inferred as Int? in each branch expression
```

Examples of if-then-else expressions with ITest expressions:
```none
let x: {f: Int?, g: String} = ...;

if !none (x.f) then %%special none ITest form
    1i 
else 
    0i

if <None> (x.f) then %%typeof form ITest 
    0i 
else 
    1i

if [none] (x.f) then %%literal equality form ITest
    0i 
else 
    1i
```

Examples of if-then-else expressions with ITest expressions and binders:
```none
let x: {f: Int?, g: String} = ...;

if !none (x.f) then 
    $ %%$ is bound to x.f@!none in the branch expression
else 
    0i 

if none (x.f) then 
    0i 
else 
    $ %%$ is bound to false flow (x.f@!none) in the else branch expression
```

## Switch Expression
Bosque provides a `switch` expression for matching against a set of literal cases. The matches in a switch expression can be literals or the special `_` wildcard match. As with if expressions the branch expressions are unioned to determine the type of the switch expression, type inference is applied if possible, and binders can be used in the branch expressions (bound to the switch expression and type refined according to matched/unmatched tests). 

Non-exhaustiveness is not checked from the values but a runtime error will be raised if there is no matching case.

Examples of simple switch expressions include:
```none
let x: Int? = ...;

switch (x) {
    |none => 0i
    | 0i => 1i
    | _  => 2i
} %%Int

let y: Bool = ...;
switch (y) {
    | true    => 0n
    | false => 1n
} %%Nat

let z: Int? = switch(x) {
    | none => 0i
    | _  => 1i
}; %%Int?
```

Examples of switch expressions with binders include:
```none
let x: {f: Nat?, g: Int} = ...;

switch (x.f) {
    |none => 0n
    | _  => $ + 1n
} %%Int

let y: Option<Nat> = ...;
switch (y) {
    | nothing => 0n
    | _  => $.value() + 1n
} %%Nat
```

## Match Expression
The Bosque `match` expression is similar to the switch expression but uses type tests instead of literal tests. The match expression is a union of the branch expressions and type inference is applied if possible. Binders can be used in the branch expressions (bound to the match expression and type refined according to matched/unmatched tests).

Non-exhaustiveness is not checked from the values but a runtime error will be raised if there is no matching case.

Examples of simple match expressions include:
```none
let x: Int | Nat | None = ...;

match (x) {
    | None  => 0i
    | Int => 1i
    | _   => 2i
} %%Int

let z: Int? = match(x) {
    | None  => 0i
    | Int => 1i
}; %%Int?
```

Examples of match expressions with binders include:
```none
let x: {f: Nat?, g: Int} = ...;

match (x.f) {
    None => 0n
    | _  => $ + 1n
} %%Int

let y: Option<Nat> = ...;
match (y) {
    Nothing          => 0n
    | Something<Nat> => $.value() + 1n
} %%Nat
```

# Bosque Expression Components

## ITests
The Bosque language type checker uses a novel _explicit flow-sensitive_ typing algorithm. Instead of relying on a set of heuristics and implicit rules in the checker logic Bosque makes the flow typing an explicit part of the language syntax. Inference introduction is limited to function/method arguments, `let`/`var` bindings and `return` statements where the type of the binding or return value is used to infer type of the expression (or vice a versa). These introductions are then pushed down the expression tree to the leaves or propagated up to roots. Otherwise flow and inference are explicitly stated with Itests and Binders.

There are three flavors of ITests in bosque:
1. **Type ITests** - These are used to test if an expression is of a specific type in a classic subtyping sense. The syntax for these is `<Type>` where `Type` is a type expression and `!<Type>` is an negated version of the test.
2. **Value ITests** - These are used to test if an expression is a specific value, which must be a literal comparable with the `===` or `!==` operator.The syntax for these is `[Literal]` where `Literal` is a literal expression and `![Literal]` is a negated version that uses the `!==` semantics.
3. **Special Constructor ITests** - These are used to test if an expression is a specific special constructor and then, depending, on the context will also extract and bind values. The syntax for these is:
    - `none` - tests if the expression is `none` and converts the result to a none
    - `some` - tests if the expression is `some` and converts the result to a some
    - `nothing` - tests if the expression is `nothing` and converts the result to a nothing
    - `something` - tests if the expression is `something` and converts the result to `T` corresponding to the `Something<T>` type value
    - `ok` - tests if the expression is `ok` and converts the result to `T` corresponding to the `Result<T, E>::Ok` type value
    - `err` - tests if the expression is `err` and converts the result to `E` corresponding to the `Result<T, E>::Err` type value
    - `result` - tests if the expression is `result` and converts the result to `Result<U, V>` corresponding to the contextual Result type value

[TODO] the `result` case has missing support in some of the positions.

## Arguments

## Binders

# Bosque Task Expressions

