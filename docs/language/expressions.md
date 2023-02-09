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
    11. Namespace and Member Functions
    12. Namespace Operators
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

Tuples with Inference:
```none
function foo(): [Int, Boolean?] {
    return [3, true]; //expression types are Int and Boolean but inference converts to Int and Boolean?
}
```

## Record Constructors
## Entity Constructors
## Special Constructors

# Bosque Expression Components

# Bosque Task Expressions

