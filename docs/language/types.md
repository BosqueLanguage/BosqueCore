# Bosque Language Type System and Checker

__Table of Contents:__

- Type System
  1. Primitive Types
  3. Enum Types
  4. NewType Types
    - NewType String Types
  6. Format String Types
  5. Concept Types
  6. Entity Types
  7. Algebraic Types
  10. EList Types
  11. Special Types
    - Option
    - Result
    - APIResult
  11. Lambda Types
  11. Template Types
    - Constraints
    - Special Kinds
  12. Task Types
- Type Checker
  1. Subtyping
  2. Implicit Type Coercion
  3. Explicit Type Coercion
  4. Type Inference
  5. Explicit Flow Typing

# Type System
The Bosque type system is designed to be expressive, flexible, and simple to use. It is based on a hybrid of object-orientated and functional programming concepts with a number of features adopted (and extended) from experience working with service base and cloud applications. Foundational concepts driving the type systems design are:
1. Prevent common programming errors, support IDE integration, and provide useful inline documentation. Some key features here include support for enhanced-ADTs, typed strings/paths, and lightweight typedecls over primitive types.
2. Avoid complex type-checking algorithms that are difficult to understand and slow to run, and ensure that, as the requirements for a program change, the type system can be easily extended/modified to match. Features like Union-types and multiple-inheritance are examples that support this goal.

Types in Bosque should be obvious and easy to write/update, provide useful information to IDE tooling and other developers, prevent a wide range of common errors, and then get out of the way!

## Primitive Types
For the set of builtin primitive types, Bosque looks broadly at the most common foundation types seen in modern programming, particularly looking toward cloud-dev, that we want to support directly such as BigInt and BigNat, UUIDs, or dates and
times. Instead of forcing developers to manually define these types, or encode them as strings with a special structure, we provide them as primitives that have well known syntax and can be extended for domain specific concepts. 

### Unique Types
- `None`: The type with a single value `none`.
- `Bool`: The type with the values `true` and `false`.

### Integral Number Types
- `Nat`: Unsigned 63-bit integers -- ensures safe cast to Int.
- `Int`: Signed 63-bit integers -- ensures safe negation and cast to Nat.
- `BigNat`: Arbitrary precision unsigned integers.
- `BigInt`: Arbitrary precision signed integers.

### Float Number Types
- `Float`: 64-bit base-2 IEEE-754 (style) floating point numbers -- Infinity/NaN are errors.
- `Decimal`: 50-digit base-10 floating point number (TODO: currently `cpp_dec_float_50`).
- `Rational`: Fraction with BigInt numerator and Nat rounding denominator.

### Specific Number Types
- `DecimalDegree`: A decimal degree value in the range [-180, 180].
- `LatLongCoordinate`: A pair of DecimalDegree values for latitude and longitude.
- `Complex`: A pair of Float values for real and imaginary parts.

### String Types

# Type Checker
