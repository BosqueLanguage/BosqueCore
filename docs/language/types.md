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
    - DashResult
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
- `BigNat`: Unsigned large (127-bit) precision unsigned integers.
- `BigInt`: Unsigned large (127-bit) precision signed integers.

### Float Number Types
- `Float`: 64-bit base-2 IEEE-754 (style) floating point numbers -- Infinity/NaN are errors.
- `Decimal`: 50-digit base-10 floating point number (TODO: currently `cpp_dec_float_50`).
- `Rational`: Fraction with BigInt numerator and Nat rounding denominator.

### Specific Number Types
- `DecimalDegree`: A decimal degree value in the range [-180, 180].
- `LatLongCoordinate`: A pair of DecimalDegree values for latitude and longitude.
- `Complex`: A pair of Float values for real and imaginary parts.

### Raw Data Types
- `Byte`: An 8-bit unsigned integer value in the range [0, 255].
- `ByteBuffer`: A sequence of Byte values.

### UUID Types
- `UUIDv4`: A version 4 UUID.
- `UUIDv7`: A version 7 UUID.

### SHA Hash Types
- `SHAHash`: A SHA3-256 hash value.

### Date and Time Types
- `DateTime`: A date and time with timezone information -- computations on these dates are aware of timezones and leap seconds. Operations are non-deterministic as timezone rules can change over time.
- `TAITime`: A time value without timezone (TAI standard) -- computations on these are simple and deterministic (by the definitions of TAI).
- `PlainDate`: A calendar date without time or timezone.
- `PlainTime`: A time of day without date or timezone.
- `Timestamp`: A UTC timestamp with millisecond precision (these are always assumed to represent past values and are not subject to change from leap second rules).
- `LogicalTime`: A logical tick-time representation as a monotonic counter.

### Data and Time Delta Types
- `DateTimeDelta`: A duration of time in days, months, years, hours, minutes, seconds, and milliseconds.
- `DateDelta`: A duration of time in days, months, and years.
- `TimeDelta`: A duration of time in hours, minutes, seconds, and milliseconds.
- `TimeStampDelta`: A delta for `Timestamp` values.
- `LogicalTimeDelta`: A delta for `LogicalTime` values.
- `SecondsDelta`: A delta of seconds (including milliseconds).

### String Types
- `String`: A UTF-8 encoded string of characters.
- `CString`: A C-String of printable ascii characters.

### Path Types
- `Path`: A URI style resource path.
- `PathFragment`: A fragment of a URI style resource path.
- `PathGlob`: A glob pattern for matching URI style resource paths.

### Regex Types
- `Regex`: A regular expression pattern for unicode strings.
- `CRegex`: A regular expression pattern for C-style strings.

### Format String and Path Types
- `FormatString<T1, ..., Tk>`: A format string with embedded typed format components.
- `FormatCString<T1, ..., Tk>`: A C-style format string with embedded typed format components.
- `FormatPath<T1, ..., Tk>`: A format path with embedded typed format components.

## Typed Values, Strings, and Paths
All primitve values in Bosque can be given explicit type annotations to create typed literals. This includes primitive strings and paths as well as format strings and paths. Typed literals are written by appending `<TypeName>` after the literal value. For example:

```none
"Hello, World!"<Greeting>
\file:/path/${0}/resource\<ConfigPath>
```

This includes format strings and paths as well:

A (new) type for a literal is declared using the `type` keyword. This creates a new nominal type that is distinct from other types, even if they have the same underlying structure. These types can be augmented with methods, functions, invariants, etc. They also inherit comparisions and numeric operations from their underlying primitive type.

Additionally strings can be specialized with regular expression and paths can be specialized with glob patterns to create new types that restrict the set of valid values!

# Type Checker
