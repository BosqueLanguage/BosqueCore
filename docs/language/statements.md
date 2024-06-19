# Bosque Language Statements

- Pure Bosque Statements
    1. Empty Statement
    2. Variable Declaration
    3. Variable Assignment
    4. Variable Re-Type
    5. Return Statement
    6. If-Else Statement
    7. Switch Statement
    8. Match Statement
    9. Abort Statement
    10. Assert Statement
    11. Validate Statement
    12. Debug Statement

## Empty Statement
The empty statement in Bosque is denoted with `;`. It has no effect on the program state but is useful for emphasizing structure and logical flow.

## Variable Declaration
Variables in Bosque can be declared as immutable using the `let` keyword, and must be initialized at that point, or can be declared as modifiable using the `var` keyword. Variables can be explicitly declared with a type using the syntax `[let|var] name: Type` and the declared type will be used in inferring the type of the initializer expression. If the type is not specified then it will be inferred from the type of the initializer expression.

If a variable is declared without initialization then it is a type error to use it before assigning a value.

Examples of `let` based declaration include:
```none
let x = 1i; //x has inferred type of Int
let y: [Int?, String] = [1i, "hello"]; //y has type of [Int?, String] and that type is used to infer tuple constructor type
```

Examples of `var` based declaration include:
```none
var x = 1i; //x has inferred type of Int
var y: Int = 0i; //y has type of Int

var y: Int; //y has type Int but is not initialized

let z = y + 1i; //error: y is not initialized
if(x != 0i) {
    y = x;
}
else {
    y = 1i;
}
//now y is initialized

let z = y + 1i; //ok: y is initialized
```

[TODO] we do not fully support short-circuit return expressions on variable declaration yet. Need to thread this through things.


## Variable Assignment
Variables in Bosque can be declared as modifiable (using the `var` keyword). These variables can be assigned to later using the `=` assignment operator (also see `ref` calls and -- later -- bulk assignment).

```none
var x: Int = 0i; //x has type of Int and value 0i
var y: Int; //y has type Int but is not initialized

if(x != 0i) {
    y = x;
}
else {
    y = 1i;
}
//now y is initialized

x = 2i; //ok: x is modifiable

let z = y + x; //ok: y is initialized and result of y + x is 3i
```

## Variable Re-Type
In many programs variables are declared with a type that is general and then later processed in blocks where they are known to have a more specific type. Bosque supports this with explicit re-typing of variables using the `e@ITest` syntax. This is a compile-time only operation that does not change the runtime type of the variable. Instead it dynamically asserts that the variable is of the specified type and then uses that type for type inference in the following flow scope.

```none
function fsimple(x: Nat?): Nat {
    x@!none; //assert that x is not none here (error otherwise) and type infer

    return x + 10n;
}

function fsplit(x: Nat?): Nat {
    if none (x) {
        return 0n;
    }
    x@<Nat>; //assert that x is a Nat here (error otherwise) and type infer

    return x + 10n;
}

function fjoin(x: Nat?): Nat {
    var y = x;

    if none (x) {
        y = 0n;
        y@<Nat>;
    }
    else {
        y@some;
    }
    //y is reflowed to be a nat

    return y + 10n;
}
```

## RefCall Statement
In addition to the `=` assignment operator, Bosque supports a `ref` operator that can be used to call a function on a variable *and* rebind the variable to the receiver of the called `ref` method. This is useful for working with code that has an environment or object-like behavior where the state needs to be updated along with computing a value in each processing step. Ref methods/calls cannot be virtual (otherwise they are parametric in the receiver type) and must be declared/invoked with the `ref` keyword.

An example of this feature is:
```none
entity Counter {
    field ctr: Nat;

    function create(): Counter {
        return Counter{0n};
    }

    method ref generateNextID(): Nat {
        let id = this.ctr;

        //TODO: this syntax is not final
        this = Counter{this.ctr + 1n};

        return id; //the current value of this is also returned implicitly and assigned at call site
    }
} 

var ctr = Counter::create();         //create a Counter 
let id1 = ref ctr.generateNextID(); //id1 is 0 -- ctr is updated
let id2 = ref ctr.generateNextID(); //id2 is 1 -- ctr is updated again
```

## Return Statement
The return statement in Bosque is used to return a single value from a function. 

## Short-Circuit Return
The short-circuit return statement in Bosque is used to conditionally return from a function when a value matches an ITest result. This allows for concise checking/handling of error and other early return cases.

[TODO] we do not fully support short-circuit return expressions on variable declaration yet. Need to thread this through things.

## Variable Short-Circuit Re-Type
The basic variable retype statement results in a runtime failure when the test fails. The short-circuit retype statement variation `v @@ ITest [: action];` allows for an ITest to be used which (1) if successful will retype the variable (just like the `v@ITest` form) and (2) if unsuccessful will execute a return with the ITest coerced value _or_ the result of the optionally specified action (which may use the `$` binder).

[TODO] tests are needed for this feature.

## If-Else Statement
Bosque provides a standard if-elif-else statement. As with the if-then-else expression the conditions in the statement can be simple expressions or ITests. The branch bodies can use binder expressions, when using ITests, and the Bosque type checker is aware of terminal branches and re-typings when control flow rejoins after the statement.

Examples of simple if-else statements include:
```none
var x: Int = ...;
if(x < 0) {
    x = -x;
}

let y: Int = ...;
if(y < 0) {
    return "negative";
}
else {
    return "positive";
}

let z: Int? = ...;
if !none (z) {
    return $ - 1;
}
```

## Switch Statement
The Bosque `switch` expression matches against a set of literal cases. The matches in a switch expression can be literals or the special `_` wildcard match. Binders can be used in the branch expressions (bound to the switch expression and type refined according to matched/unmatched tests). 

Non-exhaustiveness is not checked from the values but a runtime error will be raised if there is no matching case.

[TODO] need to finish the emitter implementation and do tests.

Examples of simple switch expressions include:
```none
let x: Int? = ...;

switch (x) {
    none => return 0i;
    | _  => return 2i;
}

let y: Bool = ...;
var k: Nat;
switch (y) {
    true    => k = 0n;
    | false => k = 1n;
} //Nat

```

## Match Statement

The Bosque `match` expression is similar to the switch expression but uses type tests instead of literal tests. The match expression is a union of the branch expressions and type inference is applied if possible. Binders can be used in the branch expressions (bound to the match expression and type refined according to matched/unmatched tests).

Non-exhaustiveness is not checked from the values but a runtime error will be raised if there is no matching case.

Examples of simple match expressions include:
```none
let x: Int | Nat | None = ...;
var k: Int;
match (x) {
    None  => k = 0i;
    | Int => k = 1i;
    | _   => k = 2i;
}
```

## Abort Statement
The abort statement immediately results in a runtime failure. This is useful for debugging and error handling.

```none
abort; //abort with failure
```

## Assert Statement
The assert statement provides a way to specify and check program conditions at runtime (and for static tooling). It can be configured with a level flag to control when it is compiled (so expensive checks are not included in production).

If the condition evaluates to false then the assert will result in a runtime failure (and the message emitted to the logger at the failure level). If the condition evaluation itself results in an error then the assert will not trigger *but* a message will be emitted to the logger at the warn level.

```none
assert x == 0i; //assert that x is zero -- default level is release
assert debug (x + 1i == 0i); //assert -- only in debug mode

assert (1i / 0i == 1i); //assert expression fails -- this will not trigger but a warning will be emitted
```

## Debug Statement
The debug statement is used to output a value to the designated diagnostics dump sink -- this is disabled unless the application is built in debug mode. It is useful for debugging and logging.

```none
__debug("hello world"); //output "hello world" to the diagnostics dump sink
```

- Bosque Statement Components
    
- Bosque Task Statements