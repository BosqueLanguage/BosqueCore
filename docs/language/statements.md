# Bosque Language Statements

- Pure Bosque Statements
    1. Empty Statement
    2. Variable Declaration
    3. Variable Assignment
    4. Variable Re-Type
    5. RefCall Statement
    6. Return Statement
    7. Short-Circuit Return
    8. Variable Short-Circuit Re-Type
    9. If-Else Statement
    10. Switch Statement
    11. Match Statement
    12. Abort Statement
    13. Assert Statement
    14. Debug Statement

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
## Return Statement

    7. Short-Circuit Return
    8. Variable Short-Circuit Re-Type
    9. If-Else Statement
    10. Switch Statement
    11. Match Statement
    12. Abort Statement
    13. Assert Statement
    14. Debug Statement

- Bosque Statement Components
    
- Bosque Task Statements