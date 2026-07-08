# Bosque Language Statements

## Empty Statement
The empty statement in Bosque is denoted with `;`. It has no effect on the program state but is useful for emphasizing structure and logical flow.

## Variable Declaration
Variables in Bosque can be declared as immutable using the `let` (or `ref`) keyword, and must be initialized at that point, or can be declared as modifiable using the `var` keyword. Variables can be explicitly declared with a type using the syntax `[let|ref|var] name: Type` and the declared type will be used in inferring the type of the initializer expression. If the type is not specified then it will be inferred from the type of the initializer expression.

If a variable is declared without initialization then it is a type error to use it before assigning a value.

The frontend also supports grouped declarations and grouped initializations such as `var x: Int, y: String;` and `let x, y = expr;` when the right-hand side produces multiple values.

Examples of `let` based declaration include:
```none
let x = 1i; //x has inferred type of Int
let y: (|Option<Int>, String|) = (|some(1i), "hello"|); //y has type of (|Option<Int>, String|) and that type is used to infer tuple constructor type
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

--In Progress-- We do not fully support short-circuit return expressions on variable declaration yet. 

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

Assignments can also be grouped when the right-hand side produces multiple values:

```none
var x: Int;
var y: String;

x, y = 1i, "ok";
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
        ref this[ctr = $ctr + 1n];

        return id; //the current value of this is also returned implicitly and assigned at call site
    }
} 

ref ctr = Counter::create();         //create a Counter 
let id1 = ref ctr.generateNextID(); //id1 is 0 -- ctr is updated
let id2 = ref ctr.generateNextID(); //id2 is 1 -- ctr is updated again
```

Bosque also allows call expressions to be used as standalone statements when their primary purpose is an effect on `ref`, `out`, `out?`, or `inout` parameters, or when a task action is being performed:

```none
updateCounter(ref ctr);
```

## Return Statement
The return statement in Bosque is used to return zero, one, or multiple values from a function.

```none
function example(): Int {
    return 42;
}

--In Progress--
function example2(): (|Int, String|) {
    return 42, "hello";
}

function example2(): Int, String {
    return 42, "hello";
}

let x, y = example2(); //x is 42 and y is "hello"
```


## Conditional Assignment
--In Progress--

## Conditional Return
--In Progress--

## Variable Short-Circuit Assignment
--In Progress--
Bosque also allows short-circuiting right-hand-side forms in variable initialization and assignment statements.

```none
let value = result ?@ ok : 0i;
let present = option @@ some;
```

The `?@` form performs an ITest-based short-circuit with an explicit fallback expression, while the `@@` form is a failure-oriented shorthand.

## Short-Circuit Return
--In Progress--
Bosque allows the same short-circuit right-hand-side forms that are used in assignments to appear in `return` statements.

```none
return result ?@ ok : fail("bad result");
return option @@ some;
```

## If-Else Statement
Bosque provides a standard if-elif-else statement. As with the if-then-else expression the conditions in the statement can be simple expressions or ITests. The branch bodies can use binder expressions inside of branch bodies.

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

let z: Option<Int> = ...;
if (z)@none {
    return $z - 1;
}
```

## Switch Statement
--In Progress--
The Bosque `switch` statement matches against a set of literal cases. The matches in a switch statement can be literals or the special `_` wildcard match.

**[TODO]** Exhaustiveness analysis and some supporting tooling around `switch` are still incomplete.

## Match Statement

The Bosque `match` statement is similar to the switch statement but uses type tests instead of literal tests. The matched value is available in each branch through a binder name, and Bosque flow typing refines that binder according to the matched branch.

[TODO] describe exhaustiveness analysis and flow typing rules for match statements.

Examples of simple match statements include:
```none
recursive method evaluate(): Bool {
    match(this) {
        Const  => { return $this.val; }
        NotOp => { return !$this.arg.evaluate[recursive](); }
        AndOp => { return $this.larg.evaluate[recursive]() && $this.rarg.evaluate[recursive](); }
        OrOp  => { return $this.larg.evaluate[recursive]() || $this.rarg.evaluate[recursive](); }
    }
} 
```

## Dispatch Statement
--In Progress--

## Abort Statement
The abort statement immediately results in a runtime failure. This is useful for debugging and error handling.

```none
abort; //abort with failure
```

## Assert Statement
The assert statement provides a way to specify and check program conditions at runtime. Asserts can be configured with a level flag to control when it is compiled (so expensive checks are not included in production).

[TODO] note that ==> can be used in asserts to check for implication and that the left-hand side is only evaluated if the right-hand side is true.

```none
assert x == 0i; //assert that x is zero -- default level is release
assert debug (x + 1i == 0i); //assert -- only in debug mode

assert (1i // 0i == 1i); //Div by zero will be reported
assert debug (1i // 0i == 1i); //Div by zero will ONLY report in debug mode (otherwise expression is guaranteed to be a NOP)
```

## Validate Statement
The `validate` statement checks a boolean condition and optionally attaches a diagnostic tag with the syntax `validate['tag'] expr;`.

```none
validate x >= 0i;
validate['bounds'] x < limit;
```

[TODO] note that ==> can be used in asserts to check for implication and that the left-hand side is only evaluated if the right-hand side is true.

## Debug Statement
The debug statement is used to output a value to the designated diagnostics dump sink -- this is disabled unless the application is built in debug mode. It is useful for debugging and logging.

```none
_debug "hello world"; //output "hello world" to the diagnostics dump sink
```

## Ref Update Statement
Bosque provides a structural update statement that rebindingly updates one or more fields on a `ref`-capable receiver. The statement form is `ref target[field = value, ...];` and the update list must be non-empty.

```none
ref point[x = 3i, y = 4i];
ref this[count = $count + 1n];
ref self[state = nextState];
```

The `target` may be a local variable, `this`, or `self` depending on the current scope.

**[TODO]** The exact scope rules for `self` updates should be expanded once the corresponding checker support is completed.

## Hole Statement
Hole statements provide structured placeholders in statement position. They can carry a name, captures, documentation text, sample input references, synthesized output variables, and `ensures` clauses.

```none
?_normalize[data] -> [result: List<Int>] {
    ensures result.size() >= 1n;
}
```

These are primarily intended for synthesis, prototyping, and documentation of unfinished logic.

## Block Statement
Statement blocks use `{ ... }` and introduce a nested scope for local variables. Empty blocks should contain an explicit empty statement `;` to make the intent clear.

```none
{
    let x = 1i;
    _debug x;
}
```
