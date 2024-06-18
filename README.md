# Bosque Programming Language

[![Licensed under the MIT License](https://img.shields.io/badge/License-MIT-blue.svg)](https://github.com/BosqueLanguage/BosqueCore/blob/master/LICENSE.txt)
[![PR's Welcome](https://img.shields.io/badge/PRs%20-welcome-brightgreen.svg)](#contribute)
[![Build Health](https://img.shields.io/github/actions/workflow/status/BosqueLanguage/BosqueCore/main.yml?branch=main)](https://github.com/BosqueLanguage/BosqueCore/actions) 


# The Bosque Project

Bosque is a new approach to programming models, development tooling, and runtime design that is focused on supporting mechanization at scale and establishing a new standard for creating high-reliability software artifacts. The foundational design precepts for Bosque are:
1. Design for Tooling & Mechanization -- The entire system should be amenable to automated analysis and transformation. Avoid features or behaviors that inhibit analysis and automation.
2. WYSIWYG -- Humans and AI Agents understand and make assumptions about the semantics (behavior) of the code from the textual representation (syntax). Minimize the presence of implicit or syntactically hidden behaviors. 
3. Total Safety -- Don't just make mistakes hard to make, eliminate them entirely. Whenever possible rule-out entire categories of failures by construction.
4. Reliable Performance at Scale -- At scale eliminate worst-case performance behaviors will occur and will be very problematic. Design for low-variance executions and minimizing worst case behavior instead of optimizing for the best or average case. 
5. Failure is Always an Option -- Failure is inevitable and mitigation/recovery is a requirement for reliable and scalable systems. Give un-happy path processing first-class support in the language and ensure observability throughout the system.

# News
After extensive(!) experimentation and prototype work the project has reached a point where all the pieces are in place for a 1.0 release! We have 2 key components that bring new ways to deal with structured text processing ([BREX](https://github.com/BosqueLanguage/BREX)) and literal value representation ([BSQON](https://github.com/BosqueLanguage/BSQON)). We also have a solid baseline compiler and runtime for the compute part of the language. The 1.0 push will be to integrate, refine, and update the components into a state where we can self-host the next parts of the compiler and have a stable language for development in general. The 2.0 push will be to write, in Bosque, a full Small Model Verifier for the Bosque compiler!

There are no hard deadlines on this work but targeting a 1.0 this summer and a 2.0 by the start of the fall! Community involvement is welcome. There are some fidgity parts that I probably just need to manage but I have tried to open issues, and where possible, flag some that are amenable for outside help. This process will be taking place on `main` so, if you need to keep stability, I have created the `stable_pre1` branch. 


# Platform Road Map 

## Current Work Items 

## Planned Next Steps

## Looking for Contributors

### Breakout Features

### High-Value Enhancements

### Chunckable Work Items
xxxx

# Documentation

Complete documenation for the language and standard libraries are on the [Language](docs/overview.md) and [Libraries](docs/overview.md) doc pages respectively. Sample code snippets below provide a quick feel of the language and syntax.

Detailed Documentation, Tutorials, and Technical Information:
* [Language Docs](docs/overview.md)
* [Library Docs](docs/overview.md)
* [Technical Papers](docs/papers/publist.md)

## Code Snippets

**Add 2 numbers:**
```none
function add2(x: Nat, y: Nat): Nat {
    return x + y;
}

add2(3n, 4n) //7n
add2(3n, 0n) //3n

add2(3i, 4.0f) //type error -- defined on Nat but given Int and Float args 
add2(3, 4)     //type error -- all numeric literals must have kind specifier
```

**All positive check using rest parameters and lambda:**
```none
function allPositive(...args: List<Int>): Bool {
    return args.allOf(pred(x) => x >= 0i);
}

allPositive(1, 3, 4)  //true
allPositive()         //true
allPositive(1, 3, -4) //false
```

**Sign (with blocks and assignment):**
```none
function sign(x: Int): Int {
    var y: Int;

    if(x == 0i) {
        y = 0i;
    }
    else {
        y = if (x > 0i) then 1i else -1i;
    }

    return y;
}

sign(5i)    //1
sign(-5i)   //-1
```

**Nominal Types with Multi-Inheritance & Data Invariants:**
```
concept WithName {
    invariant $name !== "";

    field name: String;
}

concept Greeting {
    abstract method sayHello(): String;

    virtual method sayGoodbye(): String {
        return "goodbye";
    }
}

entity GenericGreeting provides Greeting {
    const instance: GenericGreeting = GenericGreeting{};

    override method sayHello(): String {
        return "hello world";
    }
}

entity NamedGreeting provides WithName, Greeting {
    override method sayHello(): String {
        return String::concat("hello", " ", this.name);
    }
}

GenericGreeting{}.sayHello()          //"hello world"
GenericGreeting::instance.sayHello()  //"hello world"

NamedGreeting{}.sayHello()           //type error no value provided for "name" field
NamedGreeting{""}.sayHello()         //invariant error
NamedGreeting{"bob"}.sayHello()      //"hello bob"
```

**Typedecl Types**
```
typedecl Fahrenheit = Int;
typedecl Celsius = Int;

typedecl Percentage = Nat & {
    invariant $value <= 100n;
}

32i_Fahrenheit + 0i_Celsius //type error different numeric types
30n_Percentage              //valid percentage
101n_Percentage             //invariant error

function isFreezing(temp: Celsius): Bool {
    return temp <= 0i_Celsius;
}

isFreezing(5i)          //type error not a celsius number
isFreezing(5i_Celsius)  //false
isFreezing(-5i_Celsius) //true

```

**Flow and Binders:**
```
function flowit(x: Nat?): Nat {
    //ITest for none as special
    if(x)@none {
        return 0n;
    }
    else {
        //ITest allows binder for $x to value of x (with type inference)
        return $x + 10n;
    }
}

function restrict(x: Nat?): Nat {
    if(x)@@none {
        return 0n;
    }
    //x is a Nat here and type infer

    return x + 10n;
}
```

**(Algebraic Data Types)++ and Union Types**
```
datatype BoolOp using {
    line: Nat
} of
Const { val: Bool }
| NotOp { arg: BoolOp }
| AndOp { larg: BoolOp, rarg: BoolOp }
| OrOp { larg: BoolOp, rarg: BoolOp }
& {
    recursive method evaluate(): Bool {
        match(this)@ {
            Const  => return $this.val;
            | NotOp => return !$this.arg.evaluate[recursive]();
            | AndOp => return $this.larg.evaluate[recursive]() && $this.rarg.evaluate[recursive]();
            | OrOp  => return $this.larg.evaluate[recursive]() || $this.rarg.evaluate[recursive]();
        }
    } 
}

AndOp{2n, Const{1n, true}, Const{1n, false}}.evaluate[recursive]() //false
OrOp{2n, Const{1n, true}, Const{1n, false}}.evaluate[recursive]()  //true

function printType(x: Bool | Int | String | None): String {
    return match(x) {
        Bool     => "b"
        | Int    => "i"
        | String => "s"
        | _      => "n"
    };
}

printType(1.0f) //type error
printType(true) //"b"
printType(none) //"n"

```

**Validated Strings:**
```
validator ValidZipcodeUS = /[0-9]{5}("-"[0-9]{4})?/;
validator ValidCSSpt = /[0-9]+"pt"/;

function is3pt(s1: StringOf<ValidCSSpt>): Bool {
    return s1.value() === "3pt";
}

RegexValidator::accepts<ValidZipcodeUS>("98052-0000") //true
RegexValidator::accepts<ValidZipcodeUS>("1234")       //false

is3pt("12")              //type error not a StringOf<CSSpt>
is3pt("98052"(ValidZipcodeUS)) //type error not a StringOf<CSSpt>

is3pt("3pt"(ValidCSSpt)) //true
is3pt("4pt"(ValidCSSpt)) //false
```

# Installing the Bosque Language (Currently Development Only)

In order to install/build the project the following are needed:

- 64 bit Linux Operating System (Ubuntu 22 recommended)
- Version 20+ of [node.js](https://nodejs.org/en/download/) (v20 or higher)
- Typescript (5.3 or higher) -- install with: `npm i typescript -g`
- Git and [git-lfs](https://git-lfs.github.com/) setup

## Build & Test

```none
npm install && npm test
```
The Z3 theorem prover is provided as a binary dependency in the repo via git LFS. To ensure these are present you will need to have [git-lfs](https://git-lfs.github.com/) installed, run `git lfs install` to setup the needed hooks, and pull. 

## Parser & Typechecker

Current work is on spinning up the Parser/Typechecker and some basic LSP support. Key design goals in these systems are simplicity and general efficiency. Fast turnaround times in the developer loop tools are a priority so all features are geared towards a max O(n log n) complexity -- no exponential blowups (or turing completeness) in the type system, a relatively efficient 2 pass parser, and a fast emit to JavaScript.

## Compiler & Runtime

Next open task on the roadmap is a JavaScript runtime and NPM package generator. This will be targeted as a fast turnaround for developer tasks and ease of implementation (+ nice features like supporting a web-playground or REPL). A secondary task is an optimized AOT compiler with the O(1)-GC and and a focus on fast startup, low memory usage, and predictable latency.

## Visual Studio Code Integration

This repository provides basic [Visual Studio Code](https://code.visualstudio.com/) IDE support for the Bosque language (currently limited to syntax and brace highlighting). The installation requires manually copying the full `bosque-language-tools/` folder into your user `.vscode/extensions/` directory and restarting VSCode.

## Contribute

This project welcomes community contributions.

* [Submit bugs](https://github.com/BosqueLanguage/BosqueCore/issues) and help us verify fixes.
* [Submit pull requests](https://github.com/BosqueLanguage/BosqueCore/pulls) for bug fixes and features and discuss existing proposals.
* Chat about the [@BosqueLanguage](https://twitter.com/BosqueLanguage) (or [#BosqueLanguage](https://twitter.com/hashtag/BosqueLanguage)) on Twitter.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/).

## License

Code licensed under the [MIT License](LICENSE.txt).
