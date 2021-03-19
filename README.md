# mini-symex [![Build](https://github.com/wadoon/mini-symex/actions/workflows/build.yml/badge.svg)](https://github.com/wadoon/mini-symex/actions/workflows/build.yml) [![Lines of Code](https://sonarcloud.io/api/project_badges/measure?project=wadoon_mini-symex&metric=ncloc)](https://sonarcloud.io/dashboard?id=wadoon_mini-symex) [![Maintainability Rating](https://sonarcloud.io/api/project_badges/measure?project=wadoon_mini-symex&metric=sqale_rating)](https://sonarcloud.io/dashboard?id=wadoon_mini-symex) [![Quality Gate Status](https://sonarcloud.io/api/project_badges/measure?project=wadoon_mini-symex&metric=alert_status)](https://sonarcloud.io/dashboard?id=wadoon_mini-symex) [![Reliability Rating](https://sonarcloud.io/api/project_badges/measure?project=wadoon_mini-symex&metric=reliability_rating)](https://sonarcloud.io/dashboard?id=wadoon_mini-symex) [![Technical Debt](https://sonarcloud.io/api/project_badges/measure?project=wadoon_mini-symex&metric=sqale_index)](https://sonarcloud.io/dashboard?id=wadoon_mini-symex) [![Vulnerabilities](https://sonarcloud.io/api/project_badges/measure?project=wadoon_mini-symex&metric=vulnerabilities)](https://sonarcloud.io/dashboard?id=wadoon_mini-symex)


Symbolic Execution Engine and Verification Condition Generator for 
While-Language and SMTlib. 

## Project Goal

This project provides a verification condition generator (VCG) for a simple Pascal-like language.
All generated verification condition (VC) is encoded into a single SMTLIB-file in such a way 
that a program adheres to its specification if and only if all `check-sat` queries are `unsat`.
One of the goal is the linkage between a VC and the logical terms back to the original program. 

## Getting Started

```bash
$ ./gradlew :core:installDist :ui:installDist
```

## TODO

* [ ] implement `Length(x)` function
* [ ] write all positional information in the attributes
* [ ] make binary search work
* [ ] test cases

## Meta Information

We use the attribute-facility of SMT to provide positional meta information of terms 
and VCs. In SMT, we can use `(! <term> <attributes>)` form to annotate a term with additional attributes.
In particular, generated terms look as follows: 

```smt
(! (= x (+ 1 1) 
   :named <symbol>
   :source "<filename>"
   :start  <int>
   :end    <int>)
```

with following attributes

* `:named`  gives term a name (this is also specified by SMTLIB and used by SMT solvers)
* `:source` -- the filename
* `:start` -- start offset (integer) inside the given file 
* `:end` -- end offset (integer) inside the given file 

## Programming language

* Pascal-like Programming language
* Distinguishing between functions and procedures
* Statements are assignment, `if`, `while`, procedure calls.   
* Expressions over the usual operators (`+,-,*,/,%,<>,=,<,<=,>,>=`)
* Supported datatypes are `bool` and `int` as well as one-dimensional arrays
  over them.
* Currently, no support for global variables  
* Enrich with a specification language

## Description of Specification Language

We use a simple Pascal-like language as the base, and 
enrich the language with specification.   

On the statement-level you can use `assert`, `assume`, and `havoc` 
statements with the usual semantics. Functions and procedures takes additional a list of pre-conditons (`pre`), 
a list of post-condition (`post`), and also a list assignable global program-variables (`modifies`).  
Similary, loops have loop-invariants (`invariant`) and variants (`variant` or `modifies`)

`Assert`, `assume`, `invariant`, `post` and `pre` takes a list of *named expr*. 
Named expressions are a tuple of an expression (`<expr>`) and an optional name (`<id>`), written as `<id> : <expr>`.
The given name is translated into the `:named` attribute. 

In specifications, you can use universal `(\forall <binder>; <expr>)` and
existential quantification `(\forall <binder>; <expr>)` and implication
(`==>`).

An example:

```pascal
procedure main();
var  i : int; a : int[];
pre true
post (\forall y:int; 0 <= y and  y < 10 ==> a[y] = y)
begin
    i := 0;    
    while( i < 10 )  
    invariant a % 2 = 0
    variant i, a
    do
    begin
        a[i] := i;
        i := i + 1;
    end
end
```






