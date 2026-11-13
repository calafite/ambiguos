# ambiguos

Minimalist proof assistant and dependently typed programming language based on the Calculus of Constructions with Martin-Löf identity types and floating universes (typical ambiguity).

---

### Quickstart

Build and verify the standard prelude:

```sh
cabal build
cabal run ambiguos -- prelude.amb
```

Running without arguments starts an empty REPL session:

```sh
cabal run ambiguos
```

```text
● Verifying prelude.amb...
✓ Verified prelude.amb (66 definitions)
  identity, id, constant, flip, compose, (.), apply, ($), symmetry
  transitivity, congruence, congruence2, substitute, transport, Not
  absurd, doubleNegation, contraposition, Unit, unit, Ordering, less
  equal, greater, Bool, true, false, not, and, (&&), booleanAnd
  or, (||), booleanOr, xor, booleanXor, ifThenElse, booleanEliminator
  boolToType, trueNotEqualFalse, falseNotEqualTrue, Pair, pair, first
  second, fst, snd, swap, curry, uncurry, mapPair, nonContradiction
  Sigma, dependentPair, proj1, proj2, Either, left, right, either
  Maybe, nothing, just, maybe, fromMaybe, isJust, isNothing, mapMaybe
  bindMaybe, predecessor, pred, isZero, addition, (+), multiplication
  (*), power, (^), factorial, subtraction, (-), equalNat, (==)
  notEqualNat, (/=), lessOrEqualNat, (<=), lessThanNat, (<)
  greaterOrEqualNat, (>=), greaterThanNat, (>), compareNat, min, max
  even, odd, List, nil, cons, foldRight, foldr, foldLeft, foldl
  length, map, append, (++), concat, reverse, filter, all, any, isNil
  isCons, headMaybe, head, tail, replicate, take, drop, zipWith, zip

Ambiguos interactive REPL ready.
Type expressions or 'quit' to exit.
```

---

## REPL Commands

```text
def <name> [: <type>] = <term>   typecheck and bind a global definition
<expr>                           infer type and evaluate term to normal form
:load <file>                     typecheck and load definitions from file, resetting context (alias: :l)
:add <file>                      typecheck and load definitions from file, layering onto context (alias: :a)
:reload | :r                     reload the last loaded file from an empty context
:type <expr> | :t <expr>         synthesize and print the normalized type of <expr>
:info <ident> | :i <ident>       show information about an identifier
:browse | :env                   list all data types and symbols in scope with their types
:goals                           re-print unsolved goals from the most recent statement
:set +implicits | -implicits     show or hide implicit arguments in output
:help | :?                       show a summary of REPL commands and syntax
:paste                           paste mode (empty line or Ctrl-D to finish)
:!<command>                      execute a system shell command
quit                             exit the interactive session
```

---

## Syntax

### Types and Universes

```amb
Type                             floating universe (typical ambiguity)
Type 0, Type 1, ...              explicit universe hierarchy
Void                             empty type
Nat                              built-in Peano natural numbers
Id A x y                         identity type (propositional equality)
```

### Functions and Pi Types

```amb
(x : A) -> B                     dependent function type (explicit)
{x : A} -> B                     dependent function type (implicit)
A -> B                           non-dependent function type
(x y : A) -> B                   telescope grouping

\x -> t                          lambda abstraction (inferred)
\(x : A) -> t                    lambda abstraction (explicit)
\{x : A} -> t                    lambda abstraction (implicit)

f x                              explicit application
f {x}                            implicit application override
```

### Equality and Primitives

```amb
refl A x                         reflexivity: Id A x x
J A x P d y p                    Paulson's J eliminator for Id
abort A v                        ex falso quodlibet (eliminator for Void)
natRec P z s n                   primitive recursor for Nat
```

### Literals and Sugar

```amb
0, 1, 2, ...                     desugars to zero / successor chains
[x, y, z]                        desugars to cons x (cons y (cons z nil))
_                                elaboration hole / placeholder
term : Type                      explicit type annotation
x + y                            infix operator application
```

---

## Examples

From `prelude.amb`:

### Symmetry of Identity

```amb
def symmetry : {A : Type} -> {x y : A} -> Id A x y -> Id A y x
  = \p -> J A x (\(z : A) -> \_ -> Id A z x) (refl A x) y p
```

### Congruence

```amb
def congruence : {A B : Type} -> (f : A -> B) -> {x y : A} -> Id A x y -> Id B (f x) (f y)
  = \f p -> J A x (\(z : A) -> \_ -> Id B (f x) (f z)) (refl B (f x)) y p
```

### Natural Induction

```amb
def addition : Nat -> Nat -> Nat
  = \x y -> natRec (\_ -> Nat) y (\_ -> \rec -> successor rec) x

def additionZeroRight : (x : Nat) -> Id Nat (addition x 0) x
  = \x -> natRec (\(n : Nat) -> Id Nat (addition n 0) n)
               (refl Nat 0)
               (\(k : Nat) -> \(ih : Id Nat (addition k 0) k) ->
                   congruence successor ih)
               x
```

### binders.amb / bindings.amb

`bindings.amb` builds on `prelude.amb` and can be loaded after it with `:add bindings.amb` or `:load` it from a prelude context:

```amb
def additionZeroRight : (x : Nat) -> Id Nat (addition x 0) x
  = \x ->
      let motive = \(n : Nat) -> Id Nat (addition n 0) n in
      let base   = refl Nat 0 in
      let step   = \(k : Nat) -> \(ih : Id Nat (addition k 0) k) -> congruence successor ih in
      natRec motive base step x
```

---

## Verification Pipeline

Verification proceeds in five distinct stages:

1. **Automata-driven Lexer**: Keywords, operators, and identifiers are tokenized using compiled DFAs (`Automata.DFA`).
2. **Recursive Descent Parser**: Builds surface AST expressions while desugaring numeric literals, list brackets, and telescopes (`Parser`). Every parsed expression is wrapped in source-span location info (`Located`) for rich diagnostics.
3. **Elaboration & Metavariables**: Bidirectional checking (`synthesize` / `check`) instantiates implicit arguments and solves unification constraints (`TypeChecker`). Type errors carry source spans and an elaboration trace.
4. **Weak Head Normalization**: Evaluates definitions, beta-reductions, $\iota$-reductions on `J`, and primitive recursion on `natRec` (`Evaluation`).
5. **Definitional Equality**: Converts terms to normal form modulo alpha-equivalence to verify conversion rules and proof certificates (`Evaluation.equalNeutral` now correctly compares `case` branches, constructor tags, arities, bodies, and environments).

---

## License

MIT
