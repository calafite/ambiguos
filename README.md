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
cabal run ambiguos -- prelude.amb
```

```text
● Verifying prelude.amb...
✓ Verified prelude.amb (67 definitions)
  identity, constant, flip, symmetry, transitivity, congruence
  substitute, Not, absurd, doubleNegation, contraposition, Unit, unit
  Pair, pair, first, second, swap, nonContradiction, Sigma
  dependentPair, Either, left, right, either, Maybe, nothing, just
  maybe, fromMaybe, Bool, true, false, not, booleanAnd, booleanOr
  booleanXor, booleanEliminator, boolToType, trueNotEqualFalse
  predecessor, addition, multiplication, power, factorial, mersenne
  additionZeroLeft, additionZeroRight, additionSuccessorRight
  theoremTwoPlusThree, theoremTwoTimesThree, theoremTwoCubed
  theoremFactorialThree, Factors, IsComposite, mersenneFourFactors
  mersenneSixFactorsBaseTwo, mersenneSixFactorsBaseThree
  mersenneEightFactors, List, nil, cons, foldRight, length, map, append
  addTwoEach

Ambiguos interactive REPL ready.
Type expressions or 'quit' to exit.
```

---

## REPL Commands

```text
def <name> [: <type>] = <term>   typecheck and bind a global definition
<expr>                           infer type and evaluate term to normal form
:load <file>                     typecheck and load definitions from file (alias: :l)
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

---

## Verification Pipeline

Verification proceeds in five distinct stages:

1. **Automata-driven Lexer**: Keywords, operators, and identifiers are tokenized using compiled DFAs (`Automata.DFA`).
2. **Recursive Descent Parser**: Builds surface AST expressions while desugaring numeric literals, list brackets, and telescopes (`Parser`).
3. **Elaboration & Metavariables**: Bidirectional checking (`synthesize` / `check`) instantiates implicit arguments and solves unification constraints (`TypeChecker`).
4. **Weak Head Normalization**: Evaluates definitions, beta-reductions, $\iota$-reductions on `J`, and primitive recursion on `natRec` (`Evaluation`).
5. **Definitional Equality**: Converts terms to normal form modulo alpha-equivalence to verify conversion rules and proof certificates.

---

## License

MIT
