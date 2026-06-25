# Compiling SKI to the Nock {0, 1, 2} Fragment

**A four-rule transformation, with worked examples and machine-checked validation**

*~your-sigil*
*Affiliation*

> **Draft for *Urbit Systems Technical Journal*.** Byline, affiliation, and
> volume reference are placeholders. All Nock formulas and reduction traces in
> this paper were generated and checked mechanically (see §6); the source is
> reproducible.

## Abstract


## 1. Introduction

The combinatory reading of Nock is well established. Smullyan-style combinator
calculi build all computation from a handful of variable-free operators, and the
SKI system does it with three (Curry and Feys 1958). The Nock literature draws
the parallel directly: "Nock at its heart is SKI dressed up with some machinery
to handle nouns," with opcodes 2, 1, and 0 cast as S, K, and I respectively
(combinator-approach, *nock.is*). The *Documentary History of the Nock
Combinator Calculus* states the same correspondence and then sets the details
aside: there are "some subtle differences to Nock's expression of S as opcode 2
that we will elide as being fundamentally similar, but perhaps worthy of its own
monograph" (Davis and Yarvin 2025).

That elision matters more than it appears. The opcode-to-combinator analogy is
not a compilation procedure. SKI terms are curried and higher-order:
combinators are routinely partially applied, and a combinator may be passed as
an argument to another combinator. A symbol-for-symbol substitution — write `2`
where the source says `S`, `1` for `K`, `0` for `I` — produces nothing
runnable the moment `S` has fewer than three arguments, which is almost always.
What is needed is a *homomorphism*: a translation under which Nock application
of compiled terms mirrors SKI reduction, with a fixed convention for how a
compiled combinator receives its arguments.

This paper supplies that homomorphism. It is four rules (§4). The compiled
combinators are three small formulas (§3). The remainder is worked examples
(§5), mechanical validation against the `pinochle` interpreter (§6), a cost
analysis (§7), and an honest accounting of the limitations (§8).

## 2. Preliminaries

We assume Nock 4K. Evaluation is the function `*[subject formula]`. We use only
three rules:

```
*[a 0 b]    ->  /[b a]          :: slot: fetch the noun at tree address b
*[a 1 b]    ->  b               :: quote: return b unchanged
*[a 2 b c]  ->  *[*[a b] *[a c]] :: eval: compute a subject and a formula, then run
```

plus the structural distribution (autocons) rule, which fires whenever a
formula's head is itself a cell:

```
*[a [b c] d]  ->  [*[a b c] *[a d]]
```

Slot address 1 denotes the whole subject, so `*[a 0 1] = a`.

**The application convention.** A *value* is a Nock formula that consumes its
argument as the *subject*. To apply a value `v` to an argument `x` we evaluate

```
apply(v, x)  ==  *[x v].
```

This is the only design choice in the paper, and everything else is forced by
it. The convention inverts the lambda-calculus argument order — in Nock the
function is the formula and the argument is the subject — which is exactly the
"opposite argument order" noted but not exploited in the existing combinator
material.

## 3. The combinators as formulas

Under the convention of §2, each SKI combinator is a closed Nock formula. We
give each, then verify its defining law by reduction.

### 3.1 I — identity

`I x = x` requires `*[x I] = x`, which is slot 1:

```
I  =  [0 1]
```

### 3.2 K — constant

`K x y = x`. Applying `K` to `x` must yield a value that ignores its next
argument and returns `x` — that is, the constant formula `[1 x]`. So we need
`*[x K] = [1 x]`. Build the cell `[1 x]` from subject `x` by autocons:

```
K  =  [[1 1] [0 1]]
```

Check: `*[x K] = [*[x [1 1]] *[x [0 1]]] = [1 x]`. Then for any `y`,
`*[y [1 x]] = x`. Both stages hold.

### 3.3 S — substitution

`S x y z = (x z)(y z)`. The combinator accumulates `x`, then `y`, then fires on
`z`. We construct it bottom-up.

When the fully-applied `Sxy` finally receives `z` as subject, it must produce
`(x z)(y z)`. Under the convention, `x z = *[z x]` and `y z = *[z y]`, and the
outer application is `*[ *[z y]  *[z x] ]`. That is precisely opcode 2 with
subject `z`, formula-`b` equal to `y`, formula-`c` equal to `x`:

```
Sxy  =  [2 y x]          ::  *[z [2 y x]] = *[*[z y] *[z x]] = (x z)(y z)
```

Working back one step, applying `Sx` to `y` (subject `y`, constant `x`) must
build the noun `[2 y x]`:

```
Sx  =  [[1 2] [0 1] [1 x]]
```

Check: `*[y Sx] = [2 y x]`, since `*[y [1 2]] = 2`, `*[y [0 1]] = y`, and
`*[y [1 x]] = x`. Working back the final step, applying `S` to `x` (subject `x`)
must build `Sx`; the first two parts are constants and the third, `[1 x]`, is
built from `x` by the same autocons trick used for `K`:

```
S  =  [[1 [1 2]] [1 [0 1]] [[1 1] [0 1]]]
```

Check: `*[x S] = [[1 2] [0 1] [1 x]] = Sx`.

### 3.4 Derived combinators by direct derivation

Any other combinator can be reached by elaborating its lambda definition to SKI
and compiling (§4), but the result is large (§7). A named combinator is better
derived directly, by the same method as §3.3: it becomes one builder layer per
argument. The innermost layer is the opcode-2 application skeleton that fires on
the final argument; each enclosing layer is an autocons that captures one
argument and embeds it. We give B, C, and W.

For `B f g x = f (g x)`, the firing step computes `f` applied to `g x`, i.e.
`*[*[x g] f]`, which is opcode 2 with `g` in the formula-`b` slot and `f`
quoted in the formula-`c` slot; capturing `g` then `f` gives:

```
  Bfg = [2 g [1 f]]                          ::  *[x Bfg] = *[*[x g] f] = f (g x)
  Bf  = [[1 2] [0 1] [1 [1 f]]]              ::  *[g Bf]  = [2 g [1 f]]
  B   = [[1 [1 2]] [1 [0 1]] [[1 1] [[1 1] [0 1]]]]
```

The same procedure yields C (flip) and W (diagonal):

```
B  =  [[1 1 2] [1 0 1] [1 1] [1 1] 0 1]      ::  f g x -> f (g x)
C  =  [[1 1 2] [1 [1 1] 0 1] [1 1] 0 1]      ::  f x y -> f y x
W  =  [[1 2] [1 0 1] 0 1]                    ::  f x   -> f x x
```

**Quote versus slot.** The one subtlety is how a captured argument is embedded,
and it is dictated by how the combinator *uses* that argument. If the argument is
applied to a *computed* value — as `B`'s `f` is applied to `g x` — it occupies a
formula slot and is embedded quoted, `[1 f]`. If it is applied to the *current
subject* — as `W`'s `f` is applied to `x` — it must pass through as the live
formula, embedded by slot, `[0 1]`. Quote where the argument is data; slot where
the argument is the active function. Reversing the two embeds `W`'s `f` as a
constant and `W K 7` returns the partial `K 7` rather than `7`.

Notably, the value forms of B, C, and W use only opcodes **0 and 1**. The `2`
appears only in the formula they *assemble* at apply time (`[2 g [1 f]]`),
carried as quoted data. The combinators are pure construction; the application
machinery is the structure they emit. Among the basis only `S` carries a `2` in
its own body, because it performs two applications at once.

The size payoff over bracket abstraction is large (cell counts; see §7 for
method):

| | direct (§3.4) | via SKI (§4) | ratio |
| --- | --- | --- | --- |
| B | 11 | 208 | ~19× |
| C | 11 | 208 | ~19× |
| W | 6 | 130 | ~22× |

The two forms are extensionally identical on every input tested (§6). For any
combinator known by name, direct derivation is preferred and the abstraction tax
is avoided entirely; bracket abstraction remains the general fallback for
arbitrary lambda terms.

## 4. The compiler

Let `[[t]]` denote a *closed* Nock formula whose product is the value of the SKI
term `t`. The compiler is four rules:

```
[[S]]    =  [1 S]
[[K]]    =  [1 K]
[[I]]    =  [1 I]
[[A B]]  =  [2 [[B]] [[A]]]
```

with `S`, `K`, `I` the formulas of §3. The combinators are *quoted* so that
`[[·]]` always denotes a value-producing computation; application is opcode 2
applied to the two compiled operands.

**Why quote, and why this order.** Evaluating `[[A B]] = [2 [[B]] [[A]]]`
against any subject `s` gives `*[ *[s [[B]]]  *[s [[A]]] ]`. Because `[[B]]` and
`[[A]]` are closed, they ignore `s` and reduce to the values `val(B)` and
`val(A)`. The result is `*[val(B) val(A)]` — apply value `val(A)` to argument
`val(B)`, i.e. `A` applied to `B`. The operands are reduced to values *before*
application, which is what makes nested applications compose correctly; quoting
a sub-application rather than evaluating it produces an off-by-one error (a
residual `K` where the value was expected).

**Correctness.** By induction on term structure. The base cases are §3. For
application, the rule computes `apply(val(A), val(B))`, and by the induction
hypothesis `val(A)`, `val(B)` are the values of `A`, `B`; by §2 this is the
value of `A B`. The translation is therefore a homomorphism from SKI
application to Nock evaluation, under the call-by-value strategy forced by
opcode 2's eager semantics (see §8).

## 5. Worked examples

All terms below are written in lambda form for legibility, elaborated to SKI by
standard bracket abstraction (Kiselyov 2018), then compiled by §4 and run. The
results are the products actually computed (§6).

### 5.1 Identity laws

```
I 7         = 7
S K K 7     = 7          :: SKK = I
S K S 7     = 7          :: S K anything = I
```

### 5.2 Church booleans

With `TRUE = K` and `FALSE = K I`:

```
TRUE  7 8   = 7
FALSE 7 8   = 8
```

`TRUE p q = K p q = p` and `FALSE p q = K I p q = I q = q`. These are the
canonical encodings; they probe with atom arguments because neither combinator
applies its arguments as functions.

### 5.3 The B, C, W combinators

Elaborated from their defining lambda terms:

```
B = lambda f g x. f (g x)    composition
C = lambda f x y. f y x      flip
W = lambda f x.   f x x       diagonal
```

Driving B with a real Nock increment `INC = [4 0 1]` as payload, and C, W with
atoms:

```
B INC INC 7  = 9       :: INC (INC 7)
C K 7 8      = 8       :: K 8 7 = 8
W K 7        = 7       :: K 7 7 = 7
```

These exercise three-variable abstraction and argument duplication. Note that
the compiled SKI scaffolding remains pure {0, 1, 2}; the only `4` in `B`'s run
is the external increment supplied as data. The compact native forms of §3.4
produce identical results at a twentieth of the size.

### 5.4 Church numerals and arithmetic

A Church numeral `n` applies its first argument `n` times to its second. We
drive numerals with the genuine Nock increment as the iterated function and the
atom `0` as the base, so the combinatory scaffolding computes ordinary natural
numbers:

```
church k = lambda f x. f^k x
plus     = lambda m n f x. m f (n f x)
mult     = lambda m n f.   m (n f)

church 0 INC 0   = 0
church 3 INC 0   = 3
church 5 INC 0   = 5
(plus 2 3) INC 0 = 5
(mult 3 4) INC 0 = 12
```

This is the thesis of the construction in one line. `church 3 INC 0 = 3`:
variable-free control flow expressed entirely in opcodes 0, 1, and 2, driving a
real computation whose arithmetic lives in the payload, never in the
scaffolding.

## 6. Mechanical validation

Two independent checks were run.

**Reference interpreter.** The compiled formulas were evaluated on `pinochle`
(Davis 2024), a Python implementation of Nock 4K extending Urbit's `pynoun`,
selected because it shares no code with the compiler. Every example in §5 was
run on both a purpose-built {0, 1, 2} evaluator and on `pinochle`; the two
agree on all cases and match the expected values. A representative slice:

| Term | result | pinochle | expected |
| --- | --- | --- | --- |
| `I 7` | 7 | 7 | 7 |
| `S K K 7` | 7 | 7 | 7 |
| `FALSE 7 8` | 8 | 8 | 8 |
| `B INC INC 7` | 9 | 9 | 9 |
| `C K 7 8` | 8 | 8 | 8 |
| `church 3 INC 0` | 3 | 3 | 3 |
| `(plus 2 3) INC 0` | 5 | 5 | 5 |
| `(mult 3 4) INC 0` | 12 | 12 | 12 |

**Fragment check.** Every compiled formula was scanned for opcodes appearing in
formula position. For all pure-SKI terms the set is exactly `{0, 1, 2}`. The
compiled identity `S K K`, for instance, is the closed formula

```
[2 [1 [1 1] 0 1] 2 [1 [1 1] 0 1] 1 [1 1 2] [1 0 1] [1 1] 0 1]
```

which `pinochle` reduces, applied to `7`, to `7`. (Right-nested printing: e.g.
`[[1 1] 0 1]` denotes `[[1 1] [0 1]]`.)

## 7. Cost

The transformation is faithful but not frugal. Measuring SKI leaf count against
compiled Nock cell count:

| term | SKI leaves | Nock cells |
| --- | --- | --- |
| `I` | 1 | 2 |
| `S K K` | 3 | 22 |
| `W` | 16 | 130 |
| `B` | 25 | 208 |
| `C` | 25 | 208 |
| `church 2` | 76 | 640 |
| `church 5` | 187 | 1588 |
| `church 10` | 372 | 3168 |

Compiled Nock runs roughly 8.5x the SKI leaf count — a constant per combinator
plus the opcode-2 application wrapper — and the SKI itself is already
exponential in the worst case under naive bracket abstraction. The natural
number ten compiles to a 3168-cell formula. These figures are static, before
reduction; at runtime `S` duplicates its argument into both branches with no
sharing, so evaluation cost compounds on representation cost.

Named combinators escape this blow-up entirely: derived directly (§3.4) rather
than routed through bracket abstraction, `B`, `C`, and `W` are roughly twenty
times smaller. The cost above is the price of the *general* compiler on
arbitrary terms, not a property of the targets themselves.

## 8. Limitations

Three properties bound the construction. Each is a real boundary, not a
deficiency to be patched away within the fragment.

**Call-by-value.** Opcode 2 is eager: `*[a 2 b c]` fully reduces `*[a b]` and
`*[a c]` before applying. The compilation is therefore applicative-order. A term
whose normal form depends on discarding a divergent subterm will loop. Concretely,
with `omega = S I I` and `Omega = omega omega`, normal-order `K I Omega` reduces
to `I`, but the compiled form diverges — confirmed empirically. For a compilation
*target* this is usually acceptable; for a faithful lazy surface it is not, and
recovering normal order requires explicit thunking, which reintroduces runtime
branching and pulls in opcodes 3 and 6.

**No readback in {0, 1, 2}.** Compiled SKI can be *executed* but its normal form
cannot be *printed* without distinguishing a residual `S` from a `K` from an
application at runtime. That requires the cell/atom test (opcode 3) and a
conditional (opcode 6). The fragment is a faithful execution target, not a
normalizer.

**No sharing.** This is tree reduction. `S` copies its argument with no sharing,
so terms with shared redexes blow up exponentially (§7). Acceptable as an
intermediate representation to compile *through*; unacceptable as a runtime for
large terms, which want graph reduction — and graph reduction wants opcodes
beyond the fragment.

## 9. Conditionals: selection versus decision

A conditional is the obvious stress test for a fragment this small, because in a
strict evaluator a conditional that evaluates both branches is useless for its
principal job — guarding recursion. The fragment passes the test, but only once
the conditional is split into two parts, and the split is the paper's sharpest
boundary.

**Selection is combinatory and free.** Church booleans are already conditionals:
with `TRUE = K` and `FALSE = K I`, the term `b t e` routes to the chosen branch.
Critically, the routing executes *neither* branch. `K` reads its two arguments by
slot and discards one; it never applies them as formulas. So if the branches are
held as quoted formulas (thunks) and only the survivor is run, the unchosen
branch is never evaluated. The whole conditional is one closed formula in the
fragment:

```
IF cond tf ef s  =  [2 [1 s] [2 [1 ef] [2 [1 tf] [1 cond]]]]
```

reading inner to outer: apply `cond` to `tf`, then to `ef` (selection), then run
the survivor on subject `s`. It is fifteen cells, pure {0, 1, 2}.

This conditional is genuinely lazy. Setting the unchosen branch to a crashing
formula confirms it never runs: `IF TRUE 111 ⊥` returns `111` without crashing,
`IF FALSE ⊥ 222` returns `222`, and the control case `IF TRUE ⊥ 222` does crash —
the chosen branch really executes, so the laziness is not an artifact of dead
code. The discipline this requires is exact: branches must be kept as quoted
formulas, *not* compiled as combinator sub-terms. Compile a divergent branch
through §4 and the eager opcode 2 forces it before selection ever happens (the
`K I Ω` divergence of §8). Thunk the branch and it stays inert until forced.

**Decision is not in the fragment.** What the fragment cannot do is manufacture
the boolean. `IF` above routes on a boolean it is *handed*; to branch on a
property of data — "is this atom zero," "is this noun a cell" — one must first map
a datum to `K` or `K I`, and that inspection reads an atom's value or tests
cell-ness. Neither is expressible in {0, 1, 2}. Selecting on a given boolean is
free; deciding what the boolean should be requires the cell test (3), increment
(4), or equality (5).

This is precisely the shape of Nock's own conditional. Opcode 6 is derivable from
opcodes 0–5 (Lindstrom-Vautrin 2025), and what it adds over the selector above is
exactly the data-derived predicate: it runs a formula `b` to compute a loobean on
the subject, maps that loobean to an address with `++` (opcode 4) to pick one of
two formulas, and runs only the chosen one. The selection half is the combinatory
core we have built; the predicate half is the reason opcodes 3, 4, and 5 are the
minimal additions to the SKI basis rather than conveniences. The conditional's
*control* is combinatory and costs nothing; its *decision* requires looking at
data, and looking at data is the first thing the fragment cannot do. That single
boundary is the cleanest available motivation for Nock's actual shape: the SKI
core supplies universal control flow, and a small arithmetic-and-inspection
kernel — `?`, `+`, `=`, packaged with `if` — supplies everything the core
provably cannot.

## 10. Conclusion

The folklore that opcodes 2, 1, 0 "are" S, K, I is an analogy. The algorithm
behind it is four rules and three small formulas, and it is exhibited here,
verified by reduction, exercised on the standard combinators and on Church
arithmetic, and cross-checked against an independent Nock 4K interpreter. As a
corollary, the embedding is a constructive proof that the {0, 1, 2} fragment is
Turing-complete: the monograph the *Documentary History* deferred is a handful
of lines of Nock. A second corollary locates the fragment's edge precisely: a
conditional's *selection* is combinatory and lives in {0, 1, 2}, but its
*decision* — computing a boolean from data — does not, which is exactly why
Nock's basis is the SKI core plus a minimal inspection-and-arithmetic kernel.

The construction's value is pedagogical and foundational, not practical: it is
the right artifact for showing *what compiles to what* and *why the fragment
suffices*, and the wrong artifact for generating Nock anyone would ship. The
practical path forward is twofold and well understood. First, replace naive
bracket abstraction with an optimized abstraction over a richer combinator basis
(Turner's `B`, `C`, `S'` and eta-reduction), which cuts the constant factor in
§7 substantially. Second, target a sharing-aware graph reducer rather than the
tree reducer implied here. Both moves deliberately leave the {0, 1, 2} fragment
— which is the point: the fragment proves universality, and the additional
opcodes earn their place precisely where §8 says the fragment runs out.

## References

Curry, H. B., and R. Feys (1958). *Combinatory Logic*. Amsterdam: North-Holland.

Davis, N. E. ~lagrev-nocfep (2024). *Pinochle: a Python implementation of the
Nock 4K combinator calculus*. https://github.com/sigilante/pinochle.

Davis, N. E. ~lagrev-nocfep, and C. Yarvin ~sorreg-namtyv (2025). "A Documentary
History of the Nock Combinator Calculus." *Urbit Systems Technical Journal*
II:1, 155–190.

Kiselyov, O. (2018). "λ to SKI, Semantically." https://okmij.org/ftp/tagless-final/ski.pdf.

Lindstrom-Vautrin, T. ~niblyx-malnus (2025). "Deriving Nock Opcodes 6–11."
*Urbit Systems Technical Journal* II:1, 47–70.

Schönfinkel, M. (1924). "Über die Bausteine der mathematischen Logik."
*Mathematische Annalen* 92, 305–316.

Tunney, J. (2022). "Lambda Calculus in 383 Bytes." https://justine.lol/lambda/.

*Combinator Approach.* Nock documentation. https://nock.is/content/understanding/combinator-approach.html.
