**Formalization audit of lax-554803**

Audited the definition and proof at source commit
`89d8425ede159c7586f942a5f7580fa91bed434d`, together with their actual
dependencies in the pinned mathlib checkout. The local mathlib commit matches
the manifest: `c5ea00351c28e24afc9f0f84379aa41082b1188f`, under Lean `v4.30.0`.

No correctness defect was found in the definition of P or the complement
proof. The original concept and proof files are unchanged. The distinction
between a theorem checked by Lean and the mathematical identification of the
chosen machine model with textbook P is described below.

**Uniformity and the decision problem.**
The definition chooses one function and one machine witness before quantifying
over inputs. That witness contains one polynomial. It therefore requires a
single algorithm and bound valid for all binary strings. The membership
equivalence is two-sided: `true` means membership and `false` means
nonmembership. The audit proves the latter explicitly as `negative_answers`.

**Encodings and input size.**
The input encoding is the identity on `List Bool`. The machine's input alphabet
is equivalent to `Bool`, and this equivalence is applied separately to each
symbol. It preserves length and cannot perform input-dependent preprocessing.
The output encoding is a singleton list. The two possible physical outputs
are distinct because the output-alphabet equivalence is injective; this is
checked by `answer_encodings_distinct`. Neither encoding can conceal a decision
procedure for the language.

**Actual halting and actual transition counts.**
`operational_spec` unfolds the requirement to an equality asserting that
iterating the machine's step function a finite number `t` of times reaches
the specified configuration, with `t ≤ p(w.length)`. That target is
`some (haltList ...)`, whose label is `none`. The audit separately proves
that its next transition is `none`. A merely intermediate configuration or
a divergent run cannot satisfy this requirement. It holds for rejecting
inputs and for the empty word as well as for accepting inputs.

The natural-coefficient polynomial is an upper bound for every input length.
This agrees with the usual asymptotic definition of polynomial time: a
polynomial is asymptotically bounded by a monomial, and finitely many small
lengths can be covered by increasing the constant coefficient. The standard
definition is given in [Watrous, Lecture 19, §19.3](https://cs.uwaterloo.ca/~watrous/ToC-notes/ToC-notes.19.pdf).

**The subtle finiteness condition.**
The actual `FinTM2` structure explicitly makes the stack index type, program
label type, internal state type, and input alphabet finite. It does **not**
require every ambient work-stack alphabet to be finite. The comment next to
`Γk₀Fin` in mathlib should not be read as such a requirement.

This does not give these machines access to infinitely many usable symbols.
I proved `reachable_alphabet_finite` in [audit/Checks.lean](audit/Checks.lean):
for every `FinTM2`, there is one finite set of tagged stack symbols that
contains every symbol in every configuration reachable from every possible
input. The set consists of the input alphabet and the ranges of all `push`
instructions. Each such range is finite because the internal state type is
finite. There are finitely many instructions in each program body and finitely
many program labels. Induction through `stepAux` and reachability proves the
invariant; `pop`, `peek`, `load`, and branching introduce no additional symbols.

Consequently, restricting the instruction functions to the symbols and states
that can occur gives finite lookup tables. The potentially infinite ambient
types do not provide an oracle or unbounded integer arithmetic. The finite
support invariant is checked by Lean; the compilation to lookup tables is the
mathematical consequence used in this audit.

**Instruction blocks and the cleanup convention.**
One mathlib transition executes a finite statement body. The recursive calls
of `stepAux` descend through that body's syntax; `goto` returns a new
configuration instead of executing another program body recursively. The
maximum body size over the finite label set is therefore a machine-dependent
constant `B`. A run of `t` transitions performs at most `B * t` primitive
operations and creates at most that many new stack entries.

`haltList` also requires the internal state to be reset and every stack except
the output stack to be empty. This is stronger than the usual halting
convention. It preserves the class P: from an input of length `n`, at most
`n + B * t` entries require cleanup. Clearing them and writing one answer bit
costs polynomial time. This argument concerns membership in P; it does not
assert equality of exact running times between different machine conventions.

The standard simulations use two stacks for a tape, and tracks of a tape for
a fixed collection of stacks. Combining those constructions with the bounds
above gives polynomial overhead in both directions. This is the audit's
complexity analysis of the constructions in
[Watrous, Lecture 14, §14.2](https://cs.uwaterloo.ca/~watrous/ToC-notes/ToC-notes.14.pdf).

**Complement construction.**
Let `e` be the original output-alphabet equivalence. The new witness uses
`Bool.not ∘ e`, with exactly the original machine, input equivalence, and
polynomial. Its physical encoding of the negated answer satisfies

```text
(Bool.not ∘ e)⁻¹ (Bool.not (f w)) = e⁻¹ (f w).
```

Thus the original execution certificate proves the new output requirement,
including the halting configuration and time bound. The proof changes a
fixed two-symbol interpretation that is explicitly part of the machine
interface. It does not add an input-dependent decoder. The final Boolean
case split proves that the new `true` answer means membership in the
complement of the original language. `complement_iff` also checks the converse
by applying closure twice.

**Nonvacuity and proof trust.**
The audit constructs a finite one-stack machine computing length parity. An
induction proves its output and exact `n + 1` transition count for all words,
including the final cleanup. This gives `nontrivial_language_in_P`: a language
in P that rejects the empty word and accepts a one-bit word. The closure
statement is therefore not being validated only in an empty class.

The submitted definition, machine transformation, and closure theorem each
use only `propext` and `Quot.sound`. In particular, the closure theorem does
not assume its concept-package statement. Some independent audit lemmas also
use the permitted `Classical.choice`. No audit lemma uses an unproved
statement. The general polynomial-time composition claim marked
`proof_wanted` in the pinned mathlib source is not used.

**What is and is not formally certified.**
Lean certifies complement closure for the precise mathlib-based definition.
The additional audit file certifies the operational interpretation, terminal
output, finite reachable alphabet, and a nonconstant polynomial-time example.
The complete two-way polynomial simulation between this interface and a
separately defined textbook single-tape P, including cleanup, is not a theorem
of this submission. Its justification above is mathematical audit reasoning.
This is a limit on the extent of the formal development, not an outstanding
proof obligation of the submitted complement theorem.

The independent checks can be reproduced from `proofs/`:

```sh
lake env lean ../audit/Checks.lean
```

The archive checks can be reproduced from the submission root:

```sh
lax build . --replay
```

The audit file is outside the concept and proof packages. Lax's replay checks
the submission packages; the separate Lean command checks the audit lemmas.
