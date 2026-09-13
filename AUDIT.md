**Formalization audit of lax-888664**

The original definition and complement proof were audited at source commit
`89d8425ede159c7586f942a5f7580fa91bed434d`. This report also covers the subsequent
formal model-equivalence development. The local mathlib commit matches the
manifest: `c5ea00351c28e24afc9f0f84379aa41082b1188f`, under Lean `v4.30.0`.

The original definition and complement argument are retained. The former
scope limitation is resolved: both inclusions between that class and an
independently defined elementary single-tape P are now proved in Lean,
including polynomial time bounds and both input/output conventions.

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

The submission now also constructs the restricted machine in
[FiniteAlphabet.lean](proofs/Lax888664Proofs/FiniteAlphabet.lean). It retains the
input/output alphabets and all pushed symbols, and uses their subtypes as the
new stack alphabets. Its `block`, `step`, and `outputs` theorems prove that
decoding commutes with execution and preserves the exact transition count.
The `computer` theorem preserves the original time polynomial. This yields
the exported equality `finiteStackP_eq_P`; finite alphabets are no longer
just an informal consequence of the reachability invariant.

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
a fixed collection of stacks; see
[Watrous, Lecture 14, §14.2](https://cs.uwaterloo.ca/~watrous/ToC-notes/ToC-notes.14.pdf).
The bounds needed here are now theorems of the submission, as detailed next.

**Independent single-tape definition.**
[MachineModels.lean](concepts/Lax888664/MachineModels.lean) defines `SingleTape`
using mathlib's elementary `TM0`: a two-sided blank tape, a finite alphabet,
a finite control-state type, and a transition function of the current state
and scanned symbol. A transition writes one symbol or moves the head one
square. Its input embedding maps the two bits injectively to nonblank
symbols. `TM0.init` places them in their original order, with the first symbol
under the head and blanks elsewhere. There is no preprocessing hidden in
this embedding. A finite accepting-state predicate supplies the answer.

`SingleTapeP` chooses one such machine and one polynomial before quantifying
over words. On every word it requires a bounded run to a configuration whose
next transition is `none`, with acceptance equivalent to membership. There is
no requirement that its final work tape be erased. This definition contains
no reference to the stack class or to a simulation certificate.

**Formal simulations and time bounds.**
Let `n` be the input length and `t` the source transition count. All constants
below depend only on the fixed source machine.

| Construction | Formal bound | Proof source |
| --- | --- | --- |
| Restrict work alphabets | Exactly `t` transitions | `FiniteAlphabet.outputs` |
| Stacks to tape instruction blocks | `t * (1 + C * (2 * (n + t*C) + 2))` | `StackTime.run` |
| Ordinary input preparation | At most `n + 1` tape blocks | `TapeInput.prepare` |
| Expand tape blocks to elementary transitions | At most `D` transitions per block | `PostTime.run` |
| Capture the final answer in an accepting state | One transition | `TapeOutput.finish` |
| Restrict to an actual finite control type | Exactly the same transition count | `FiniteControl.run` |
| Single tape to stacks, including input and cleanup | At most `3*n + 2*t + 6` | `TapeToStack.outputs` |

The stack-to-tape construction reuses mathlib's track simulator. Its timed
proof bounds both the scan to each stack top and the return to the bottom
marker. `TapeInput` proves that reflecting the simulated tape permits a
single input scan, rather than assuming the input was supplied in reverse
order. It treats the empty word separately. The existing block-to-elementary
compiler is given a proved constant bound over its finite support. The final
output bit is read into a control state, and the state space is restricted
to the proved finite support.

The complete forward bound is
`D * (n + 1 + t * (1 + C * (2 * (n + t*C) + 2))) + 1`.
Substituting the source polynomial for `t` gives the explicit polynomial used
in [StackToTape.lean](proofs/Lax888664Proofs/StackToTape.lean).

In the reverse construction, two stacks represent the squares to the left
and right of the head; the current square and control state are in the finite
store. Each elementary transition is simulated in one stack transition. The
sum of the two stack lengths grows by at most one per transition. Input
conversion costs `2*n + 3` transitions. Cleanup erases both work stacks,
resets the store, and writes the singleton answer on the Boolean I/O stack.
The resulting polynomial is `3*X + 2*p + 6`, proved in
[TapeToStack.lean](proofs/Lax888664Proofs/TapeToStack.lean).

The equalities and the transported single-tape complement theorem are
exported by [ModelEquivalence.lean](proofs/Lax888664Proofs/ModelEquivalence.lean).

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

The original definition, machine transformation, and closure theorem each
use only `propext` and `Quot.sound`. The new model equivalences also use the
permitted `Classical.choice`, for example to choose finite representations.
The compiler proofs and `singleTapeP_eq_P_closed` use no concept-statement
axioms. The annotated archive proofs cite previously proved concept statements
to expose the mathematical dependencies in Lax's proof network; every such
dependency is discharged within this submission. No proof assumes its own
conclusion, and there are no dependency cycles. No result uses
`sorryAx` or the general polynomial-time composition claim marked
`proof_wanted` in the pinned mathlib source.

The independent audit also proves complement closure directly in
`SingleTapeP` by negating its accepting-state predicate with the same machine
and polynomial. It transfers the nonconstant parity language to this class,
checking that both accepting and rejecting instances exist. The audit prints
the axiom dependencies of both compiler directions, both class equalities,
and both complement arguments.

**Certified results.**
Lean certifies the two class equalities and complement closure for both the
original stack definition and the independent elementary single-tape
definition. The input preparation, finite alphabets and control, simulation
time bounds, final acceptance, and cleanup are included in those proofs.
The separate audit file additionally checks the operational interpretation
and nonconstant examples. The submission does not rely on an informal
stack/tape equivalence to identify these two definitions.

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
