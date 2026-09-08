import Mathlib.Computability.TuringMachine.Computable

/-!
---
title: The complexity class P
type: definition
---
A language of finite binary strings belongs to $\mathrm{P}$ if a deterministic
Turing machine decides membership in that language in polynomial time.
Precisely, there are a single machine and a polynomial $p \in \mathbb{N}[X]$
such that, on every input $w$, the machine halts within $p(|w|)$ steps and
returns the bit $1$ if $w$ belongs to the language and $0$ otherwise.

# Formalization notes

A language is a set of lists of Booleans. Its deciding function has type
`Word → Bool`, and its correctness is expressed by an equivalence between
returning `true` and membership in the language.

`Turing.TM2ComputableInPolyTime` supplies the machine, its polynomial bound,
and a proof that every input reaches the required halting configuration
within that bound. The input encoding is the identity, so the time bound is
evaluated at the binary string's length. `Computability.encodeBool` encodes
the answer as a singleton list. `Nonempty` retains the proposition that
such a machine exists.

Mathlib's machine has finitely many stacks, control states, and program
labels. Its time measure counts transitions, each executing one of the
fixed finite instruction blocks of the program.

`Lax554803.MachineModels` independently defines elementary single-tape P.
The polynomial-time equivalence, including input preparation and cleanup,
is formalized in `Lax554803.ModelEquivalence`.
-/

namespace Lax554803.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

/-- A language of finite binary strings. -/
abbrev Language := Set Word

/-- Languages whose Boolean characteristic functions are computable in polynomial time. -/
def P : Set Language :=
  {L | ∃ f : Word → Bool,
    (∀ w, f w = true ↔ w ∈ L) ∧
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeBool f)}

end Lax554803.PolynomialTime
