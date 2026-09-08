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

The definition uses mathlib's deterministic stack machines, the identity
encoding of binary strings, and a singleton Boolean output. Time counts
transitions of fixed finite instruction blocks. We also prove equivalence
with elementary single-tape machines.
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
