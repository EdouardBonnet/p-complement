import Lax554803.ComplementClosure
import Mathlib.Logic.Equiv.Bool

namespace Lax554803Proofs

open Lax554803.PolynomialTime

/-- Exchange the two output-symbol interpretations, retaining the machine and its time bound. -/
def negateOutput {f : Word → Bool}
    (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool f) :
    Turing.TM2ComputableInPolyTime id Computability.encodeBool (fun w ↦ !(f w)) where
  tm := M.tm
  inputAlphabet := M.inputAlphabet
  outputAlphabet := M.outputAlphabet.trans Equiv.boolNot
  time := M.time
  outputsFun w := by
    change Turing.TM2OutputsInTime M.tm
      (List.map M.inputAlphabet.invFun w)
      (some [M.outputAlphabet.invFun (!(!(f w)))]) (M.time.eval w.length)
    simpa only [Computability.encodeBool, List.map_cons, List.map_nil, Bool.not_not]
      using M.outputsFun w

/--
---
conclusion: Lax554803.ComplementClosure.closed_under_complement
---
Negate the characteristic function of the language. Exchanging the two
output-symbol interpretations of its Turing machine computes this negated
function with the same execution and polynomial bound.

# Proof strategy

Compose the machine's output-alphabet equivalence with Boolean negation.
The physical output encoding of the negated answer is then exactly the
original output encoding, so the existing bound on the run applies directly.
Negating the characteristic function's correctness equivalence identifies
the decided language with the complement.
-/
theorem closed_under_complement (L : Language) : L ∈ P → Lᶜ ∈ P := by
  rintro ⟨f, hf, ⟨M⟩⟩
  refine ⟨fun w ↦ !(f w), ?_, ⟨negateOutput M⟩⟩
  intro w
  change (Bool.not (f w) = true) ↔ w ∉ L
  rw [← hf w]
  cases f w <;> decide

end Lax554803Proofs
