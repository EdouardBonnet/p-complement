import Lax888664.ComplementClosure
import Mathlib.Logic.Equiv.Bool

set_option backward.isDefEq.respectTransparency false

namespace Lax888664Proofs

open Lax888664.PolynomialTime

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
      using! M.outputsFun w

/--
---
conclusion: Lax888664.ComplementClosure.closed_under_complement
---
Compose the output-alphabet equivalence with Boolean negation. The same
machine execution then computes the complemented answer with the same time
bound. Negating the correctness equivalence identifies the complement language.
-/
theorem closed_under_complement (L : Language) : L ∈ P → Lᶜ ∈ P := by
  rintro ⟨f, hf, ⟨M⟩⟩
  refine ⟨fun w ↦ !(f w), ?_, ⟨negateOutput M⟩⟩
  intro w
  change (Bool.not (f w) = true) ↔ w ∉ L
  rw [← hf w]
  cases f w <;> decide

end Lax888664Proofs
