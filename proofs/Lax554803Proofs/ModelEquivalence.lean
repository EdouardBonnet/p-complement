import Lax554803.ModelEquivalence
import Lax554803.FiniteStackEquivalence
import Lax554803.SingleTapeComplement
import Lax554803.ComplementClosure
import Lax554803Proofs.StackToTape
import Lax554803Proofs.TapeToStack
import Lax554803Proofs.ComplementClosure

namespace Lax554803Proofs.ModelEquivalence

open Lax554803.PolynomialTime Lax554803.MachineModels

/--
---
conclusion: Lax554803.FiniteStackEquivalence.finiteStackP_eq_P
---
Retain the input/output symbols and the finite ranges of push instructions.
Restricting each stack alphabet to these symbols preserves every transition
and the original time polynomial.
-/
theorem finiteStackP_eq_P : FiniteStackP = P := FiniteAlphabet.finiteStackP_eq_P

/-- Direct class equality, without any concept-statement assumptions. -/
theorem singleTapeP_eq_P_closed : SingleTapeP = P :=
  Set.Subset.antisymm TapeToStack.singleTapeP_subset_P StackToTape.P_subset_singleTapeP

/--
---
conclusion: Lax554803.ModelEquivalence.singleTapeP_eq_P
assumptions:
  - Lax554803.FiniteStackEquivalence.finiteStackP_eq_P
---
After restricting stack alphabets, compile stacks to tape tracks with polynomial
overhead. Conversely, simulate a tape by two stacks with linear overhead.
Both bounds include input conversion and final output conversion.
-/
theorem singleTapeP_eq_P : SingleTapeP = P :=
  Set.Subset.antisymm TapeToStack.singleTapeP_subset_P (by
    rw [← Lax554803.FiniteStackEquivalence.finiteStackP_eq_P]
    exact StackToTape.finiteStackP_subset_singleTapeP)

/--
---
conclusion: Lax554803.SingleTapeComplement.closed_under_complement
assumptions:
  - Lax554803.ModelEquivalence.singleTapeP_eq_P
  - Lax554803.ComplementClosure.closed_under_complement
---
Transport the established complement theorem across the proved class equality.
-/
theorem singleTape_closed_under_complement (L : Language) :
    L ∈ SingleTapeP → Lᶜ ∈ SingleTapeP := by
  rw [Lax554803.ModelEquivalence.singleTapeP_eq_P]
  exact Lax554803.ComplementClosure.closed_under_complement L

end Lax554803Proofs.ModelEquivalence
