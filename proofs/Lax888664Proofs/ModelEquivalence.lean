import Lax888664.ModelEquivalence
import Lax888664.FiniteStackEquivalence
import Lax888664.SingleTapeComplement
import Lax888664.ComplementClosure
import Lax888664Proofs.StackToTape
import Lax888664Proofs.TapeToStack
import Lax888664Proofs.ComplementClosure

namespace Lax888664Proofs.ModelEquivalence

open Lax888664.PolynomialTime Lax888664.MachineModels

/--
---
conclusion: Lax888664.FiniteStackEquivalence.finiteStackP_eq_P
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
conclusion: Lax888664.ModelEquivalence.singleTapeP_eq_P
assumptions:
  - Lax888664.FiniteStackEquivalence.finiteStackP_eq_P
---
After restricting stack alphabets, compile stacks to tape tracks with polynomial
overhead. Conversely, simulate a tape by two stacks with linear overhead.
Both bounds include input conversion and final output conversion.
-/
theorem singleTapeP_eq_P : SingleTapeP = P :=
  Set.Subset.antisymm TapeToStack.singleTapeP_subset_P (by
    rw [← Lax888664.FiniteStackEquivalence.finiteStackP_eq_P]
    exact StackToTape.finiteStackP_subset_singleTapeP)

/--
---
conclusion: Lax888664.SingleTapeComplement.closed_under_complement
assumptions:
  - Lax888664.ModelEquivalence.singleTapeP_eq_P
  - Lax888664.ComplementClosure.closed_under_complement
---
Transport the established complement theorem across the proved class equality.
-/
theorem singleTape_closed_under_complement (L : Language) :
    L ∈ SingleTapeP → Lᶜ ∈ SingleTapeP := by
  rw [Lax888664.ModelEquivalence.singleTapeP_eq_P]
  exact Lax888664.ComplementClosure.closed_under_complement L

end Lax888664Proofs.ModelEquivalence
