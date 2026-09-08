import Lax554803.ModelEquivalence
import Lax554803Proofs.StackToTape
import Lax554803Proofs.TapeToStack
import Lax554803Proofs.ComplementClosure

namespace Lax554803Proofs.ModelEquivalence

open Lax554803.PolynomialTime Lax554803.MachineModels

/--
---
conclusion: Lax554803.ModelEquivalence.finiteStackP_eq_P
---
Retain all input/output symbols and all symbols occurring in the ranges of
push instructions. This set is finite because both the program and its store
are finite. Restriction to these symbols preserves each transition and the
original time polynomial.
-/
theorem finiteStackP_eq_P : FiniteStackP = P := FiniteAlphabet.finiteStackP_eq_P

/--
---
conclusion: Lax554803.ModelEquivalence.singleTapeP_eq_P
---
Compile stacks to tracks on a single tape, with a proved quadratic overhead
in the source run length and a linear input scan. Expand the resulting finite
instruction blocks into elementary transitions and restrict to their finite
control support. Conversely, represent a tape by two stacks, simulating each
elementary transition in one stack transition; include input conversion and
final erasure in the linear bound. Both compilers use one fixed machine for
all inputs and preserve the Boolean answer.
-/
theorem singleTapeP_eq_P : SingleTapeP = P :=
  Set.Subset.antisymm TapeToStack.singleTapeP_subset_P StackToTape.P_subset_singleTapeP

/--
---
conclusion: Lax554803.ModelEquivalence.singleTape_closed_under_complement
---
Transport the established complement theorem across the proved class equality.
-/
theorem singleTape_closed_under_complement (L : Language) :
    L ∈ SingleTapeP → Lᶜ ∈ SingleTapeP := by
  rw [singleTapeP_eq_P]
  exact Lax554803Proofs.closed_under_complement L

end Lax554803Proofs.ModelEquivalence
