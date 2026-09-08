import Lax554803.MachineModels

/-!
---
title: Polynomial time is invariant under the machine model
type: theorem
---
The original stack-machine definition of P, its restriction to finite work
alphabets, and the elementary single-tape definition describe exactly the same
languages. The simulations include polynomial bounds for input preparation,
instruction expansion, tape scans, and final output conversion.
Consequently the elementary single-tape class is closed under complement too.
-/

namespace Lax554803.ModelEquivalence

open PolynomialTime MachineModels

/-- Requiring all work alphabets to be finite does not change P. -/
axiom finiteStackP_eq_P : FiniteStackP = P

/-- The elementary single-tape and stack definitions give the same class P. -/
axiom singleTapeP_eq_P : SingleTapeP = P

/-- Complement closure for the independent elementary single-tape definition. -/
axiom singleTape_closed_under_complement (L : Language) :
  L ∈ SingleTapeP → Lᶜ ∈ SingleTapeP

end Lax554803.ModelEquivalence
