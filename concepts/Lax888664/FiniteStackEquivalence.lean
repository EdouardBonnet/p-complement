import Lax888664.MachineModels

/-!
---
title: Finite stack alphabets suffice
type: theorem
---
Requiring every work-stack alphabet to be finite leaves $\mathrm{P}$ unchanged.
-/

namespace Lax888664.FiniteStackEquivalence

open PolynomialTime MachineModels

/-- Requiring all work alphabets to be finite does not change P. -/
axiom finiteStackP_eq_P : FiniteStackP = P

end Lax888664.FiniteStackEquivalence
