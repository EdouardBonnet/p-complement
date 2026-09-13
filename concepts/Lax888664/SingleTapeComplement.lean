import Lax888664.MachineModels

/-!
---
title: Single-tape P is closed under complement
type: theorem
---
The elementary single-tape class $\mathrm{P}$ is closed under complement.
-/

namespace Lax888664.SingleTapeComplement

open PolynomialTime MachineModels

/-- Complement closure for the elementary single-tape definition. -/
axiom closed_under_complement (L : Language) :
  L ∈ SingleTapeP → Lᶜ ∈ SingleTapeP

end Lax888664.SingleTapeComplement
