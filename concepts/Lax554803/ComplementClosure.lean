import Lax554803.PolynomialTime

/-!
---
title: P is closed under complement
type: theorem
---
If a language of binary strings belongs to $\mathrm{P}$, then its complement
also belongs to $\mathrm{P}$. The complement is taken in the set of all finite
binary strings.
-/

namespace Lax554803.ComplementClosure

open Lax554803.PolynomialTime

/-- The complement of a polynomial-time decidable language is polynomial-time decidable. -/
axiom closed_under_complement (L : Language) : L ∈ P → Lᶜ ∈ P

end Lax554803.ComplementClosure
