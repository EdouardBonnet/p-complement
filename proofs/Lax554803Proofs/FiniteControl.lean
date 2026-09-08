import Lax554803Proofs.Time
import Lax554803.MachineModels

/-! Restrict a finitely supported elementary machine to an actual finite state type. -/

namespace Lax554803Proofs.FiniteControl

open Turing Time

variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q]
variable (M : TM0.Machine Γ Q) (S : Finset Q) (hS : TM0.Supports M (S : Set Q))

@[reducible] def initial : Inhabited {q // q ∈ S} := ⟨⟨default, hS.1⟩⟩

def restrict : @TM0.Machine Γ {q // q ∈ S} (initial M S hS) :=
  fun q a ↦ match h : M q.val a with
    | none => none
    | some p => some (⟨p.1, hS.2 h q.property⟩, p.2)

def decode (c : TM0.Cfg Γ {q // q ∈ S}) : TM0.Cfg Γ Q :=
  ⟨c.q.val, c.Tape⟩

theorem step (c : TM0.Cfg Γ {q // q ∈ S}) :
    (@TM0.step Γ _ (initial M S hS) _ (restrict M S hS) c).map (decode S) =
      TM0.step M (decode S c) := by
  rcases c with ⟨q, T⟩
  simp only [TM0.step, restrict, decode]
  split <;> simp_all [decode]

/-- Every finite run lifts without any time overhead. -/
theorem run {n : ℕ} {a b : TM0.Cfg Γ Q} (h : Run (TM0.step M) n a b)
    (ha : a.q ∈ S) :
    ∃ b' : TM0.Cfg Γ {q // q ∈ S},
      decode S b' = b ∧
      Run (@TM0.step Γ _ (initial M S hS) _ (restrict M S hS)) n
        ⟨⟨a.q, ha⟩, a.Tape⟩ b' :=
  h.lift (decode S) (step M S hS) rfl

theorem halted (c : TM0.Cfg Γ {q // q ∈ S})
    (h : TM0.step M (decode S c) = none) :
    @TM0.step Γ _ (initial M S hS) _ (restrict M S hS) c = none := by
  have he := step M S hS c
  rw [h] at he
  exact Option.map_eq_none_iff.mp he

end Lax554803Proofs.FiniteControl
