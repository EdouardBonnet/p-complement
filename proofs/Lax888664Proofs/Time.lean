import Mathlib.Computability.StateTransition
import Lean.Elab.Tactic.Omega

/-! Finite runs, with explicit transition counts, used by the machine simulations. -/

namespace Lax888664Proofs.Time

variable {α β : Type*}

/-- A run of exactly `n` successful transitions. The endpoint is still a configuration. -/
inductive Run (step : α → Option α) : ℕ → α → α → Prop
  | zero (a : α) : Run step 0 a a
  | cons {n : ℕ} {a b c : α} :
      step a = some b → Run step n b c → Run step (n + 1) a c

namespace Run

variable {step : α → Option α} {n m : ℕ} {a b c : α}

theorem one (h : step a = some b) : Run step 1 a b := .cons h (.zero b)

theorem trans (h : Run step n a b) (h' : Run step m b c) :
    Run step (n + m) a c := by
  induction h with
  | zero => simpa using h'
  | cons hs _ ih => simpa [Nat.add_right_comm] using Run.cons hs (ih h')

theorem iterate (h : Run step n a b) :
    (fun x : Option α ↦ x.bind step)^[n] (some a) = some b := by
  induction h with
  | zero => rfl
  | cons hs _ ih => simpa [Function.iterate_succ_apply, hs] using ih

theorem none_iterate (step : α → Option α) (n : ℕ) :
    (fun x : Option α ↦ x.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [Function.iterate_succ_apply] using ih

theorem of_iterate
    (h : (fun x : Option α ↦ x.bind step)^[n] (some a) = some b) :
    Run step n a b := by
  induction n generalizing a with
  | zero => exact Option.some.inj h ▸ .zero a
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    simp only [Option.bind_some] at h
    cases hs : step a with
    | none => rw [hs, none_iterate] at h; contradiction
    | some c => exact .cons hs (ih (by simpa only [hs] using h))

theorem of_step_eq {a' : α} (h : Run step n a b) (hn : 0 < n)
    (he : step a' = step a) : Run step n a' b := by
  cases h with
  | zero => omega
  | cons hs ht => exact .cons (he.trans hs) ht

theorem map {step' : β → Option β} (f : α → β)
    (hs : ∀ x y, step x = some y → step' (f x) = some (f y))
    (h : Run step n a b) : Run step' n (f a) (f b) := by
  induction h with
  | zero => exact .zero _
  | cons h _ ih => exact .cons (hs _ _ h) ih

theorem invariant (I : α → Prop) (hs : ∀ x y, I x → step x = some y → I y)
    (h : Run step n a b) (ha : I a) : I b := by
  induction h with
  | zero => exact ha
  | cons h _ ih => exact ih (hs _ _ ha h)

/-- Lift a run through a transition-preserving representation, without changing its length. -/
theorem lift {step' : β → Option β} (f : β → α)
    (hs : ∀ x, (step' x).map f = step (f x))
    (h : Run step n a b) {a' : β} (ha : f a' = a) :
    ∃ b', f b' = b ∧ Run step' n a' b' := by
  induction h generalizing a' with
  | zero => exact ⟨a', ha, .zero a'⟩
  | cons h ht ih =>
    have he := hs a'
    rw [ha, h] at he
    cases h' : step' a' with
    | none => simp [h'] at he
    | some d =>
      have hd : f d = _ := Option.some.inj (by simpa only [h', Option.map_some] using he)
      obtain ⟨b', hb', hr⟩ := ih hd
      exact ⟨b', hb', .cons h' hr⟩

end Run

/-- A bounded run. Halting, when required, is stated separately about its endpoint. -/
def Within (step : α → Option α) (t : ℕ) (a b : α) : Prop :=
  ∃ n ≤ t, Run step n a b

namespace Within

variable {step : α → Option α} {n m : ℕ} {a b c : α}

theorem refl (a : α) : Within step 0 a a := ⟨0, le_rfl, .zero a⟩

theorem one (h : step a = some b) : Within step 1 a b := ⟨1, le_rfl, .one h⟩

theorem mono (h : Within step n a b) (hn : n ≤ m) : Within step m a b := by
  obtain ⟨t, ht, h⟩ := h
  exact ⟨t, ht.trans hn, h⟩

theorem trans (h : Within step n a b) (h' : Within step m b c) :
    Within step (n + m) a c := by
  obtain ⟨t, ht, h⟩ := h
  obtain ⟨s, hs, h'⟩ := h'
  exact ⟨t + s, Nat.add_le_add ht hs, h.trans h'⟩

theorem of_evals (h : StateTransition.EvalsToInTime step a (some b) n) :
    Within step n a b := ⟨h.steps, h.steps_le_m, .of_iterate h.evals_in_steps⟩

noncomputable def evals (h : Within step n a b) :
    StateTransition.EvalsToInTime step a (some b) n where
  steps := h.choose
  steps_le_m := h.choose_spec.1
  evals_in_steps := h.choose_spec.2.iterate

end Within

/-- Compose a simulation whose cost per source transition is bounded uniformly. -/
theorem simulate_constant {step : α → Option α} {step' : β → Option β}
    (R : α → β → Prop) (C : ℕ)
    (hs : ∀ a b a', step a = some b → R a a' →
      ∃ b', R b b' ∧ Within step' C a' b')
    {n : ℕ} {a b : α} {a' : β} (h : Run step n a b) (ha : R a a') :
    ∃ b', R b b' ∧ Within step' (n * C) a' b' := by
  induction h generalizing a' with
  | zero => exact ⟨a', ha, (Within.refl a').mono (by simp)⟩
  | cons h _ ih =>
    obtain ⟨c', hc', hr⟩ := hs _ _ _ h ha
    obtain ⟨b', hb', ht⟩ := ih hc'
    exact ⟨b', hb', (hr.trans ht).mono (by simp [Nat.add_mul, Nat.add_comm])⟩

end Lax888664Proofs.Time
