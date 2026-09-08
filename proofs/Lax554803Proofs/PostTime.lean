/-
The block proof adapts mathlib's untimed TM1to0 simulation:
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The adaptation adds explicit elementary-transition counts.
-/
import Lax554803Proofs.Time
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The existing TM1 → TM0 compiler has constant time overhead.
This supplies the quantitative statement missing from its untimed correctness theorem. -/

namespace Lax554803Proofs.PostTime

open Turing Time

variable {Γ Λ σ : Type} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]

/-- Upper bound on the number of elementary tape transitions in one instruction block. -/
def cost : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q | .write _ q => cost q + 1
  | .load _ q => cost q
  | .branch _ q r => max (cost q) (cost r)
  | .goto _ | .halt => 1

omit [Inhabited Γ] [Inhabited Λ] [Inhabited σ] in
theorem cost_pos (q : TM1.Stmt Γ Λ σ) : 0 < cost q := by
  induction q <;> simp_all [cost]

variable (M : Λ → TM1.Stmt Γ Λ σ)

/-- Compile a block: at least one and at most `cost q` elementary transitions. -/
theorem block (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    ∃ n ≤ cost q, 0 < n ∧
      Run (TM0.step (TM1to0.tr M)) n ⟨(some q, v), T⟩
        (TM1to0.trCfg M (TM1.stepAux q v T)) := by
  induction q generalizing v T with
  | move d q ih =>
    obtain ⟨n, hn, hp, hr⟩ := ih v (T.move d)
    exact ⟨n + 1, Nat.add_le_add_right hn 1, by omega, .cons rfl hr⟩
  | write f q ih =>
    obtain ⟨n, hn, hp, hr⟩ := ih v (T.write (f T.head v))
    exact ⟨n + 1, Nat.add_le_add_right hn 1, by omega, .cons rfl hr⟩
  | load f q ih =>
    obtain ⟨n, hn, hp, hr⟩ := ih (f T.head v) T
    exact ⟨n, hn, hp, hr.of_step_eq hp rfl⟩
  | branch f q r ihq ihr =>
    cases he : f T.head v
    · obtain ⟨n, hn, hp, hr⟩ := ihr v T
      refine ⟨n, hn.trans (Nat.le_max_right _ _), hp, ?_⟩
      simpa only [TM1.stepAux, he, cond_false] using
        hr.of_step_eq hp (show TM0.step (TM1to0.tr M) ⟨(some (.branch f q r), v), T⟩ =
          TM0.step (TM1to0.tr M) ⟨(some r, v), T⟩ by
            simp [TM0.step, TM1to0.tr, TM1to0.trAux, he])
    · obtain ⟨n, hn, hp, hr⟩ := ihq v T
      refine ⟨n, hn.trans (Nat.le_max_left _ _), hp, ?_⟩
      simpa only [TM1.stepAux, he, cond_true] using
        hr.of_step_eq hp (show TM0.step (TM1to0.tr M) ⟨(some (.branch f q r), v), T⟩ =
          TM0.step (TM1to0.tr M) ⟨(some q, v), T⟩ by
            simp [TM0.step, TM1to0.tr, TM1to0.trAux, he])
  | goto f =>
    refine ⟨1, le_rfl, by decide, .one ?_⟩
    simp [TM0.step, TM1to0.tr, TM1to0.trAux, TM1to0.trCfg, TM1.stepAux,
      Tape.write_self]
  | halt =>
    refine ⟨1, le_rfl, by decide, .one ?_⟩
    simp [TM0.step, TM1to0.tr, TM1to0.trAux, TM1to0.trCfg, TM1.stepAux,
      Tape.write_self]

/-- A finite collection of accessible instruction blocks gives one uniform constant. -/
noncomputable def overhead (S : Finset Λ) : ℕ := ∑ l ∈ S, cost (M l)

theorem step {S : Finset Λ} {a b : TM1.Cfg Γ Λ σ}
    (ha : ∀ l ∈ a.l, l ∈ S) (h : TM1.step M a = some b) :
    Within (TM0.step (TM1to0.tr M)) (overhead M S)
      (TM1to0.trCfg M a) (TM1to0.trCfg M b) := by
  classical
  rcases a with ⟨l, v, T⟩
  cases l with
  | none => cases h
  | some l =>
    cases Option.some.inj h
    obtain ⟨n, hn, _, hr⟩ := block M (M l) v T
    exact ⟨n, hn.trans (Finset.single_le_sum (fun i _ ↦ Nat.zero_le (cost (M i)))
      (ha l rfl)), hr⟩

/-- A whole run expands by at most the same constant per macro transition. -/
theorem run {S : Finset Λ} (hs : TM1.Supports M S) {n : ℕ}
    {a b : TM1.Cfg Γ Λ σ} (ha : a.l ∈ Finset.insertNone S)
    (h : Run (TM1.step M) n a b) :
    Within (TM0.step (TM1to0.tr M)) (n * overhead M S)
      (TM1to0.trCfg M a) (TM1to0.trCfg M b) := by
  classical
  induction h with
  | zero => exact (Within.refl _).mono (by simp)
  | cons h _ ih =>
    have hb := TM1.step_supports M hs h ha
    have hfirst := step M (S := S) (fun l hl ↦ by
      exact Finset.some_mem_insertNone.mp (by simpa only [Option.mem_def.mp hl] using ha)) h
    exact (hfirst.trans (ih hb)).mono (by simp [Nat.add_mul, Nat.add_comm])

/-- Halting is preserved, in addition to preservation of the final tape. -/
theorem halted (v : σ) (T : Tape Γ) :
    TM0.step (TM1to0.tr M) (TM1to0.trCfg M ⟨none, v, T⟩) = none := rfl

end Lax554803Proofs.PostTime
