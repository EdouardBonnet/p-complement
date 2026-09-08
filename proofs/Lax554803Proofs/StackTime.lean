/-
The scan proofs adapt mathlib's untimed TM2to1 simulation:
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The adaptations add explicit transition counts and whole-run bounds.
-/
import Lax554803Proofs.Time
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! Quantitative correctness of mathlib's stack-to-single-tape simulator. -/

namespace Lax554803Proofs.StackTime

open Turing Time Function TM2to1

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- Maximum number of stack operations executed by a block. -/
def work : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q | .peek _ _ q | .pop _ _ q => work q + 1
  | .load _ q => work q
  | .branch _ q r => max (work q) (work r)
  | .goto _ | .halt => 0

theorem work_run {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    work (stRun o q) = work q + 1 := by cases o <;> rfl

theorem stWrite_length {k : K} (o : StAct K Γ σ k) (v : σ) (S : List (Γ k)) :
    (stWrite v S o).length ≤ S.length + 1 := by
  cases o <;> simp [stWrite]
  omega

variable [DecidableEq K]

theorem action_bound {k : K} (o : StAct K Γ σ k) (v : σ)
    (S : ∀ k, List (Γ k)) {s : ℕ} (hs : ∀ j, (S j).length ≤ s) :
    ∀ j, (update S k (stWrite v (S k) o) j).length ≤ s + 1 := by
  intro j
  by_cases h : j = k
  · subst j
    rw [update_self]
    exact (stWrite_length o v _).trans (Nat.add_le_add_right (hs k) 1)
  · rw [update_of_ne h]
    exact (hs j).trans (by omega)

theorem block_bound (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k))
    {s : ℕ} (hs : ∀ k, (S k).length ≤ s) :
    ∀ k, ((TM2.stepAux q v S).stk k).length ≤ s + work q := by
  induction q using stmtStRec generalizing v S s with
  | run k o q ih =>
    rw [step_run, work_run]
    intro j
    exact (ih _ _ (action_bound o v S hs) j).trans (by omega)
  | load f q ih => exact ih _ _ hs
  | branch f q r ihq ihr =>
    cases he : f v
    · simp only [TM2.stepAux, he, cond_false]
      exact fun k ↦ (ihr _ _ hs k).trans (Nat.add_le_add_left (Nat.le_max_right _ _) s)
    · simp only [TM2.stepAux, he, cond_true]
      exact fun k ↦ (ihq _ _ hs k).trans (Nat.add_le_add_left (Nat.le_max_left _ _) s)
  | goto _ | halt => simpa only [TM2.stepAux, work, Nat.add_zero] using hs

variable (M : Λ → TM2.Stmt Γ Λ σ)

/-- Scanning to the top of a stack takes exactly its length in TM1 transitions. -/
theorem go_run {k : K} (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    {S : List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse)
    (n : ℕ) (hn : n ≤ S.length) :
    Run (TM1.step (tr M)) n ⟨some (.go k o q), v, Tape.mk' ∅ (addBottom L)⟩
      ⟨some (.go k o q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => exact .zero _
  | succ n ih =>
    apply (ih (by omega)).trans (Run.one ?_)
    rw [iterate_succ_apply']
    simp only [TM1.step, TM1.stepAux, tr, Tape.mk'_nth_nat, Tape.move_right_n_head,
      addBottom_nth_snd]
    rw [stk_nth_val _ hL, List.getElem?_eq_getElem]
    · rfl
    · rw [List.length_reverse]; omega

/-- Returning to the bottom marker takes exactly the distance from it. -/
theorem ret_run (q : TM2.Stmt Γ Λ σ) (v : σ)
    (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    Run (TM1.step (tr M)) n
      ⟨some (.ret q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      ⟨some (.ret q), v, Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => exact .zero _
  | succ n ih =>
    refine .cons ?_ ih
    simp only [TM1.step]
    rw [Option.some_inj, tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat,
      addBottom_nth_succ_fst, TM1.stepAux, iterate_succ', Function.comp_apply,
      Tape.move_right_left]
    rfl

/-- A whole block costs at most `work q` scans, each of length at most `2*B+2`.
The hypothesis reserves space for all pushes in the block. -/
theorem block (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k))
    (L : ListBlank (∀ k, Option (Γ k)))
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse)
    (s B : ℕ) (hs : ∀ k, (S k).length ≤ s) (hB : s + work q ≤ B) :
    ∃ b, TrCfg (TM2.stepAux q v S) b ∧
      Within (TM1.step (tr M)) (work q * (2 * B + 2))
        (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L))) b := by
  induction q using stmtStRec generalizing v S L s with
  | run k o q ih =>
    rw [work_run] at hB ⊢
    simp only [trNormal_run, step_run, TM1.stepAux]
    let S' := update S k (stWrite v (S k) o)
    let v' := stVar v (S k) o
    obtain ⟨L', hL', hact⟩ := tr_respects_aux₂
      (q := TM1.Stmt.goto fun _ _ ↦ .ret q) hL o
    have hg := go_run M o q v (hL k) (S k).length le_rfl
    have ha : TM1.step (tr M)
        ⟨some (.go k o q), v,
          (Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩ =
        some ⟨some (.ret q), v',
          (Tape.move Dir.right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
      simp only [TM1.step]
      rw [tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat,
        addBottom_nth_snd, stk_nth_val _ (hL k),
        List.getElem?_eq_none (le_of_eq List.length_reverse)]
      exact congrArg some hact
    have hr := ret_run M q v' L' (S' k).length
    have hb : TM1.step (tr M) ⟨some (.ret q), v', Tape.mk' ∅ (addBottom L')⟩ =
        some (TM1.stepAux (trNormal q) v' (Tape.mk' ∅ (addBottom L'))) := by
      simp [TM1.step, tr, TM1.stepAux, Tape.mk'_head, addBottom_head_fst]
    obtain ⟨b, hrel, htail⟩ := ih v' S' L' hL' (s + 1)
      (action_bound o v S hs) (by omega)
    refine ⟨b, hrel, ?_⟩
    have hprefix := ((hg.trans (.one ha)).trans hr).trans (.one hb)
    have hbound : (S k).length + 1 + (S' k).length + 1 ≤ 2 * B + 2 := by
      have h0 := hs k
      have h1 := action_bound o v S hs k
      change (S' k).length ≤ s + 1 at h1
      omega
    have hp : Within (TM1.step (tr M)) (2 * B + 2) _ _ :=
      ⟨_, hbound, hprefix⟩
    exact (hp.trans htail).mono (by simp [Nat.add_mul, Nat.add_comm])
  | load f q ih => exact ih _ _ _ hL s hs hB
  | branch f q r ihq ihr =>
    cases he : f v
    · simp only [TM2.stepAux, trNormal, TM1.stepAux, he, cond_false]
      obtain ⟨b, hb, ht⟩ := ihr v S L hL s hs (by simp only [work] at hB; omega)
      exact ⟨b, hb, ht.mono (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))⟩
    · simp only [TM2.stepAux, trNormal, TM1.stepAux, he, cond_true]
      obtain ⟨b, hb, ht⟩ := ihq v S L hL s hs (by simp only [work] at hB; omega)
      exact ⟨b, hb, ht.mono (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))⟩
  | goto f => exact ⟨_, ⟨L, hL⟩, (Within.refl _).mono (by simp [work])⟩
  | halt => exact ⟨_, ⟨L, hL⟩, (Within.refl _).mono (by simp [work])⟩

/-- A source step costs one dispatch plus the scans for its stack operations. -/
theorem step {C s B : ℕ} (hC : ∀ l, work (M l) ≤ C) (hB : s + C ≤ B)
    {a b : TM2.Cfg Γ Λ σ} {a' : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ}
    (hs : ∀ k, (a.stk k).length ≤ s) (h : TM2.step M a = some b)
    (ha : TrCfg a a') :
    ∃ b', TrCfg b b' ∧ Within (TM1.step (tr M)) (1 + C * (2 * B + 2)) a' b' := by
  cases ha with
  | @mk l v S L hL =>
    cases l with
    | none => cases h
    | some l =>
      cases Option.some.inj h
      obtain ⟨b', hb', hr⟩ := block M (M l) v S L hL s B hs (by have := hC l; omega)
      refine ⟨b', hb', ?_⟩
      have hf : Within (TM1.step (tr M)) 1
          ⟨some (.normal l), v, Tape.mk' ∅ (addBottom L)⟩
          (TM1.stepAux (trNormal (M l)) v (Tape.mk' ∅ (addBottom L))) := .one rfl
      exact (hf.trans hr).mono (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hC l)) 1)

theorem step_bound {C s : ℕ} (hC : ∀ l, work (M l) ≤ C)
    {a b : TM2.Cfg Γ Λ σ} (hs : ∀ k, (a.stk k).length ≤ s)
    (h : TM2.step M a = some b) : ∀ k, (b.stk k).length ≤ s + C := by
  rcases a with ⟨l, v, S⟩
  cases l with
  | none => cases h
  | some l =>
    cases Option.some.inj h
    exact fun k ↦ (block_bound (M l) v S hs k).trans (Nat.add_le_add_left (hC l) s)

/-- An `n`-step stack run is simulated in `O(n * (s+n))` single-tape macro steps.
Here `s` bounds the initial stack lengths and `C` depends only on the fixed program. -/
theorem run {C : ℕ} (hC : ∀ l, work (M l) ≤ C) {n s : ℕ}
    {a b : TM2.Cfg Γ Λ σ} {a' : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ}
    (hs : ∀ k, (a.stk k).length ≤ s) (h : Run (TM2.step M) n a b)
    (ha : TrCfg a a') :
    ∃ b', TrCfg b b' ∧
      Within (TM1.step (tr M)) (n * (1 + C * (2 * (s + n * C) + 2))) a' b' := by
  induction h generalizing s a' with
  | zero => exact ⟨a', ha, (Within.refl _).mono (by simp)⟩
  | @cons n a d b h ht ih =>
    have hd := step_bound M hC hs h
    obtain ⟨d', hd', hfirst⟩ := step M hC (B := s + (n + 1) * C)
      (by simp only [Nat.add_mul, Nat.one_mul]; omega) hs h ha
    obtain ⟨b', hb', hrest⟩ := ih hd hd'
    refine ⟨b', hb', (hfirst.trans hrest).mono ?_⟩
    simp only [Nat.add_mul, Nat.one_mul]
    nlinarith

/-- A uniform instruction bound for a bundled finite-control machine. -/
noncomputable def overhead (tm : FinTM2) : ℕ :=
  letI := tm.ΛFin
  ∑ l, work (tm.m l)

theorem work_le_overhead (tm : FinTM2) (l : tm.Λ) : work (tm.m l) ≤ overhead tm := by
  classical
  letI := tm.ΛFin
  exact Finset.single_le_sum (fun i _ ↦ Nat.zero_le (work (tm.m i))) (Finset.mem_univ l)

theorem init_bound (tm : FinTM2) (w : List (tm.Γ tm.k₀)) :
    ∀ k, ((initList tm w).stk k).length ≤ w.length := by
  intro k
  by_cases h : k = tm.k₀
  · subst k; simp [initList]
  · simp [initList, h]

end Lax554803Proofs.StackTime
