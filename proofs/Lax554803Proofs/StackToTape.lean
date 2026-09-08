import Lax554803Proofs.FiniteAlphabet
import Lax554803Proofs.TapeInput
import Lax554803Proofs.TapeOutput
import Mathlib.Tactic.GCongr

/-! Polynomial-time stack deciders compiled to ordinary elementary single-tape deciders. -/

namespace Lax554803Proofs.StackToTape

open Turing Time TM2to1 Lax554803.MachineModels

theorem supports_univ {K : Type} {Γ : K → Type} {Λ σ : Type}
    [Fintype Λ] [Inhabited Λ] (M : Λ → TM2.Stmt Γ Λ σ) :
    TM2.Supports M Finset.univ := by
  refine ⟨Finset.mem_univ _, fun l _ ↦ ?_⟩
  induction M l <;> simp_all [TM2.SupportsStmt]

theorem input_relation (tm : FinTM2) (w : List (tm.Γ tm.k₀)) :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    TrCfg (initList tm w)
      (TM1.init (trInit tm.k₀ w) : TM1.Cfg (Γ' tm.K tm.Γ) (Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ) := by
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  have he : initList tm w = TM2.init tm.k₀ w := by
    simp [initList, TM2.init]
    congr 1
    funext k
    by_cases hk : k = tm.k₀
    · subst k; simp [Function.update]
    · simp [Function.update, hk]
  rw [he]
  exact trCfg_init tm.k₀ w

theorem output_relation (tm : FinTM2) (b : tm.Γ tm.k₁)
    (c : TM1.Cfg (Γ' tm.K tm.Γ) (Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ)
    (h : TrCfg (haltList tm [b]) c) : c.l = none ∧ c.Tape.head.2 tm.k₁ = some b := by
  cases h with
  | mk T hT =>
    refine ⟨rfl, ?_⟩
    have he := stk_nth_val 0 (hT tm.k₁)
    simpa [haltList, ListBlank.nth_zero, Tape.mk'_head, addBottom] using he

/-- The finite-alphabet stack model is simulated by a conventional single tape. -/
theorem finiteStackP_subset_singleTapeP : FiniteStackP ⊆ SingleTapeP := by
  classical
  rintro L ⟨f, M, hf, hfinite⟩
  let tm := M.tm
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  letI : ∀ k, Fintype (tm.Γ k) := fun k ↦ @Fintype.ofFinite _ (hfinite k)
  let A := Γ' tm.K tm.Γ
  let Q := Λ' tm.K tm.Γ tm.Λ tm.σ
  let base : Q → TM1.Stmt A Q tm.σ := tr tm.m
  let Pgm := TapeInput.program tm.k₀ (TM2to1.Λ'.normal tm.main) base
  let S := trSupp tm.m Finset.univ
  have hS : TM1.Supports base S := tr_supports tm.m (supports_univ tm.m)
  have hm : TM2to1.Λ'.normal tm.main ∈ S := hS.1
  letI := TapeInput.startState Q
  let S' := TapeInput.labels S
  have hS' : TM1.Supports Pgm S' := TapeInput.program_supports tm.k₀ _ base hS hm
  let E := TM1to0.tr Pgm
  let ES := TM1to0.trStmts Pgm S'
  have hES : TM0.Supports E (ES : Set (TM1to0.Λ' Pgm)) := TM1to0.tr_supports Pgm hS'
  let C := StackTime.overhead tm
  let D := PostTime.overhead Pgm S'
  let p := M.time
  let bound : Polynomial ℕ :=
    (Polynomial.X + 1 + p * (1 + Polynomial.C C *
      (2 * (Polynomial.X + p * Polynomial.C C) + 2))) * Polynomial.C D
  let input : Bool ↪ A :=
    { toFun := fun b ↦ TapeInput.letter tm.k₀ (M.inputAlphabet.symm b)
      inj' := by
        intro a b h
        have he := congrArg (fun z : A ↦ z.2 tm.k₀) h
        simp only [TapeInput.letter, Function.update_self] at he
        exact M.inputAlphabet.symm.injective (Option.some.inj he) }
  have hi : ∀ b, input b ≠ default := by
    intro b he
    have h := congrArg (fun z : A ↦ z.2 tm.k₀) he
    have hs : (input b).2 tm.k₀ = some (M.inputAlphabet.symm b) := by
      simp [input, TapeInput.letter]
    have hn : (default : A).2 tm.k₀ = none := rfl
    have bad : some (M.inputAlphabet.symm b) = none := hs.symm.trans (h.trans hn)
    contradiction
  let read : TM1to0.Λ' Pgm → A → Bool :=
    fun _ a ↦ ((a.2 tm.k₁).map M.outputAlphabet).getD false
  apply TapeOutput.of_supported E read ES hES input hi bound L
  intro w
  let u := w.map M.inputAlphabet.symm
  have hu : u.length = w.length := List.length_map _
  have hsrc : Run tm.step (M.outputsFun w).steps
      (initList tm u) (haltList tm [M.outputAlphabet.symm (f w)]) :=
    Run.of_iterate (M.outputsFun w).evals_in_steps
  obtain ⟨c, hc, ⟨t, ht, hrun⟩⟩ := StackTime.run tm.m (StackTime.work_le_overhead tm)
    (StackTime.init_bound tm u) hsrc (input_relation tm u)
  have hout := output_relation tm _ c hc
  have hmirror := TapeInput.run base Pgm Sum.inr (fun _ ↦ rfl) hrun
  have hprep := TapeInput.prepare tm.k₀ (TM2to1.Λ'.normal tm.main) base tm.initialState u
  have hmrun : Within (TM1.step Pgm)
      (w.length + 1 + p.eval w.length * (1 + C * (2 * (w.length + p.eval w.length * C) + 2)))
      (TM1.init (w.map input)) (TapeInput.cfg Sum.inr c) := by
    obtain ⟨r, hr, hprepare⟩ := hprep
    have hall := hprepare.trans hmirror
    refine ⟨r + t, ?_, ?_⟩
    · have hn := (M.outputsFun w).steps_le_m
      rw [hu] at hr ht
      apply Nat.add_le_add hr
      apply ht.trans
      gcongr <;> exact hn
    · simpa only [u, input, List.map_map] using hall
  obtain ⟨r, hr, hmacro⟩ := hmrun
  have hstart : (TM1.init (w.map input) : TM1.Cfg A (Sum Bool Q) tm.σ).l ∈
      Finset.insertNone S' := Finset.some_mem_insertNone.mpr hS'.1
  have helem := PostTime.run Pgm hS' hstart hmacro
  refine ⟨TM1to0.trCfg Pgm (TapeInput.cfg Sum.inr c), ?_, ?_, ?_⟩
  · apply helem.mono
    change r * D ≤ bound.eval w.length
    simpa [bound] using Nat.mul_le_mul_right D hr
  · rcases c with ⟨l, v, T⟩
    have hl : l = none := hout.1
    obtain rfl := hl
    rfl
  · change (((c.Tape.head.2 tm.k₁).map M.outputAlphabet).getD false = true) ↔ w ∈ L
    simpa only [hout.2, Option.map_some, Equiv.apply_symm_apply, Option.getD_some] using hf w

/-- The original definition of P implies elementary single-tape polynomial time. -/
theorem P_subset_singleTapeP : Lax554803.PolynomialTime.P ⊆ SingleTapeP := by
  rw [← FiniteAlphabet.finiteStackP_eq_P]
  exact finiteStackP_subset_singleTapeP

end Lax554803Proofs.StackToTape
