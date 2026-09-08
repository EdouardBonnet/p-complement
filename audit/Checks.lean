import Lax554803Proofs
import Mathlib.Data.Set.Finite.Lattice

set_option autoImplicit false

/-!
Independent semantic checks for the audit. This file is outside the submission
packages and does not add assumptions to the archived result.

Run from `proofs/`: `lake env lean ../audit/Checks.lean`.
-/

namespace Audit

open Lax554803.PolynomialTime Turing

/-- Unpack the definition all the way to a bounded sequence of transitions. -/
theorem operational_spec {L : Language} (h : L ∈ P) :
    ∃ (f : Word → Bool) (M : TM2ComputableInPolyTime id Computability.encodeBool f),
      (∀ w, f w = true ↔ w ∈ L) ∧
      ∀ w, ∃ t : ℕ, t ≤ M.time.eval w.length ∧
        (fun c : Option M.tm.Cfg ↦ c.bind M.tm.step)^[t]
          (some (initList M.tm (w.map M.inputAlphabet.symm))) =
          some (haltList M.tm [M.outputAlphabet.symm (f w)]) := by
  obtain ⟨f, hf, ⟨M⟩⟩ := h
  refine ⟨f, M, hf, fun w ↦ ?_⟩
  exact ⟨(M.outputsFun w).steps, (M.outputsFun w).steps_le_m,
    (M.outputsFun w).evals_in_steps⟩

/-- The required final configuration actually halts. -/
theorem required_output_is_terminal (M : FinTM2) (out : List (M.Γ M.k₁)) :
    M.step (haltList M out) = none := rfl

/-- Every rejecting answer corresponds exactly to nonmembership. -/
theorem negative_answers {L : Language} {f : Word → Bool}
    (hf : ∀ w, f w = true ↔ w ∈ L) (w : Word) :
    f w = false ↔ w ∉ L := by
  rw [← hf w]
  cases f w <;> decide

/-- The two answer encodings are distinct; a run cannot stand for both answers. -/
theorem answer_encodings_distinct {f : Word → Bool}
    (M : TM2ComputableInPolyTime id Computability.encodeBool f) :
    [M.outputAlphabet.symm true] ≠ [M.outputAlphabet.symm false] := by
  intro h
  have h' := M.outputAlphabet.symm.injective (List.cons.inj h).1
  cases h'

/-- Complementing twice gives the original membership statement, including the empty word. -/
theorem complement_iff (L : Language) : Lᶜ ∈ P ↔ L ∈ P := by
  constructor
  · intro h
    simpa only [compl_compl] using Lax554803Proofs.closed_under_complement Lᶜ h
  · exact Lax554803Proofs.closed_under_complement L

section FiniteAlphabet

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- All symbols that a statement can push, tagged with their stack index. -/
def pushedSymbols : TM2.Stmt Γ Λ σ → Set (Sigma Γ)
  | .push k f q => Set.range (fun v ↦ Sigma.mk k (f v)) ∪ pushedSymbols q
  | .peek _ _ q | .pop _ _ q | .load _ q => pushedSymbols q
  | .branch _ q₁ q₂ => pushedSymbols q₁ ∪ pushedSymbols q₂
  | .goto _ | .halt => ∅

theorem pushedSymbols_finite [Finite σ] (q : TM2.Stmt Γ Λ σ) :
    (pushedSymbols q).Finite := by
  induction q with
  | push k f q ih => exact (Set.finite_range _).union ih
  | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ ih₁ ih₂ => exact ih₁.union ih₂
  | goto _ | halt => exact Set.finite_empty

/-- Every symbol in every stack belongs to S. -/
def StoresOnly (S : Set (Sigma Γ)) (stk : ∀ k, List (Γ k)) : Prop :=
  ∀ k a, a ∈ stk k → Sigma.mk k a ∈ S

theorem stepAux_storesOnly [DecidableEq K] (q : TM2.Stmt Γ Λ σ)
    (S : Set (Sigma Γ)) (v : σ) (stk : ∀ k, List (Γ k))
    (hq : pushedSymbols q ⊆ S) (hs : StoresOnly S stk) :
    StoresOnly S (TM2.stepAux q v stk).stk := by
  induction q generalizing v stk with
  | push k f q ih =>
    apply ih _ _ (fun _ h ↦ hq (Or.inr h))
    intro j a ha
    by_cases h : j = k
    · subst j
      simp only [Function.update_self, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hq (Or.inl ⟨v, rfl⟩)
      · exact hs k a ha
    · rw [Function.update_of_ne h] at ha
      exact hs j a ha
  | peek k f q ih => exact ih _ _ hq hs
  | pop k f q ih =>
    apply ih _ _ hq
    intro j a ha
    by_cases h : j = k
    · subst j
      rw [Function.update_self] at ha
      exact hs k a (List.mem_of_mem_tail ha)
    · rw [Function.update_of_ne h] at ha
      exact hs j a ha
  | load f q ih => exact ih _ _ hq hs
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases h : f v
    · simpa only [TM2.stepAux, h, cond_false] using
        ih₂ v stk (fun _ h ↦ hq (Or.inr h)) hs
    · simpa only [TM2.stepAux, h, cond_true] using
        ih₁ v stk (fun _ h ↦ hq (Or.inl h)) hs
  | goto _ | halt => exact hs

end FiniteAlphabet

/-- A fixed set of symbols, independent of the input word and run length. -/
def machineSymbols (M : FinTM2) : Set (Sigma M.Γ) :=
  Set.range (fun a : M.Γ M.k₀ ↦ Sigma.mk M.k₀ a) ∪
    ⋃ l, pushedSymbols (M.m l)

theorem machineSymbols_finite (M : FinTM2) : (machineSymbols M).Finite := by
  letI := M.Γk₀Fin
  letI := M.ΛFin
  letI := M.σFin
  exact (Set.finite_range _).union (Set.finite_iUnion fun l ↦ pushedSymbols_finite (M.m l))

theorem init_storesOnly (M : FinTM2) (w : List (M.Γ M.k₀)) :
    StoresOnly (machineSymbols M) (initList M w).stk := by
  intro k a ha
  by_cases h : k = M.k₀
  · subst k
    exact Or.inl ⟨a, rfl⟩
  · simp [initList, h] at ha

theorem step_storesOnly (M : FinTM2) (c c' : M.Cfg)
    (hs : StoresOnly (machineSymbols M) c.stk) (h : M.step c = some c') :
    StoresOnly (machineSymbols M) c'.stk := by
  rcases c with ⟨l, v, stk⟩
  cases l with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
    have h' : TM2.stepAux (M.m l) v stk = c' := Option.some.inj h
    subst c'
    exact stepAux_storesOnly (M.m l) _ v stk
      (fun _ ha ↦ Or.inr (Set.mem_iUnion_of_mem l ha)) hs

/-- Despite possibly infinite ambient stack types, every reachable symbol lies
in one finite set depending only on the machine, uniformly over all inputs. -/
theorem reachable_alphabet_finite (M : FinTM2) :
    ∃ S : Set (Sigma M.Γ), S.Finite ∧
      ∀ (w : List (M.Γ M.k₀)) (c : M.Cfg),
        TM2.Reaches M.m (initList M w) c → StoresOnly S c.stk := by
  refine ⟨machineSymbols M, machineSymbols_finite M, ?_⟩
  intro w c h
  induction h with
  | refl => exact init_storesOnly M w
  | tail _ h ih => exact step_storesOnly M _ _ ih (Option.mem_def.mp h)

/-- A concrete nonconstant decision function, toggling once per input bit. -/
def parityFrom (b : Bool) : Word → Bool
  | [] => b
  | _ :: w => parityFrom (!b) w

/-- A finite one-stack machine that erases the input and writes its length parity. -/
def parityMachine : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool × Bool
  initialState := (false, false)
  m _ := .pop () (fun s a ↦ (if a.isSome then !s.1 else s.1, a.isSome))
    (.branch Prod.snd (.goto fun _ ↦ ())
      (.push () Prod.fst (.load (fun _ ↦ (false, false)) .halt)))

def parityCfg (b flag : Bool) (w : Word) : parityMachine.Cfg :=
  ⟨some (), (b, flag), fun _ ↦ w⟩

theorem parity_step_nil (b flag : Bool) :
    parityMachine.step (parityCfg b flag []) =
      some (haltList parityMachine [b]) := by
  simp [FinTM2.step, TM2.step, parityMachine, parityCfg, TM2.stepAux,
    Function.const_def, haltList]
  congr 2

theorem parity_step_cons (b flag a : Bool) (w : Word) :
    parityMachine.step (parityCfg b flag (a :: w)) =
      some (parityCfg (!b) true w) := by
  simp [FinTM2.step, TM2.step, parityMachine, parityCfg, TM2.stepAux,
    Function.const_def]
  congr 2

/-- The claimed time bound holds for every word, not just selected examples. -/
theorem parity_run (b flag : Bool) (w : Word) :
    (fun c : Option parityMachine.Cfg ↦ c.bind parityMachine.step)^[w.length + 1]
      (some (parityCfg b flag w)) =
      some (haltList parityMachine [parityFrom b w]) := by
  induction w generalizing b flag with
  | nil => simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      Option.bind_some, parityFrom] using parity_step_nil b flag
  | cons a w ih =>
    rw [List.length_cons, Nat.succ_add, Function.iterate_succ_apply]
    simp only [Option.bind_some, parity_step_cons, parityFrom]
    exact ih (!b) true

theorem parity_init (w : Word) :
    initList parityMachine w = parityCfg false false w := by
  simp [initList, parityMachine, parityCfg]

noncomputable def parityComputer :
    TM2ComputableInPolyTime id Computability.encodeBool (parityFrom false) where
  tm := parityMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun w :=
    { steps := w.length + 1
      evals_in_steps := by
        change (fun c : Option parityMachine.Cfg ↦ c.bind parityMachine.step)^[w.length + 1]
          (some (initList parityMachine (w.map id))) =
          some (haltList parityMachine [parityFrom false w])
        rw [List.map_id, parity_init]
        exact parity_run false false w
      steps_le_m := by simp }

/-- P contains a language with both a positive and a negative instance. -/
theorem nontrivial_language_in_P :
    ∃ L : Language, L ∈ P ∧ ([] : Word) ∉ L ∧ [false] ∈ L := by
  refine ⟨{w | parityFrom false w = true}, ?_, by decide, by decide⟩
  exact ⟨parityFrom false, fun _ ↦ Iff.rfl, ⟨parityComputer⟩⟩

#print axioms operational_spec
#print axioms required_output_is_terminal
#print axioms negative_answers
#print axioms answer_encodings_distinct
#print axioms complement_iff
#print axioms reachable_alphabet_finite
#print axioms nontrivial_language_in_P
#print axioms Lax554803.PolynomialTime.P
#print axioms Lax554803Proofs.negateOutput
#print axioms Lax554803Proofs.closed_under_complement

end Audit
