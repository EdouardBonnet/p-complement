import Lax888664Proofs.Time
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Set.Finite.Lattice
import Lax888664.MachineModels

set_option backward.isDefEq.respectTransparency false

/-! Restrict every stack to a finite alphabet, preserving each transition exactly.
Only symbols that can be pushed, or occur in input/output, are retained. -/

namespace Lax888664Proofs.FiniteAlphabet

open Turing Function Time

section

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

def pushed : TM2.Stmt Γ Λ σ → Set (Sigma Γ)
  | .push k f q => Set.range (fun v ↦ Sigma.mk k (f v)) ∪ pushed q
  | .peek _ _ q | .pop _ _ q | .load _ q => pushed q
  | .branch _ q r => pushed q ∪ pushed r
  | .goto _ | .halt => ∅

theorem pushed_finite [Finite σ] (q : TM2.Stmt Γ Λ σ) : (pushed q).Finite := by
  induction q with
  | push k f q ih => exact (Set.finite_range _).union ih
  | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ ih₁ ih₂ => exact ih₁.union ih₂
  | goto _ | halt => exact Set.finite_empty

variable (A : Set (Sigma Γ))

/-- The actual alphabet at stack `k`. It may be empty for an unused stack. -/
def Alphabet (k : K) := {a : Γ k // Sigma.mk k a ∈ A}

def decodeStacks (S : ∀ k, List (Alphabet A k)) : ∀ k, List (Γ k) :=
  fun k ↦ (S k).map Subtype.val

def decodeCfg (c : TM2.Cfg (Alphabet A) Λ σ) : TM2.Cfg Γ Λ σ :=
  ⟨c.l, c.var, decodeStacks A c.stk⟩

variable [DecidableEq K]

theorem decode_update (S : ∀ k, List (Alphabet A k)) (k : K) (l : List (Alphabet A k)) :
    decodeStacks A (update S k l) = update (decodeStacks A S) k (l.map Subtype.val) := by
  funext j
  by_cases h : j = k
  · subst j; simp [decodeStacks]
  · simp [decodeStacks, update_of_ne h]

/-- Translate a block using its proof that every pushed symbol is available. -/
def compile : (q : TM2.Stmt Γ Λ σ) → (pushed q ⊆ A) → TM2.Stmt (Alphabet A) Λ σ
  | .push k f q, h =>
    .push k (fun v ↦ ⟨f v, h (Or.inl ⟨v, rfl⟩)⟩)
      (compile q (fun _ hx ↦ h (Or.inr hx)))
  | .peek k f q, h => .peek k (fun v a ↦ f v (a.map Subtype.val)) (compile q h)
  | .pop k f q, h => .pop k (fun v a ↦ f v (a.map Subtype.val)) (compile q h)
  | .load f q, h => .load f (compile q h)
  | .branch f q r, h =>
    .branch f (compile q (fun _ hx ↦ h (Or.inl hx)))
      (compile r (fun _ hx ↦ h (Or.inr hx)))
  | .goto f, _ => .goto f
  | .halt, _ => .halt

theorem block (q : TM2.Stmt Γ Λ σ) (hq : pushed q ⊆ A) (v : σ)
    (S : ∀ k, List (Alphabet A k)) :
    decodeCfg A (TM2.stepAux (compile A q hq) v S) =
      TM2.stepAux q v (decodeStacks A S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [compile, TM2.stepAux]
    rw [ih, decode_update]
    rfl
  | peek k f q ih =>
    simpa only [compile, TM2.stepAux, decodeStacks, List.head?_map] using ih _ _ _
  | pop k f q ih =>
    simp only [compile, TM2.stepAux]
    rw [ih, decode_update]
    simp only [decodeStacks, List.head?_map]
    congr 2
    cases S k <;> rfl
  | load f q ih => exact ih _ _ _
  | branch f q r ihq ihr =>
    cases he : f v
    · simpa only [compile, TM2.stepAux, he, cond_false] using ihr _ _ _
    · simpa only [compile, TM2.stepAux, he, cond_true] using ihq _ _ _
  | goto f | halt => rfl

theorem step (M : Λ → TM2.Stmt Γ Λ σ) (hM : ∀ l, pushed (M l) ⊆ A)
    (c : TM2.Cfg (Alphabet A) Λ σ) :
    (TM2.step (fun l ↦ compile A (M l) (hM l)) c).map (decodeCfg A) =
      TM2.step M (decodeCfg A c) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => rfl
  | some l => exact congrArg some (block A (M l) (hM l) v S)

omit [DecidableEq K] in
theorem decodeCfg_injective : Injective (decodeCfg A (Λ := Λ) (σ := σ)) := by
  intro a b h
  cases a with | mk la va Sa =>
    cases b with | mk lb vb Sb =>
      have hl := congrArg TM2.Cfg.l h
      have hv := congrArg TM2.Cfg.var h
      have hs := congrArg TM2.Cfg.stk h
      simp only [decodeCfg, TM2.Cfg.mk.injEq] at hl hv hs ⊢
      refine ⟨hl, hv, funext fun k ↦ ?_⟩
      exact List.map_injective_iff.mpr Subtype.val_injective (congrFun hs k)

@[reducible] noncomputable def alphabetFintype (hA : A.Finite) (k : K) : Fintype (Alphabet A k) :=
  (Set.Finite.preimage (f := Sigma.mk k) (fun _ _ _ _ h ↦ by simpa using h) hA).fintype

/-- No symbols are lost at an input/output stack whose whole alphabet is retained. -/
def alphabetEquiv (k : K) (hk : ∀ a : Γ k, Sigma.mk k a ∈ A) : Alphabet A k ≃ Γ k where
  toFun := Subtype.val
  invFun a := ⟨a, hk a⟩
  left_inv _ := rfl
  right_inv _ := rfl

end

/-- The finite symbol set retains the entire input and output alphabets. -/
def symbols (tm : FinTM2) : Set (Sigma tm.Γ) :=
  (Set.range fun a : tm.Γ tm.k₀ ↦ Sigma.mk tm.k₀ a) ∪
    (Set.range fun a : tm.Γ tm.k₁ ↦ Sigma.mk tm.k₁ a) ∪ ⋃ l, pushed (tm.m l)

theorem symbols_finite (tm : FinTM2) [Finite (tm.Γ tm.k₁)] : (symbols tm).Finite := by
  letI := tm.Γk₀Fin
  letI := tm.ΛFin
  letI := tm.σFin
  exact ((Set.finite_range _).union (Set.finite_range _)).union
    (Set.finite_iUnion fun l ↦ pushed_finite (tm.m l))

theorem input_mem (tm : FinTM2) (a : tm.Γ tm.k₀) : Sigma.mk tm.k₀ a ∈ symbols tm :=
  Or.inl (Or.inl ⟨a, rfl⟩)

theorem output_mem (tm : FinTM2) (a : tm.Γ tm.k₁) : Sigma.mk tm.k₁ a ∈ symbols tm :=
  Or.inl (Or.inr ⟨a, rfl⟩)

theorem pushed_mem (tm : FinTM2) (l : tm.Λ) : pushed (tm.m l) ⊆ symbols tm :=
  fun _ h ↦ Or.inr (Set.mem_iUnion_of_mem l h)

noncomputable def restrict (tm : FinTM2) [Finite (tm.Γ tm.k₁)] : FinTM2 where
  K := tm.K
  kDecidableEq := tm.kDecidableEq
  kFin := tm.kFin
  k₀ := tm.k₀
  k₁ := tm.k₁
  Γ := Alphabet (symbols tm)
  Λ := tm.Λ
  main := tm.main
  ΛFin := tm.ΛFin
  σ := tm.σ
  initialState := tm.initialState
  σFin := tm.σFin
  Γk₀Fin := alphabetFintype (symbols tm) (symbols_finite tm) tm.k₀
  m l := compile (symbols tm) (tm.m l) (pushed_mem tm l)

theorem restrict_finite (tm : FinTM2) [Finite (tm.Γ tm.k₁)] (k : tm.K) :
    Finite ((restrict tm).Γ k) :=
  @Finite.of_fintype _ (alphabetFintype (symbols tm) (symbols_finite tm) k)

def inputEquiv (tm : FinTM2) : Alphabet (symbols tm) tm.k₀ ≃ tm.Γ tm.k₀ :=
  alphabetEquiv (symbols tm) tm.k₀ (input_mem tm)

def outputEquiv (tm : FinTM2) : Alphabet (symbols tm) tm.k₁ ≃ tm.Γ tm.k₁ :=
  alphabetEquiv (symbols tm) tm.k₁ (output_mem tm)

theorem init_decode (tm : FinTM2) [Finite (tm.Γ tm.k₁)] (w : List (tm.Γ tm.k₀)) :
    decodeCfg (symbols tm) (initList (restrict tm) (w.map (inputEquiv tm).symm)) =
      initList tm w := by
  change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst k
    simp [decodeStacks, initList, restrict, inputEquiv, alphabetEquiv]
    induction w with
    | nil => rfl
    | cons a w ih => exact congrArg (List.cons a) ih
  · simp [decodeStacks, initList, restrict, h]

theorem halt_decode (tm : FinTM2) [Finite (tm.Γ tm.k₁)] (w : List (tm.Γ tm.k₁)) :
    decodeCfg (symbols tm) (haltList (restrict tm) (w.map (outputEquiv tm).symm)) =
      haltList tm w := by
  change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst k
    simp [decodeStacks, haltList, restrict, outputEquiv, alphabetEquiv]
    induction w with
    | nil => rfl
    | cons a w ih => exact congrArg (List.cons a) ih
  · simp [decodeStacks, haltList, restrict, h]

/-- The finite-alphabet machine computes the same output in exactly the same number of steps. -/
theorem outputs (tm : FinTM2) [Finite (tm.Γ tm.k₁)]
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (n : ℕ)
    (h : Run tm.step n (initList tm input) (haltList tm output)) :
    Run (restrict tm).step n (initList (restrict tm) (input.map (inputEquiv tm).symm))
      (haltList (restrict tm) (output.map (outputEquiv tm).symm)) := by
  obtain ⟨c, hc, hr⟩ := h.lift (decodeCfg (symbols tm))
    (step (symbols tm) tm.m (pushed_mem tm)) (init_decode tm input)
  have he : c = haltList (restrict tm) (output.map (outputEquiv tm).symm) :=
    decodeCfg_injective (symbols tm) (hc.trans (halt_decode tm output).symm)
  exact he ▸ hr

/-- Normalize a polynomial-time computer without changing its time polynomial. -/
theorem computer {f : List Bool → Bool}
    (M : TM2ComputableInPolyTime id Computability.encodeBool f) :
    ∃ N : TM2ComputableInPolyTime id Computability.encodeBool f,
      N.time = M.time ∧ ∀ k, Finite (N.tm.Γ k) := by
  letI : Fintype (M.tm.Γ M.tm.k₁) := Fintype.ofEquiv Bool M.outputAlphabet.symm
  let N : TM2ComputableInPolyTime id Computability.encodeBool f :=
    { tm := restrict M.tm
      inputAlphabet := (inputEquiv M.tm).trans M.inputAlphabet
      outputAlphabet := (outputEquiv M.tm).trans M.outputAlphabet
      time := M.time
      outputsFun w :=
        { steps := (M.outputsFun w).steps
          steps_le_m := (M.outputsFun w).steps_le_m
          evals_in_steps := by
            have hr := outputs M.tm (w.map M.inputAlphabet.symm)
              [M.outputAlphabet.symm (f w)] (M.outputsFun w).steps
              (Run.of_iterate (M.outputsFun w).evals_in_steps)
            simpa only [List.map_map, List.map_cons, List.map_nil] using! hr.iterate } }
  exact ⟨N, rfl, restrict_finite M.tm⟩

/-- Requiring finite work alphabets does not change the language class. -/
theorem finiteStackP_eq_P :
    Lax888664.MachineModels.FiniteStackP = Lax888664.PolynomialTime.P := by
  ext L
  constructor
  · rintro ⟨f, M, hf, _⟩
    exact ⟨f, hf, ⟨M⟩⟩
  · rintro ⟨f, hf, ⟨M⟩⟩
    obtain ⟨N, _, hN⟩ := computer M
    exact ⟨f, N, hf, hN⟩

end Lax888664Proofs.FiniteAlphabet
