import Lax554803Proofs.StackTime
import Lax554803Proofs.PostTime

/-! Ordinary input preparation for the stack-to-tape simulator.
Reflecting the simulated tape lets a single scan prepare input in its original order. -/

namespace Lax554803Proofs.TapeInput

open Turing Time Function

section Mirror

variable {Γ Λ Λ' σ : Type} [Inhabited Γ]

def mirror (T : Tape Γ) : Tape Γ := ⟨T.head, T.right, T.left⟩

def opposite : Dir → Dir | .left => .right | .right => .left

@[simp] theorem mirror_mirror (T : Tape Γ) : mirror (mirror T) = T := rfl

@[simp] theorem mirror_move (d : Dir) (T : Tape Γ) :
    mirror (T.move d) = (mirror T).move (opposite d) := by cases d <;> rfl

@[simp] theorem mirror_write (a : Γ) (T : Tape Γ) :
    mirror (T.write a) = (mirror T).write a := rfl

def stmt (f : Λ → Λ') : TM1.Stmt Γ Λ σ → TM1.Stmt Γ Λ' σ
  | .move d q => .move (opposite d) (stmt f q)
  | .write a q => .write a (stmt f q)
  | .load a q => .load a (stmt f q)
  | .branch p q r => .branch p (stmt f q) (stmt f r)
  | .goto l => .goto fun a v ↦ f (l a v)
  | .halt => .halt

def cfg (f : Λ → Λ') (c : TM1.Cfg Γ Λ σ) : TM1.Cfg Γ Λ' σ :=
  ⟨c.l.map f, c.var, mirror c.Tape⟩

theorem block (f : Λ → Λ') (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    TM1.stepAux (stmt f q) v (mirror T) = cfg f (TM1.stepAux q v T) := by
  induction q generalizing v T with
  | move d q ih => simpa only [stmt, TM1.stepAux, mirror_move] using ih v (T.move d)
  | write a q ih => simpa only [stmt, TM1.stepAux, mirror_write, mirror] using ih v (T.write (a T.head v))
  | load a q ih => exact ih _ _
  | branch p q r ihq ihr =>
    cases he : p T.head v
    · simpa only [stmt, TM1.stepAux, mirror, he, cond_false] using ihr v T
    · simpa only [stmt, TM1.stepAux, mirror, he, cond_true] using ihq v T
  | goto l | halt => rfl

theorem run (M : Λ → TM1.Stmt Γ Λ σ) (N : Λ' → TM1.Stmt Γ Λ' σ)
    (f : Λ → Λ') (hN : ∀ l, N (f l) = stmt f (M l))
    {n : ℕ} {a b : TM1.Cfg Γ Λ σ} (h : Run (TM1.step M) n a b) :
    Run (TM1.step N) n (cfg f a) (cfg f b) := by
  apply h.map (cfg f)
  intro c d hd
  rcases c with ⟨l, v, T⟩
  cases l with
  | none => cases hd
  | some l =>
    cases Option.some.inj hd
    change some (TM1.stepAux (N (f l)) v (mirror T)) = _
    rw [hN, block]

omit [Inhabited Γ] in
theorem supports {S : Finset Λ} {S' : Finset Λ'} (f : Λ → Λ')
    (hf : ∀ l ∈ S, f l ∈ S') (q : TM1.Stmt Γ Λ σ) (h : TM1.SupportsStmt S q) :
    TM1.SupportsStmt S' (stmt f q) := by
  induction q with
  | move _ _ ih | write _ _ ih | load _ _ ih => exact ih h
  | branch _ _ _ ihq ihr => exact ⟨ihq h.1, ihr h.2⟩
  | goto l => exact fun a v ↦ hf _ (h a v)
  | halt => trivial

end Mirror

section Prepare

open TM2to1

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
variable (k : K) (main : Λ) (M : Λ → TM1.Stmt (Γ' K Γ) Λ σ)

omit [DecidableEq K] in
@[simp] theorem default_track : (default : Γ' K Γ).2 k = none := rfl

@[simp] theorem blank_singleton {α : Type} [Inhabited α] :
    ListBlank.mk [default] = ListBlank.mk ([] : List α) :=
  ListBlank.cons_head_tail (ListBlank.mk [])

def letter (a : Γ k) : Γ' K Γ := (false, update (fun _ ↦ none) k (some a))

def mark (a : Γ' K Γ) : Γ' K Γ := (true, a.2)

def program : Sum Bool Λ → TM1.Stmt (Γ' K Γ) (Sum Bool Λ) σ
  | .inl false =>
    .branch (fun a _ ↦ (a.2 k).isNone)
      (.write (fun a _ ↦ mark a) (.goto fun _ _ ↦ .inr main))
      (.move .right (.goto fun _ _ ↦ .inl true))
  | .inl true =>
    .branch (fun a _ ↦ (a.2 k).isNone)
      (.move .left (.write (fun a _ ↦ mark a) (.goto fun _ _ ↦ .inr main)))
      (.move .right (.goto fun _ _ ↦ .inl true))
  | .inr l => stmt Sum.inr (M l)

/-- The scan visits each input square once. -/
theorem scan (v : σ) (L R : List (Γ k)) :
    Run (TM1.step (program k main M)) R.length
      ⟨some (.inl true), v, Tape.mk₂ (L.map (letter k)) (R.map (letter k))⟩
      ⟨some (.inl true), v, Tape.mk₂ ((R.reverse ++ L).map (letter k)) []⟩ := by
  induction R generalizing L with
  | nil => exact .zero _
  | cons a R ih =>
    have hs : TM1.step (program k main M)
        ⟨some (.inl true), v, Tape.mk₂ (L.map (letter k)) ((a :: R).map (letter k))⟩ =
        some ⟨some (.inl true), v, Tape.mk₂ ((a :: L).map (letter k)) (R.map (letter k))⟩ := by
      simp [TM1.step, program, TM1.stepAux, Tape.mk₂, Tape.mk',
        ListBlank.head_mk, ListBlank.tail_mk, letter, Tape.move, ListBlank.cons_mk]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
      Run.cons hs (ih (a :: L))

theorem finish (v : σ) (w : List (Γ k)) (hw : w ≠ []) :
    TM1.step (program k main M)
      ⟨some (.inl true), v, Tape.mk₂ (w.reverse.map (letter k)) []⟩ =
      some ⟨some (.inr main), v, mirror (Tape.mk₁ (trInit k w))⟩ := by
  have hn : w.reverse ≠ [] := by simpa using hw
  cases he : w.reverse with
  | nil => contradiction
  | cons a L =>
    simp [TM1.step, program, TM1.stepAux, Tape.mk₂, Tape.mk', Tape.mk₁, Tape.move,
      Tape.write, trInit, he, letter, mark, mirror, ListBlank.head_mk,
      ListBlank.tail_mk, ListBlank.cons_mk]
    rfl

/-- Preparing ordinary input takes at most its length plus one macro transition. -/
theorem prepare (v : σ) (w : List (Γ k)) :
    Within (TM1.step (program k main M)) (w.length + 1)
      ⟨some (.inl false), v, Tape.mk₁ (w.map (letter k))⟩
      ⟨some (.inr main), v, mirror (Tape.mk₁ (trInit k w))⟩ := by
  cases w with
  | nil =>
    apply Within.one
    simp [TM1.step, program, TM1.stepAux, Tape.mk₁, Tape.mk₂, Tape.mk', Tape.write,
      trInit, mark, mirror, ListBlank.head_mk, ListBlank.tail_mk]
  | cons a w =>
    have hs : TM1.step (program k main M)
        ⟨some (.inl false), v, Tape.mk₁ ((a :: w).map (letter k))⟩ =
        some ⟨some (.inl true), v, Tape.mk₂ ([a].map (letter k)) (w.map (letter k))⟩ := by
      simp [TM1.step, program, TM1.stepAux, Tape.mk₁, Tape.mk₂, Tape.mk', Tape.move,
        letter, ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]
    have ht := scan k main M v [a] w
    have hf := finish k main M v (a :: w) (by simp)
    rw [List.reverse_cons] at hf
    exact ⟨w.length + 2, by simp, (Run.cons hs ht).trans (.one hf)⟩

noncomputable def labels (S : Finset Λ) : Finset (Sum Bool Λ) := by
  classical
  exact {.inl false, .inl true} ∪ S.image Sum.inr

@[reducible] def startState (Λ : Type) : Inhabited (Sum Bool Λ) := ⟨Sum.inl false⟩

attribute [local instance] startState

omit [DecidableEq K] in
theorem program_supports [Inhabited Λ] {S : Finset Λ} (hS : TM1.Supports M S)
    (hm : main ∈ S) : TM1.Supports (program k main M) (labels S) := by
  classical
  refine ⟨by simp [labels, default], ?_⟩
  intro l hl
  cases l with
  | inl b => cases b <;> simp [program, TM1.SupportsStmt, labels, hm]
  | inr l =>
    have hl' : l ∈ S := by simpa [labels] using hl
    exact supports Sum.inr (fun i hi ↦ by simp [labels, hi]) (M l) (hS.2 l hl')

end Prepare

end Lax554803Proofs.TapeInput
