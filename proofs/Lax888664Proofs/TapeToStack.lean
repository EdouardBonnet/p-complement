import Lax888664Proofs.Time
import Lax888664.MachineModels
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-! Simulate an elementary single tape by its left and right stacks.
Input conversion and final erasure are included in the time bound. -/

namespace Lax888664Proofs.TapeToStack

open Turing Time Lax888664.MachineModels

inductive Slot | io | left | right deriving DecidableEq, Fintype
inductive Label | readInput | reverseInput | start | simulate | clearLeft | clearRight
  deriving DecidableEq, Fintype

structure Store (Q Γ : Type) where
  q : Q
  head : Γ
  bit : Bool
  present : Bool
  deriving Fintype

@[reducible] def alphabet (M : SingleTape) : Slot → Type
  | .io => Bool
  | .left | .right => M.Γ

def initial (M : SingleTape) : Store M.Q M.Γ := ⟨default, default, false, false⟩

def next (M : SingleTape) (v : Store M.Q M.Γ) : M.Q × TM0.Stmt M.Γ :=
  (M.transition v.q v.head).getD (v.q, .write v.head)

def program (M : SingleTape) : Label → TM2.Stmt (alphabet M) Label (Store M.Q M.Γ)
  | .readInput =>
    .pop .io (fun v a ↦ {v with head := M.input (a.getD false), present := a.isSome})
      (.branch Store.present
        (.push .left Store.head (.goto fun _ ↦ .readInput))
        (.goto fun _ ↦ .reverseInput))
  | .reverseInput =>
    .pop .left (fun v a ↦ {v with head := a.getD default, present := a.isSome})
      (.branch Store.present
        (.push .right Store.head (.goto fun _ ↦ .reverseInput))
        (.goto fun _ ↦ .start))
  | .start =>
    .pop .right (fun _ a ↦ ⟨default, a.getD default, false, false⟩)
      (.goto fun _ ↦ .simulate)
  | .simulate =>
    .branch (fun v ↦ (M.transition v.q v.head).isNone)
      (.load (fun v ↦ ⟨default, default, M.accept v.q, false⟩)
        (.goto fun _ ↦ .clearLeft))
      (.branch (fun v ↦ match (next M v).2 with | .move .left => true | _ => false)
        (.push .right Store.head
          (.load (fun v ↦ ⟨(next M v).1, v.head, false, false⟩)
            (.pop .left (fun v a ↦ {v with head := a.getD default})
              (.goto fun _ ↦ .simulate))))
        (.branch (fun v ↦ match (next M v).2 with | .move .right => true | _ => false)
          (.push .left Store.head
            (.load (fun v ↦ ⟨(next M v).1, v.head, false, false⟩)
              (.pop .right (fun v a ↦ {v with head := a.getD default})
                (.goto fun _ ↦ .simulate))))
          (.load (fun v ↦ ⟨(next M v).1,
              (match (next M v).2 with | .write a => a | _ => v.head), false, false⟩)
            (.goto fun _ ↦ .simulate))))
  | .clearLeft =>
    .pop .left (fun v a ↦ {v with present := a.isSome})
      (.branch Store.present (.goto fun _ ↦ .clearLeft) (.goto fun _ ↦ .clearRight))
  | .clearRight =>
    .pop .right (fun v a ↦ {v with present := a.isSome})
      (.branch Store.present (.goto fun _ ↦ .clearRight)
        (.push .io Store.bit (.load (fun _ ↦ initial M) .halt)))

def machine (M : SingleTape) : FinTM2 where
  K := Slot
  k₀ := .io
  k₁ := .io
  Γ := alphabet M
  Λ := Label
  main := .readInput
  σ := Store M.Q M.Γ
  initialState := initial M
  m := program M

def tapes (M : SingleTape) (I : List Bool) (L R : List M.Γ) : ∀ k, List (alphabet M k)
  | .io => I
  | .left => L
  | .right => R

def cfg (M : SingleTape) (l : Label) (v : Store M.Q M.Γ)
    (I : List Bool) (L R : List M.Γ) : (machine M).Cfg :=
  ⟨some l, v, tapes M I L R⟩

def simCfg (M : SingleTape) (q : M.Q) (a : M.Γ) (L R : List M.Γ) : (machine M).Cfg :=
  cfg M .simulate ⟨q, a, false, false⟩ [] L R

def tapeCfg (M : SingleTape) (q : M.Q) (a : M.Γ) (L R : List M.Γ) : TM0.Cfg M.Γ M.Q :=
  ⟨q, ⟨a, ListBlank.mk L, ListBlank.mk R⟩⟩

theorem tapes_io (M : SingleTape) (I I' : List Bool) (L R : List M.Γ) :
    Function.update (tapes M I L R) .io I' = tapes M I' L R := by
  funext k; cases k <;> rfl

theorem tapes_left (M : SingleTape) (I : List Bool) (L L' R : List M.Γ) :
    Function.update (tapes M I L R) .left L' = tapes M I L' R := by
  funext k; cases k <;> rfl

theorem tapes_right (M : SingleTape) (I : List Bool) (L R R' : List M.Γ) :
    Function.update (tapes M I L R) .right R' = tapes M I L R' := by
  funext k; cases k <;> rfl

theorem move_left (M : SingleTape) (q q' : M.Q) (a : M.Γ) (L R : List M.Γ)
    (h : M.transition q a = some (q', .move .left)) :
    (machine M).step (simCfg M q a L R) =
      some (simCfg M q' (L.head?.getD default) L.tail (a :: R)) := by
  simp [FinTM2.step, machine, program, simCfg, cfg, TM2.step, TM2.stepAux, next, h,
    tapes]
  congr 2
  funext k; cases k <;> rfl

theorem move_right (M : SingleTape) (q q' : M.Q) (a : M.Γ) (L R : List M.Γ)
    (h : M.transition q a = some (q', .move .right)) :
    (machine M).step (simCfg M q a L R) =
      some (simCfg M q' (R.head?.getD default) (a :: L) R.tail) := by
  simp [FinTM2.step, machine, program, simCfg, cfg, TM2.step, TM2.stepAux, next, h,
    tapes]
  congr 2
  funext k; cases k <;> rfl

theorem write (M : SingleTape) (q q' : M.Q) (a b : M.Γ) (L R : List M.Γ)
    (h : M.transition q a = some (q', .write b)) :
    (machine M).step (simCfg M q a L R) = some (simCfg M q' b L R) := by
  simp [FinTM2.step, machine, program, simCfg, cfg, TM2.step, TM2.stepAux, next, h]

/-- One elementary tape transition is exactly one stack transition. -/
theorem step (M : SingleTape) (q : M.Q) (a : M.Γ) (L R : List M.Γ)
    (c : TM0.Cfg M.Γ M.Q) (h : TM0.step M.transition (tapeCfg M q a L R) = some c) :
    ∃ (q' : M.Q) (a' : M.Γ) (L' R' : List M.Γ),
      c = tapeCfg M q' a' L' R' ∧ L'.length + R'.length ≤ L.length + R.length + 1 ∧
      (machine M).step (simCfg M q a L R) = some (simCfg M q' a' L' R') := by
  cases he : M.transition q a with
  | none => simp [TM0.step, tapeCfg, he] at h
  | some p =>
    rcases p with ⟨q', act⟩
    simp only [TM0.step, tapeCfg, he, Option.map_some] at h
    cases Option.some.inj h
    cases act with
    | move d =>
      cases d with
      | left =>
        refine ⟨q', L.head?.getD default, L.tail, a :: R, ?_, ?_, move_left M q q' a L R he⟩
        · cases L <;> rfl
        · simp; omega
      | right =>
        refine ⟨q', R.head?.getD default, a :: L, R.tail, ?_, ?_, move_right M q q' a L R he⟩
        · cases R <;> rfl
        · simp; omega
    | write b =>
      refine ⟨q', b, L, R, ?_, by omega, write M q q' a b L R he⟩
      rfl

/-- The two explicit tape halves grow by at most one symbol per source transition. -/
theorem run (M : SingleTape) {n : ℕ} {c d : TM0.Cfg M.Γ M.Q}
    (h : Run (TM0.step M.transition) n c d)
    (q : M.Q) (a : M.Γ) (L R : List M.Γ) (hc : c = tapeCfg M q a L R) :
    ∃ (q' : M.Q) (a' : M.Γ) (L' R' : List M.Γ),
      d = tapeCfg M q' a' L' R' ∧ L'.length + R'.length ≤ L.length + R.length + n ∧
      Run (machine M).step n (simCfg M q a L R) (simCfg M q' a' L' R') := by
  induction h generalizing q a L R with
  | zero => exact ⟨q, a, L, R, hc, by omega, .zero _⟩
  | cons hs ht ih =>
    rw [hc] at hs
    obtain ⟨q₁, a₁, L₁, R₁, he, hlen, hstep⟩ := step M q a L R _ hs
    obtain ⟨q₂, a₂, L₂, R₂, he₂, hlen₂, hrun⟩ := ih q₁ a₁ L₁ R₁ he
    exact ⟨q₂, a₂, L₂, R₂, he₂, by omega, .cons hstep hrun⟩

theorem read_cons (M : SingleTape) (v : Store M.Q M.Γ)
    (b : Bool) (w : List Bool) (L R : List M.Γ) :
    (machine M).step (cfg M .readInput v (b :: w) L R) =
      some (cfg M .readInput {v with head := M.input b, present := true}
        w (M.input b :: L) R) := by
  simp [FinTM2.step, machine, program, cfg, TM2.step, TM2.stepAux, tapes]
  congr 2
  funext k; cases k <;> rfl

theorem read_nil (M : SingleTape) (v : Store M.Q M.Γ) (L R : List M.Γ) :
    (machine M).step (cfg M .readInput v [] L R) =
      some (cfg M .reverseInput {v with head := M.input false, present := false} [] L R) := by
  simp [FinTM2.step, machine, program, cfg, TM2.step, TM2.stepAux, tapes]

theorem read_run (M : SingleTape) (v : Store M.Q M.Γ)
    (w : List Bool) (L R : List M.Γ) :
    Run (machine M).step (w.length + 1) (cfg M .readInput v w L R)
      (cfg M .reverseInput {v with head := M.input false, present := false}
        [] (w.reverse.map M.input ++ L) R) := by
  induction w generalizing v L with
  | nil => exact .one (read_nil M v L R)
  | cons b w ih =>
    simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append] using!
      Run.cons (read_cons M v b w L R)
        (ih {v with head := M.input b, present := true} (M.input b :: L))

theorem reverse_cons (M : SingleTape) (v : Store M.Q M.Γ)
    (a : M.Γ) (L R : List M.Γ) :
    (machine M).step (cfg M .reverseInput v [] (a :: L) R) =
      some (cfg M .reverseInput {v with head := a, present := true} [] L (a :: R)) := by
  simp [FinTM2.step, machine, program, cfg, TM2.step, TM2.stepAux, tapes]
  congr 2
  funext k; cases k <;> rfl

theorem reverse_nil (M : SingleTape) (v : Store M.Q M.Γ) (R : List M.Γ) :
    (machine M).step (cfg M .reverseInput v [] [] R) =
      some (cfg M .start {v with head := default, present := false} [] [] R) := by
  simp [FinTM2.step, machine, program, cfg, TM2.step, TM2.stepAux, tapes]

theorem reverse_run (M : SingleTape) (v : Store M.Q M.Γ) (L R : List M.Γ) :
    Run (machine M).step (L.length + 1) (cfg M .reverseInput v [] L R)
      (cfg M .start {v with head := default, present := false} [] [] (L.reverse ++ R)) := by
  induction L generalizing v R with
  | nil => exact .one (reverse_nil M v R)
  | cons a L ih =>
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using!
      Run.cons (reverse_cons M v a L R) (ih {v with head := a, present := true} (a :: R))

theorem start (M : SingleTape) (v : Store M.Q M.Γ) (R : List M.Γ) :
    (machine M).step (cfg M .start v [] [] R) =
      some (simCfg M default (R.head?.getD default) [] R.tail) := by
  simp [FinTM2.step, machine, program, cfg, simCfg, TM2.step, TM2.stepAux, tapes]
  congr 2
  funext k; cases k <;> rfl

theorem init_cfg (M : SingleTape) (w : List Bool) :
    initList (machine M) w = cfg M .readInput (initial M) w [] [] := by
  simp [initList, machine, cfg]
  congr 1
  funext k; cases k <;> rfl

/-- Input conversion uses two scans and one initial head load. -/
theorem prepare (M : SingleTape) (w : List Bool) :
    Run (machine M).step (2 * w.length + 3) (initList (machine M) w)
      (simCfg M default ((w.map M.input).head?.getD default) [] (w.map M.input).tail) := by
  rw [init_cfg]
  have h₁ := read_run M (initial M) w [] []
  simp only [List.append_nil] at h₁
  have h₂ := reverse_run M {initial M with head := M.input false, present := false}
    (w.reverse.map M.input) []
  simp only [List.length_map, List.length_reverse, ← List.map_reverse, List.reverse_reverse,
    List.append_nil] at h₂
  have h₃ := start M (initial M) (w.map M.input)
  have hr := (h₁.trans h₂).trans (.one h₃)
  convert hr using 1
  omega

def cleanStore (M : SingleTape) (b p : Bool) : Store M.Q M.Γ := ⟨default, default, b, p⟩

theorem finish (M : SingleTape) (q : M.Q) (a : M.Γ) (L R : List M.Γ)
    (h : M.transition q a = none) :
    (machine M).step (simCfg M q a L R) =
      some (cfg M .clearLeft (cleanStore M (M.accept q) false) [] L R) := by
  simp [FinTM2.step, machine, program, simCfg, cfg, TM2.step, TM2.stepAux, h, cleanStore]

theorem clear_left_cons (M : SingleTape) (b p : Bool) (a : M.Γ) (L R : List M.Γ) :
    (machine M).step (cfg M .clearLeft (cleanStore M b p) [] (a :: L) R) =
      some (cfg M .clearLeft (cleanStore M b true) [] L R) := by
  simp [FinTM2.step, machine, program, cfg, TM2.step, TM2.stepAux, cleanStore, tapes]
  congr 2
  funext k; cases k <;> rfl

theorem clear_left_nil (M : SingleTape) (b p : Bool) (R : List M.Γ) :
    (machine M).step (cfg M .clearLeft (cleanStore M b p) [] [] R) =
      some (cfg M .clearRight (cleanStore M b false) [] [] R) := by
  simp [FinTM2.step, machine, program, cfg, TM2.step, TM2.stepAux, cleanStore, tapes]

theorem clear_left (M : SingleTape) (b p : Bool) (L R : List M.Γ) :
    Run (machine M).step (L.length + 1) (cfg M .clearLeft (cleanStore M b p) [] L R)
      (cfg M .clearRight (cleanStore M b false) [] [] R) := by
  induction L generalizing p with
  | nil => exact .one (clear_left_nil M b p R)
  | cons a L ih => exact .cons (clear_left_cons M b p a L R) (ih true)

theorem clear_right_cons (M : SingleTape) (b p : Bool) (a : M.Γ) (R : List M.Γ) :
    (machine M).step (cfg M .clearRight (cleanStore M b p) [] [] (a :: R)) =
      some (cfg M .clearRight (cleanStore M b true) [] [] R) := by
  simp [FinTM2.step, machine, program, cfg, TM2.step, TM2.stepAux, cleanStore, tapes]
  congr 2
  funext k; cases k <;> rfl

theorem clear_right_nil (M : SingleTape) (b p : Bool) :
    (machine M).step (cfg M .clearRight (cleanStore M b p) [] [] []) =
      some (haltList (machine M) [b]) := by
  simp [FinTM2.step, machine, program, cfg, TM2.step, TM2.stepAux, cleanStore,
    tapes, haltList, initial]
  congr 2
  funext k; cases k <;> rfl

theorem clear_right (M : SingleTape) (b p : Bool) (R : List M.Γ) :
    Run (machine M).step (R.length + 1) (cfg M .clearRight (cleanStore M b p) [] [] R)
      (haltList (machine M) [b]) := by
  induction R generalizing p with
  | nil => exact .one (clear_right_nil M b p)
  | cons a R ih => exact .cons (clear_right_cons M b p a R) (ih true)

/-- Complete simulation, including input conversion and erasing both work stacks. -/
theorem outputs (M : SingleTape) (w : List Bool) {n : ℕ} {c : TM0.Cfg M.Γ M.Q}
    (hr : Run (TM0.step M.transition) n (TM0.init (w.map M.input)) c)
    (hh : TM0.step M.transition c = none) :
    Within (machine M).step (3 * w.length + 2 * n + 6)
      (initList (machine M) w) (haltList (machine M) [M.accept c.q]) := by
  have hi : TM0.init (w.map M.input) =
      tapeCfg M default ((w.map M.input).head?.getD default) [] (w.map M.input).tail := by
    generalize w.map M.input = l
    cases l <;> rfl
  obtain ⟨q', a', L', R', he, hlen, hrun⟩ :=
    run M hr default _ [] (w.map M.input).tail hi
  rw [he] at hh ⊢
  have halt : M.transition q' a' = none := Option.map_eq_none_iff.mp hh
  have hf := finish M q' a' L' R' halt
  have hl := clear_left M (M.accept q') false L' R'
  have hr' := clear_right M (M.accept q') false R'
  have hall := (((prepare M w).trans hrun).trans (.one hf)).trans (hl.trans hr')
  refine ⟨_, ?_, hall⟩
  simp only [List.length_nil, List.length_tail, List.length_map] at hlen
  omega

/-- Elementary single-tape polynomial time implies the original stack definition of P. -/
theorem singleTapeP_subset_P : SingleTapeP ⊆ Lax888664.PolynomialTime.P := by
  classical
  rintro L ⟨M, p, hM⟩
  let f : List Bool → Bool := fun w ↦ decide (w ∈ L)
  let p' : Polynomial ℕ := 3 * Polynomial.X + 2 * p + 6
  have hrun (w : List Bool) : Within (machine M).step (p'.eval w.length)
      (initList (machine M) w) (haltList (machine M) [f w]) := by
    obtain ⟨c, ⟨hc⟩, hh, ha⟩ := hM w
    have hf : M.accept c.q = f w := by
      apply Bool.eq_iff_iff.mpr
      simpa [f] using ha
    have hr := outputs M w (Run.of_iterate hc.evals_in_steps) hh
    rw [hf] at hr
    apply hr.mono
    have hn := hc.steps_le_m
    simp only [p', Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    omega
  refine ⟨f, fun w ↦ by simp [f], ⟨{
    tm := machine M
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := p'
    outputsFun := fun w ↦ ?_ }⟩⟩
  change StateTransition.EvalsToInTime (machine M).step
    (initList (machine M) (w.map id)) (some (haltList (machine M) [f w])) (p'.eval w.length)
  rw [List.map_id]
  exact Within.evals (hrun w)

end Lax888664Proofs.TapeToStack
