import Lax888664Proofs.FiniteControl

set_option backward.isDefEq.respectTransparency false

/-! Turn a Boolean read from the final tape square into a conventional accepting state. -/

namespace Lax888664Proofs.TapeOutput

open Turing Time

variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q]
variable (M : TM0.Machine Γ Q) (read : Q → Γ → Bool)

@[reducible] def initial (Q : Type) [Inhabited Q] : Inhabited (Sum Q Bool) :=
  ⟨Sum.inl default⟩

attribute [local instance] initial

def program : TM0.Machine Γ (Sum Q Bool)
  | .inl q, a => match M q a with
      | none => some (.inr (read q a), .write a)
      | some (q', act) => some (.inl q', act)
  | .inr _, _ => none

def cfg (c : TM0.Cfg Γ Q) : TM0.Cfg Γ (Sum Q Bool) := ⟨.inl c.q, c.Tape⟩

theorem step {a b : TM0.Cfg Γ Q} (h : TM0.step M a = some b) :
    TM0.step (program M read) (cfg a) = some (cfg b) := by
  rcases a with ⟨q, T⟩
  cases he : M q T.head with
  | none => simp [TM0.step, he] at h
  | some p =>
    cases p with | mk q' act =>
      simp only [TM0.step, he, Option.map_some] at h
      cases Option.some.inj h
      cases act <;> simp [TM0.step, program, cfg, he]

theorem run {n : ℕ} {a b : TM0.Cfg Γ Q} (h : Run (TM0.step M) n a b) :
    Run (TM0.step (program M read)) n (cfg a) (cfg b) :=
  h.map cfg (fun _ _ hs ↦ step M read hs)

theorem finish (c : TM0.Cfg Γ Q) (h : TM0.step M c = none) :
    TM0.step (program M read) (cfg c) =
      some ⟨.inr (read c.q c.Tape.head), c.Tape⟩ := by
  have he : M c.q c.Tape.head = none := Option.map_eq_none_iff.mp h
  simp [TM0.step, program, cfg, he, Tape.write_self]

theorem halted (b : Bool) (T : Tape Γ) :
    TM0.step (program M read) ⟨.inr b, T⟩ = none := rfl

noncomputable def labels (S : Finset Q) : Finset (Sum Q Bool) := by
  classical
  exact S.image Sum.inl ∪ {Sum.inr false, Sum.inr true}

omit [Inhabited Γ] in
theorem supports {S : Finset Q} (hS : TM0.Supports M (S : Set Q)) :
    TM0.Supports (program M read) (labels S : Set (Sum Q Bool)) := by
  classical
  refine ⟨by simpa [labels, default] using hS.1, ?_⟩
  intro q a q' act h hq
  cases q with
  | inr b => cases h
  | inl q =>
    have hq' : q ∈ S := by simpa [labels] using hq
    cases he : M q a with
    | none =>
      have hp : (Sum.inr (read q a), TM0.Stmt.write a) = (q', act) :=
        Option.some.inj (by simpa only [program, he] using! h)
      cases hp
      cases read q a <;> simp [labels]
    | some p =>
      rcases p with ⟨r, instr⟩
      have hp : (Sum.inl r, instr) = (q', act) :=
        Option.some.inj (by simpa only [program, he] using! h)
      cases hp
      have hr := hS.2 he hq'
      simp [labels]
      exact hr

/-- A finite-supported machine with a Boolean observation of its halting
configuration yields an ordinary finite single-tape decider, with one extra step. -/
theorem of_supported [Fintype Γ] (S : Finset Q) (hS : TM0.Supports M (S : Set Q))
    (input : Bool ↪ Γ) (hi : ∀ b, input b ≠ default) (p : Polynomial ℕ)
    (L : Lax888664.PolynomialTime.Language)
    (h : ∀ w : List Bool, ∃ c : TM0.Cfg Γ Q,
      Within (TM0.step M) (p.eval w.length) (TM0.init (w.map input)) c ∧
      TM0.step M c = none ∧ (read c.q c.Tape.head = true ↔ w ∈ L)) :
    L ∈ Lax888664.MachineModels.SingleTapeP := by
  classical
  let W := program M read
  let S' := labels S
  have hS' : TM0.Supports W (S' : Set (Sum Q Bool)) := supports M read hS
  letI := FiniteControl.initial W S' hS'
  let N : Lax888664.MachineModels.SingleTape :=
    { Γ := Γ
      Q := {q // q ∈ S'}
      input := input
      input_ne_blank := hi
      transition := FiniteControl.restrict W S' hS'
      accept := fun q ↦ q.val.elim (fun _ ↦ false) id }
  refine ⟨N, p + 1, fun w ↦ ?_⟩
  obtain ⟨c, ⟨n, hn, hr⟩, hc, ha⟩ := h w
  have hrun := (run M read hr).trans (Run.one (finish M read c hc))
  obtain ⟨c', he, ht⟩ := FiniteControl.run W S' hS' hrun hS'.1
  refine ⟨c', ⟨Within.evals ⟨n + 1, ?_, ht⟩⟩, ?_, ?_⟩
  · simpa using Nat.add_le_add_right hn 1
  · apply FiniteControl.halted W S' hS'
    rw [he]
    exact halted M read _ _
  · have hq := congrArg TM0.Cfg.q he
    change c'.q.val = Sum.inr (read c.q c.Tape.head) at hq
    change (c'.q.val.elim (fun _ ↦ false) id = true) ↔ w ∈ L
    simpa only [hq, Sum.elim_inr, id_eq] using ha

end Lax888664Proofs.TapeOutput
