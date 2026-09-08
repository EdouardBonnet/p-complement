import Lax554803.PolynomialTime
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
---
title: Finite-stack and elementary single-tape definitions of P
type: definition
---
These definitions specify machine models independently. `FiniteStackP` requires
every stack alphabet to be finite. `SingleTapeP` uses an elementary deterministic
single-tape machine: each transition either moves the head one square or writes
one symbol. Both its alphabet and control-state type are finite. The input is
written in its original order, starting at the head, with blank tape elsewhere.
The two input symbols are distinct and different from blank. A halted control
state determines the Boolean answer; work tape need not be erased.
-/

namespace Lax554803.MachineModels

open Turing PolynomialTime

/-- Polynomial-time stack deciders with finite alphabets at every stack. -/
def FiniteStackP : Set Language :=
  {L | ∃ (f : Word → Bool)
    (M : TM2ComputableInPolyTime id Computability.encodeBool f),
    (∀ w, f w = true ↔ w ∈ L) ∧ ∀ k, Finite (M.tm.Γ k)}

/-- A finite elementary single-tape machine, with ordinary binary input. -/
structure SingleTape where
  Γ : Type
  Q : Type
  [alphabet : Fintype Γ]
  [control : Fintype Q]
  [blank : Inhabited Γ]
  [initial : Inhabited Q]
  input : Bool ↪ Γ
  input_ne_blank : ∀ b, input b ≠ default
  transition : TM0.Machine Γ Q
  accept : Q → Bool

attribute [instance] SingleTape.alphabet SingleTape.control SingleTape.blank SingleTape.initial

/-- The standard single-tape formulation: one machine and one polynomial,
halting on every input, with acceptance exactly matching membership. -/
def SingleTapeP : Set Language :=
  {L | ∃ (M : SingleTape) (p : Polynomial ℕ), ∀ w : Word,
    ∃ c : TM0.Cfg M.Γ M.Q,
      Nonempty (StateTransition.EvalsToInTime (TM0.step M.transition)
        (TM0.init (w.map M.input)) (some c) (p.eval w.length)) ∧
      TM0.step M.transition c = none ∧ (M.accept c.q = true ↔ w ∈ L)}

end Lax554803.MachineModels
