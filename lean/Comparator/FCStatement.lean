-- Generated from FormalConjectures/ErdosProblems/782.lean.
-- Copyright 2026 The Formal Conjectures Authors. Licensed under Apache-2.0.
-- FC revision 2de491f90132d3f3fac934edf5bd72acb3dfd15c.
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Set.Defs

@[expose] public section

namespace Erdos782

def ContainsQuasiProgression (S : Set ℕ) (C k : ℕ) : Prop :=
  ∃ (x : ℕ → ℕ) (d : ℕ), 0 < d ∧ (∀ i < k, x i ∈ S) ∧
    ∀ i, i + 1 < k → x i + d ≤ x (i + 1) ∧ x (i + 1) ≤ x i + d + C

/-- The type of FC's erdos_782.parts.i, captured without its proof. -/
abbrev FCPartIStatement : Prop :=
    ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ, ContainsQuasiProgression {n : ℕ | IsSquare n} C k

end Erdos782
