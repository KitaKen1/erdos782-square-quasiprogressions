module

import Erdos782QuasiProgressions

open Erdos782Reduction

-- The statement of part (i) with FC's quasi-progression definition expanded.
example (walk : PlanarWalkTheorem) (finitePoints : SixRootFiniteness) :
    ¬ ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ,
      ∃ (x : ℕ → ℕ) (d : ℕ), 0 < d ∧
        (∀ i < k, x i ∈ {n : ℕ | IsSquare n}) ∧
        ∀ i, i + 1 < k → x i + d ≤ x (i + 1) ∧ x (i + 1) ≤ x i + d + C :=
  not_exists_width walk finitePoints

/-- info: 'Erdos782Reduction.not_exists_width' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos782Reduction.not_exists_width
