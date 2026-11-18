module

public import Comparator.FCStatement
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

namespace Erdos782

/-- The form of the planar walk theorem needed for the reduction. -/
def PlanarWalkInput : Prop :=
  ∀ C : ℕ, ∃ N : ℕ, ∀ e : ℕ → ℕ,
    (∀ i < N, e i ≤ e (i + 1) ∧ e (i + 1) ≤ e i + C) →
    ∃ (b : ℕ) (h : Fin 6 → Fin (N + 1)) (a : ℚ),
      b ≤ N ∧ Function.Injective h ∧ 0 ≤ a ∧ a ≤ C ∧
      ∀ j, b + (h j).val ≤ N ∧
        (e (b + (h j).val) : ℚ) = e b + a * (h j).val

/-- Finiteness of the rational abscissae for the six-root curves. -/
def RationalPointInput : Prop :=
  ∀ h : Fin 6 → ℕ, Function.Injective h →
    {t : ℚ | ∃ y : ℚ, y ^ 2 = ∏ j, (t + (h j : ℚ))}.Finite

end Erdos782
