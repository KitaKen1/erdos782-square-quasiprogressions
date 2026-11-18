module

public import Comparator.FCStatement
public import Erdos782QuasiProgressions.PlanarWalk
public import SexticFiniteness

@[expose] public section

namespace Erdos782

theorem erdos_782.parts.i_neg :
    ¬ (∃ C : ℕ, 0 < C ∧ ∀ k : ℕ,
      ContainsQuasiProgression {n : ℕ | IsSquare n} C k) :=
  Erdos782Reduction.not_exists_width Erdos782Walk.planarWalk Erdos782Arithmetic.sixRootFiniteness

end Erdos782

#print axioms Erdos782.erdos_782.parts.i_neg
