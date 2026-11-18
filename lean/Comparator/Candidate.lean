module

public import Comparator.Spec
public import Erdos782QuasiProgressions

@[expose] public section

namespace Erdos782

theorem erdos_782.parts.i_neg
    (walk : PlanarWalkInput) (finitePoints : RationalPointInput) :
    ¬ (∃ C : ℕ, 0 < C ∧ ∀ k : ℕ,
      ContainsQuasiProgression {n : ℕ | IsSquare n} C k) :=
  Erdos782Reduction.not_exists_width walk finitePoints

end Erdos782

#print axioms Erdos782.erdos_782.parts.i_neg
