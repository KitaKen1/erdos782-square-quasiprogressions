module

public import Comparator.FCStatement
public import Erdos782QuasiProgressions.PlanarWalk
public import SexticFinitenessAdapter

@[expose] public section

namespace Erdos782

example
    (faltings : ∀ {K F : Type} [Field K] [NumberField K] [Field F]
      [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FunctionField K F],
      2 ≤ Faltings.genus K F → {v : Faltings.Place K F | v.IsDegreeOne}.Finite) :
    ¬ (∃ C : ℕ, 0 < C ∧ ∀ k : ℕ,
      ContainsQuasiProgression {n : ℕ | IsSquare n} C k) :=
  Erdos782Reduction.not_exists_width Erdos782Walk.planarWalk
    (Erdos782Arithmetic.sixRootFinitenessAdapter (K := ℚ) (fun hg => faltings hg))

end Erdos782
