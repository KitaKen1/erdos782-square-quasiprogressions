module

public import Comparator.Spec
public import Erdos782QuasiProgressions

@[expose] public section

namespace Erdos782

theorem part_i_negative (walk : PlanarWalkInput) (finitePoints : RationalPointInput) :
    ¬ ArbitrarilyLongSquareQuasiProgressions :=
  Erdos782Reduction.not_exists_width walk finitePoints

end Erdos782

#print axioms Erdos782.part_i_negative
