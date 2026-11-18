module

public import SexticFinitenessAdapter
public import Mordell.MordellConjecture.FunctionField

@[expose] public section

namespace Erdos782Arithmetic

/-- Faltings' theorem gives finitely many rational abscissae on the six-root curve. -/
theorem sixRootFiniteness (h : Fin 6 → ℕ) (hh : Function.Injective h) :
    {t : ℚ | ∃ y : ℚ, y ^ 2 = ∏ j, (t + (h j : ℚ))}.Finite :=
  sixRootFinitenessAdapter (K := ℚ) (fun hg => Faltings.finite_setOf_place_isDegreeOne hg) h hh

end Erdos782Arithmetic
