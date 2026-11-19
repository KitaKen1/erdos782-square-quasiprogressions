module

public import Comparator.FCStatement

@[expose] public section

namespace Erdos782

set_option warn.sorry false in
theorem erdos_782.parts.i_neg :
    ¬ (∃ C : ℕ, 0 < C ∧ ∀ k : ℕ,
      ContainsQuasiProgression {n : ℕ | IsSquare n} C k) := by
  sorry

end Erdos782
