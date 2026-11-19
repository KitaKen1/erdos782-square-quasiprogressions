module

public import Mordell.FunctionField.Genus
public import TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring

@[expose] public section

namespace Erdos782Arithmetic

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F]

/-- Forget the normalization of a Tau Ceti valuation and keep its valuation ring. -/
noncomputable def toFaltingsPlace (P : TauCeti.Place k F) : Faltings.Place k F := by
  let A : Subalgebra k F := { P.integers.toSubring with
    algebraMap_mem' := P.algebraMap_mem_integers }
  refine
    { toSubalgebra := A
      neg_mem' := fun {x} hx => P.integers.neg_mem x hx
      mem_or_inv_mem' := P.integers.mem_or_inv_mem
      ne_top := ?_ }
  intro hA
  apply P.integers_ne_top
  ext x
  change x ∈ A ↔ x ∈ (⊤ : ValuationSubring F)
  rw [hA]
  simp

@[simp]
theorem toFaltingsPlace_mem (P : TauCeti.Place k F) (a : F) :
    a ∈ (toFaltingsPlace P).toSubalgebra ↔ a ∈ P.integers := Iff.rfl

theorem toFaltingsPlace_injective :
    Function.Injective (toFaltingsPlace : TauCeti.Place k F → Faltings.Place k F) := by
  intro P Q h
  exact TauCeti.Place.integers_injective (congrArg Faltings.Place.toValuationSubring h)

theorem toFaltingsPlace_isDegreeOne {P : TauCeti.Place k F} (h : P.degree = 1) :
    (toFaltingsPlace P).IsDegreeOne := by
  change Module.rank k (IsLocalRing.ResidueField P.integers) = 1
  rw [← (P.residueFieldEquivOfDegreeEqOne h).toLinearEquiv.rank_eq]
  exact Module.rank_self k

theorem toFaltingsPlace_surjective (hF : TauCeti.IsFunctionField k F) :
    Function.Surjective (toFaltingsPlace : TauCeti.Place k F → Faltings.Place k F) := by
  intro P
  have hconst (c : k) : algebraMap k F c ∈ P.toValuationSubring :=
    P.toSubalgebra.algebraMap_mem c
  have hproper : P.toValuationSubring ≠ ⊤ := by
    intro heq
    apply P.ne_top
    ext x
    change x ∈ P.toValuationSubring ↔ x ∈ (⊤ : Subalgebra k F)
    rw [heq]
    simp
  obtain ⟨Q, hQ, _⟩ :=
    TauCeti.Place.existsUnique_integers_eq hF hconst hproper
  refine ⟨Q, ?_⟩
  ext x
  change x ∈ Q.integers ↔ x ∈ P.toValuationSubring
  rw [hQ]

noncomputable def placeEquiv (hF : TauCeti.IsFunctionField k F) :
    TauCeti.Place k F ≃ Faltings.Place k F :=
  Equiv.ofBijective toFaltingsPlace ⟨toFaltingsPlace_injective, toFaltingsPlace_surjective hF⟩

theorem placeEquiv_apply (hF : TauCeti.IsFunctionField k F) (P : TauCeti.Place k F) :
    placeEquiv hF P = toFaltingsPlace P := rfl

end Erdos782Arithmetic
