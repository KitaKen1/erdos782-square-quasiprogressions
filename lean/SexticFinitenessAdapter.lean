module

public import SixRootPolynomial
public import AdelicBridge
public import TauCeti.FieldTheory.FunctionField.Hyperelliptic.RationalPoint
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open Polynomial
open scoped IntermediateField

namespace Erdos782Arithmetic

variable {K : Type} [Field K] [CharZero K]

/-- A finite set of rational abscissae on the six-branch-point curve. -/
theorem sixRootFinitenessAdapter
    (faltings : ∀ {F : Type} [Field F] [Algebra K F] [Algebra (RatFunc K) F]
      [IsScalarTower K (RatFunc K) F] [FunctionField K F],
      2 ≤ Faltings.genus K F → {v : Faltings.Place K F | v.IsDegreeOne}.Finite)
    (h : Fin 6 → ℕ) (hh : Function.Injective h) :
    {t : K | ∃ y : K, y ^ 2 = ∏ j, (t + (h j : K))}.Finite := by
  classical
  let f := sixRootPolynomial (K := K) h
  have hfs : Squarefree f := squarefree_sixRootPolynomial hh
  have hdeg : f.natDegree = 6 := natDegree_sixRootPolynomial h
  have hpos : 0 < f.natDegree := by simp [hdeg]
  let q : (RatFunc K)[X] := X ^ 2 - C (algebraMap K[X] (RatFunc K) f)
  letI : Fact (Irreducible q) := ⟨irreducible_sixRootExtension hh⟩
  let F := AdjoinRoot q
  haveI : IsScalarTower K (RatFunc K) F :=
    inferInstanceAs (IsScalarTower K (RatFunc K) (AdjoinRoot q))
  let y : F := AdjoinRoot.root q
  have hy : y ^ 2 = algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) f) :=
    root_X_pow_sub_C_pow 2 _
  have hgen : (RatFunc K)⟮y⟯ = ⊤ := IntermediateField.adjoin_root_eq_top q
  have h₂ : (2 : K) ≠ 0 := by norm_num
  obtain ⟨hfd, _⟩ := TauCeti.finiteDimensional_and_isSeparable_of_sq_eq h₂ hfs hpos hgen hy
  let : FiniteDimensional (RatFunc K) F := hfd
  have hF : TauCeti.IsFunctionField K F :=
    TauCeti.isFunctionField_iff_functionField.mpr inferInstance
  have hex : IsIntegrallyClosedIn K F :=
    TauCeti.isIntegrallyClosedIn_of_sq_eq h₂ hfs hpos hgen hy
  have hg : 2 ≤ Faltings.genus K F := by
    rw [genus_eq hF hex, TauCeti.genus_eq_of_sq_eq h₂ hfs hpos hgen hy, hdeg]
  have hfinite := faltings hg
  let : Finite {v : Faltings.Place K F | v.IsDegreeOne} := hfinite.to_subtype
  let Z : Set K := {t | f.eval t = 0}
  have hZ : Z.Finite := by
    apply (f.roots.toFinset.finite_toSet).subset
    intro t ht
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hfs.ne_zero).mpr ht)
  let U : Set K := {t | ∃ z : K, z ≠ 0 ∧ z ^ 2 = f.eval t}
  have hplaces (t : U) : ∃ Q : TauCeti.Place K F,
      Q.restrict K (RatFunc K) = TauCeti.Place.adicOfIrreducible (irreducible_X_sub_C t.1) ∧
        Q.degree = 1 := by
    obtain ⟨b, hb, he⟩ := t.2
    obtain ⟨Q, hr, hd, _⟩ :=
      TauCeti.Place.exists_ord_sub_pos_of_sq_eq h₂ hfs hpos hgen hy hb he
    exact ⟨Q, hr, hd⟩
  choose g hr hd using hplaces
  have hinj : Function.Injective g := by
    intro t u htu
    apply Subtype.ext
    apply TauCeti.Place.adicOfIrreducible_X_sub_C_injective
    exact (hr t).symm.trans ((congrArg
      (fun Q : TauCeti.Place K F => Q.restrict K (RatFunc K)) htu).trans (hr u))
  have hU : U.Finite := by
    rw [← Set.finite_coe_iff]
    apply Finite.of_injective
      (fun t : U => (⟨toFaltingsPlace (g t), toFaltingsPlace_isDegreeOne (hd t)⟩ :
        {v : Faltings.Place K F | v.IsDegreeOne}))
    · exact fun _ _ ht => hinj (toFaltingsPlace_injective (congrArg Subtype.val ht))
  refine (hZ.union hU).subset ?_
  rintro t ⟨b, hb⟩
  have he : b ^ 2 = f.eval t := hb.trans (eval_sixRootPolynomial h t).symm
  by_cases hz : b = 0
  · left
    simpa [Z, hz] using he.symm
  · exact Or.inr ⟨b, hz, he⟩

end Erdos782Arithmetic

#print axioms Erdos782Arithmetic.sixRootFinitenessAdapter
