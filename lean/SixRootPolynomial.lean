module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Tactic

@[expose] public section

open Polynomial

namespace Erdos782Arithmetic

variable {K : Type*} [Field K] [CharZero K]

/-- The sextic obtained by multiplying the six affine terms on the lattice line. -/
noncomputable def sixRootPolynomial (h : Fin 6 → ℕ) : K[X] :=
  ∏ j, (X - C (-(h j : K)))

theorem eval_sixRootPolynomial (h : Fin 6 → ℕ) (t : K) :
    (sixRootPolynomial (K := K) h).eval t = ∏ j, (t + (h j : K)) := by
  simp [sixRootPolynomial, eval_prod]

theorem squarefree_sixRootPolynomial {h : Fin 6 → ℕ} (hh : Function.Injective h) :
    Squarefree (sixRootPolynomial (K := K) h) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    have hne : (-(h i : K)) ≠ -(h j : K) := by
      intro he
      apply hij
      apply hh
      exact_mod_cast neg_injective he
    exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hne).isUnit).isRelPrime
  · intro i _
    exact (irreducible_X_sub_C _).squarefree

theorem natDegree_sixRootPolynomial (h : Fin 6 → ℕ) :
    (sixRootPolynomial (K := K) h).natDegree = 6 := by
  unfold sixRootPolynomial
  rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C (-(h j : K)))]
  simp_rw [natDegree_X_sub_C]
  simp

private theorem not_square_in_ratFunc {f : K[X]} (hs : Squarefree f)
    (hd : 0 < f.natDegree) (r : RatFunc K) :
    r ^ 2 ≠ algebraMap K[X] (RatFunc K) f := by
  intro he
  have hi : IsIntegral K[X] r := by
    refine ⟨X ^ 2 - C f, monic_X_pow_sub_C f (by decide : 2 ≠ 0), ?_⟩
    simp [he]
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
  have hfg : g ^ 2 = f := by
    apply (IsFractionRing.injective K[X] (RatFunc K))
    rw [map_pow, ← he, hg]
  have hu : IsUnit g := hs g ⟨1, by simp [← hfg, pow_two]⟩
  have hzero : g.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
  rw [← hfg, natDegree_pow, hzero, mul_zero] at hd
  exact (lt_irrefl _ hd)

theorem irreducible_sixRootExtension {h : Fin 6 → ℕ} (hh : Function.Injective h) :
    Irreducible (X ^ 2 - C (algebraMap K[X] (RatFunc K) (sixRootPolynomial (K := K) h)) :
      (RatFunc K)[X]) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two
    (not_square_in_ratFunc (squarefree_sixRootPolynomial (K := K) hh)
      (by simp [natDegree_sixRootPolynomial]))

end Erdos782Arithmetic

#print axioms Erdos782Arithmetic.irreducible_sixRootExtension
