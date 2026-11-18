module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! Elementary reduction of Erdős 782(i) to the planar walk theorem of
Gerver and Ramsey and the six-branch-point case of Faltings's theorem.
The two deep inputs are explicit hypotheses of the final theorem. -/

namespace Erdos782Reduction

/-- The graph-walk special case of Gerver–Ramsey. Six points of the graph
are on a line. Subtracting the smallest selected index gives offsets h. -/
def PlanarWalkTheorem : Prop :=
  ∀ C : ℕ, ∃ N : ℕ, ∀ e : ℕ → ℕ,
    (∀ i < N, e i ≤ e (i + 1) ∧ e (i + 1) ≤ e i + C) →
    ∃ (b : ℕ) (h : Fin 6 → Fin (N + 1)) (a : ℚ),
      b ≤ N ∧ Function.Injective h ∧ 0 ≤ a ∧ a ≤ C ∧
      ∀ j, b + (h j).val ≤ N ∧
        (e (b + (h j).val) : ℚ) = e b + a * (h j).val

/-- Affine rational abscissae on y² = ∏(t+hⱼ), a smooth genus-two model
after completion because the six branch points are distinct. -/
def SixRootFiniteness : Prop :=
  ∀ h : Fin 6 → ℕ, Function.Injective h →
    {t : ℚ | ∃ y : ℚ, y ^ 2 = ∏ j, (t + (h j : ℚ))}.Finite

private theorem uniformBound (finitePoints : SixRootFiniteness) (N : ℕ) :
    ∃ T : ℕ, ∀ h : Fin 6 → Fin (N + 1), Function.Injective h →
      ∀ t y : ℚ, y ^ 2 = ∏ j, (t + ((h j).val : ℚ)) → t ≤ T := by
  classical
  let points (h : Fin 6 → Fin (N + 1)) : Set ℚ :=
    {t | Function.Injective h ∧ ∃ y : ℚ, y ^ 2 = ∏ j, (t + ((h j).val : ℚ))}
  have hf (h : Fin 6 → Fin (N + 1)) : (points h).Finite := by
    by_cases hi : Function.Injective h
    · exact (finitePoints (fun j => (h j).val) (Fin.val_injective.comp hi)).subset
        (fun _ hx => hx.2)
    · simp [points, hi]
  obtain ⟨v, hv⟩ := (Set.finite_iUnion hf).bddAbove
  obtain ⟨T, hT⟩ := exists_nat_ge v
  refine ⟨T, fun h hi t y hy => (hv ?_).trans hT⟩
  exact Set.mem_iUnion.mpr ⟨h, hi, y, hy⟩

private theorem productIdentity (q t : ℚ) (hq : 0 < q) (h : Fin 6 → ℕ)
    (r : Fin 6 → ℚ) (hr : ∀ j, r j ^ 2 = q * (t + h j)) :
    ((∏ j, r j) / q ^ 3) ^ 2 = ∏ j, (t + h j) := by
  have hprod : (∏ j, r j ^ 2) = ∏ j, (q * (t + h j)) :=
    Finset.prod_congr rfl (fun j _ => hr j)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_pow] at hprod
  rw [div_pow, hprod]
  field_simp

/-- Same quantifiers and natural-number indexing as ContainsQuasiProgression
in FC, with membership in the squares expanded as an explicit root. -/
def SquareBlock (C k : ℕ) : Prop :=
  ∃ (x : ℕ → ℕ) (d : ℕ), 0 < d ∧ (∀ i < k, ∃ r : ℕ, x i = r * r) ∧
    ∀ i, i + 1 < k → x i + d ≤ x (i + 1) ∧ x (i + 1) ≤ x i + d + C

/-- Definitional comparison with FC's set-membership expression. -/
theorem squareBlock_iff_fc (C k : ℕ) : SquareBlock C k ↔
    ∃ (x : ℕ → ℕ) (d : ℕ), 0 < d ∧
      (∀ i < k, x i ∈ {n : ℕ | IsSquare n}) ∧
      ∀ i, i + 1 < k → x i + d ≤ x (i + 1) ∧ x (i + 1) ≤ x i + d + C := by
  rfl

theorem noArbitrarilyLong (walk : PlanarWalkTheorem) (finitePoints : SixRootFiniteness) :
    ∀ C : ℕ, ∃ k : ℕ, ¬ SquareBlock C k := by
  intro C
  obtain ⟨N, hN⟩ := walk C
  obtain ⟨T, hT⟩ := uniformBound finitePoints N
  let m := T * (C + 1) + 1
  refine ⟨m + N + 1, ?_⟩
  rintro ⟨x, d, hd, squares, gaps⟩
  have growth (i : ℕ) (hi : i ≤ m + N) : i * d ≤ x i := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hg := (gaps i (by omega)).1
      rw [Nat.succ_mul]
      exact (Nat.add_le_add_right (ih (by omega)) d).trans hg
  let e (i : ℕ) := x (m + i) - (m + i) * d
  have decomp (i : ℕ) (hi : i ≤ N) :
      x (m + i) = (m + i) * d + e i := by
    have := growth (m + i) (by omega)
    dsimp [e]
    omega
  have ew (i : ℕ) (hi : i < N) : e i ≤ e (i + 1) ∧ e (i + 1) ≤ e i + C := by
    have hx := gaps (m + i) (by omega)
    have h0 := decomp i (by omega)
    have h1 := decomp (i + 1) (by omega)
    rw [← Nat.add_assoc, Nat.add_one_mul] at h1
    omega
  obtain ⟨b, h, a, hb, hinj, ha, hC, line⟩ := hN e ew
  let q : ℚ := d + a
  have hq : 0 < q := by dsimp [q]; positivity
  let X : ℕ := x (m + b)
  let t : ℚ := X / q
  have identityAt (j : Fin 6) : (x (m + (b + (h j).val)) : ℚ) =
      q * (t + ((h j).val : ℚ)) := by
    have base : (X : ℚ) = (m + b : ℕ) * (d : ℚ) + (e b : ℚ) := by
      exact_mod_cast decomp b hb
    have hs : (x (m + (b + (h j).val)) : ℚ) =
        (m + (b + (h j).val) : ℕ) * (d : ℚ) + (e (b + (h j).val) : ℚ) := by
      exact_mod_cast decomp _ (line j).1
    rw [hs, (line j).2]
    simp only [Nat.cast_add] at base ⊢
    dsimp only [t]
    have hcancel : q * ((X : ℚ) / q) = X := by field_simp
    rw [mul_add, hcancel, base]
    dsimp [q]
    ring
  choose r hr using fun j : Fin 6 =>
    squares (m + (b + (h j).val)) (by have := (line j).1; omega)
  have hr' (j : Fin 6) : (r j : ℚ)^2 = q * (t + ((h j).val : ℚ)) := by
    rw [← identityAt j, hr j, Nat.cast_mul, pow_two]
  have ht := hT h hinj t _ (productIdentity q t hq _ _ hr')
  have hxq : (X : ℚ) ≤ T * q := (div_le_iff₀ hq).mp ht
  have hqd : q ≤ (C + 1 : ℕ) * (d : ℚ) := by
    dsimp [q]
    push_cast
    have hd1 : (1 : ℚ) ≤ d := by exact_mod_cast hd
    nlinarith [mul_nonneg (show (0 : ℚ) ≤ C by positivity) (sub_nonneg.mpr hd1)]
  have upper : (X : ℚ) ≤ (T * (C + 1) : ℕ) * (d : ℚ) := by
    push_cast
    calc
      _ ≤ T * q := hxq
      _ ≤ T * ((C + 1 : ℕ) * (d : ℚ)) := by gcongr
      _ = _ := by push_cast; ring
  have upperNat : X ≤ T * (C + 1) * d := by exact_mod_cast upper
  have lower := growth (m + b) (by omega)
  change (m + b) * d ≤ X at lower
  have hm : T * (C + 1) < m + b := by dsimp [m]; omega
  exact (Nat.mul_lt_mul_of_pos_right hm hd).not_ge (lower.trans upperNat)

/-- The negative answer in the existential quantifier order used by FC. -/
theorem not_exists_width (walk : PlanarWalkTheorem) (finitePoints : SixRootFiniteness) :
    ¬ ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ, SquareBlock C k := by
  rintro ⟨C, _, allLengths⟩
  obtain ⟨k, impossible⟩ := noArbitrarilyLong walk finitePoints C
  exact impossible (allLengths k)

end Erdos782Reduction
