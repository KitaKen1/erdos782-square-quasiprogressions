module

public import Erdos782QuasiProgressions
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Interval
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

@[expose] public section

/-!
# The bounded-increment lattice walk lemma

If all integer levels of every rational slope contain at most five vertices, bounded steps
force an infinite walk eventually to stay on one side of any rational slope. Its average
slope then converges. Dirichlet approximation puts too many late vertices on too few
parallel integer levels. Compactness of the space of bounded increment sequences gives a
uniform finite length bound.
-/

open Set Filter Topology
open scoped BigOperators

namespace Erdos782Walk

private def drift (e : ℕ → ℕ) (p q : ℤ) (n : ℕ) : ℤ :=
  q * (e n : ℤ) - p * (n : ℤ)

private def SmallFibers (e : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ (p q z : ℤ), 0 < q →
    ((Finset.range (N + 1)).filter fun n => drift e p q n = z).card ≤ 5

private theorem fiber_card_le (e : ℕ → ℕ) (h : ∀ N, SmallFibers e N)
    (s : Finset ℕ) (p q z : ℤ) (hq : 0 < q) :
    (s.filter fun n => drift e p q n = z).card ≤ 5 := by
  refine (Finset.card_le_card (t := (Finset.range (s.sup id + 1)).filter
      fun n => drift e p q n = z) ?_).trans (h _ p q z hq)
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn.1)), hn.2⟩

private theorem eventually_outside (e : ℕ → ℕ) (h : ∀ N, SmallFibers e N)
    (p q B : ℤ) (hq : 0 < q) :
    ∀ᶠ n in atTop, ¬ (drift e p q n ∈ Finset.Icc (-B) B) := by
  classical
  have hf (z : ℤ) : {n : ℕ | drift e p q n = z}.Finite := by
    by_contra hi
    have inf : {n : ℕ | drift e p q n = z}.Infinite := hi
    obtain ⟨s, hs, hc⟩ := inf.exists_subset_card_eq 6
    have hall : s.filter (fun n => drift e p q n = z) = s :=
      Finset.filter_true_of_mem fun n hn => hs hn
    have hh := fiber_card_le e h s p q z hq
    rw [hall, hc] at hh
    omega
  have hbounded : {n : ℕ | drift e p q n ∈ Finset.Icc (-B) B}.Finite := by
    refine (Set.Finite.biUnion (Finset.Icc (-B) B).finite_toSet (fun z _ => hf z)).subset ?_
    intro n hn
    exact Set.mem_iUnion₂.mpr ⟨drift e p q n, hn, rfl⟩
  obtain ⟨M, hM⟩ := hbounded.bddAbove
  filter_upwards [eventually_ge_atTop (M + 1)] with n hn hmem
  have : n ≤ M := hM hmem
  omega

private theorem eventual_sign (e : ℕ → ℕ) (C : ℕ) (h : ∀ N, SmallFibers e N)
    (step : ∀ n, e n ≤ e (n + 1) ∧ e (n + 1) ≤ e n + C)
    (p q : ℤ) (hq : 0 < q) :
    (∀ᶠ n in atTop, 0 < drift e p q n) ∨ (∀ᶠ n in atTop, drift e p q n < 0) := by
  let B : ℤ := q * C + |p|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hstep (n : ℕ) : |drift e p q (n + 1) - drift e p q n| ≤ B := by
    have h₁ : (e n : ℤ) ≤ e (n + 1) := by exact_mod_cast (step n).1
    have h₂ : (e (n + 1) : ℤ) ≤ e n + C := by exact_mod_cast (step n).2
    have hdiff : |(e (n + 1) : ℤ) - e n| ≤ C := abs_le.mpr (by constructor <;> omega)
    have hid : drift e p q (n + 1) - drift e p q n =
        q * ((e (n + 1) : ℤ) - e n) + (-p) := by
      simp only [drift, Nat.cast_add, Nat.cast_one]
      ring
    calc
      _ = _ := congrArg abs hid
      _ ≤ |q * ((e (n + 1) : ℤ) - e n)| + |(-p)| := abs_add_le _ _
      _ ≤ B := by
        rw [abs_mul, abs_of_pos hq, abs_neg]
        exact add_le_add (mul_le_mul_of_nonneg_left hdiff hq.le) le_rfl
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eventually_outside e h p q B hq)
  have hfar (n : ℕ) (hn : M ≤ n) : drift e p q n < -B ∨ B < drift e p q n := by
    have hh := hM n hn
    rw [Finset.mem_Icc] at hh
    omega
  rcases hfar M le_rfl with hm | hm
  · right
    refine eventually_atTop.2 ⟨M, fun n hn => ?_⟩
    suffices drift e p q n < -B by omega
    induction n, hn using Nat.le_induction with
    | base => exact hm
    | succ n hn ih =>
        rcases hfar (n + 1) (by omega) with hnext | hnext
        · exact hnext
        · have hs := (abs_le.mp (hstep n)).2
          omega
  · left
    refine eventually_atTop.2 ⟨M, fun n hn => ?_⟩
    suffices B < drift e p q n by omega
    induction n, hn using Nat.le_induction with
    | base => exact hm
    | succ n hn ih =>
        rcases hfar (n + 1) (by omega) with hnext | hnext
        · have hs := (abs_le.mp (hstep n)).1
          omega
        · exact hnext

private theorem slope_comparison (e : ℕ → ℕ) (C : ℕ) (h : ∀ N, SmallFibers e N)
    (step : ∀ n, e n ≤ e (n + 1) ∧ e (n + 1) ≤ e n + C) (r : ℚ) :
    (∀ᶠ n : ℕ in atTop, (r : ℝ) < (e n : ℝ) / n) ∨
    (∀ᶠ n : ℕ in atTop, (e n : ℝ) / n < (r : ℝ)) := by
  have hq : 0 < (r.den : ℤ) := by exact_mod_cast r.den_pos
  have hqr : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  rcases eventual_sign e C h step r.num r.den hq with hpos | hneg
  · left
    filter_upwards [hpos, eventually_ge_atTop (1 : ℕ)] with n hp hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hp' : (0 : ℝ) < (r.den : ℝ) * e n - (r.num : ℝ) * n := by
      exact_mod_cast hp
    rw [Rat.cast_def]
    apply (lt_div_iff₀ hnr).2
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hqr).2
    calc
      (r.num : ℝ) * n < r.den * (e n : ℝ) := by linarith
      _ = (e n : ℝ) * r.den := mul_comm _ _
  · right
    filter_upwards [hneg, eventually_ge_atTop (1 : ℕ)] with n hp hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hp' : (r.den : ℝ) * e n - (r.num : ℝ) * n < 0 := by
      exact_mod_cast hp
    rw [Rat.cast_def]
    apply (div_lt_iff₀ hnr).2
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ hqr).2
    calc
      (e n : ℝ) * r.den = r.den * (e n : ℝ) := mul_comm _ _
      _ < (r.num : ℝ) * n := by linarith

private theorem slope_tendsto (e : ℕ → ℕ) (C : ℕ) (h : ∀ N, SmallFibers e N)
    (he : e 0 = 0) (step : ∀ n, e n ≤ e (n + 1) ∧ e (n + 1) ≤ e n + C) :
    ∃ a : ℝ, Tendsto (fun n : ℕ => (e n : ℝ) / n) atTop (𝓝 a) := by
  let f : ℕ → ℝ := fun n => (e n : ℝ) / n
  let L : Set ℝ := {r | ∀ᶠ n in atTop, r ≤ f n}
  have hnon : L.Nonempty := ⟨0, Eventually.of_forall fun n => by dsimp [f]; positivity⟩
  have hbound (n : ℕ) : e n ≤ C * n := by
    induction n with
    | zero => simp [he]
    | succ n ih => simpa [Nat.mul_succ] using (step n).2.trans (Nat.add_le_add_right ih C)
  have hb : BddAbove L := by
    refine ⟨C, fun r hr => ?_⟩
    have hevent : ∀ᶠ n in atTop, r ≤ f n := hr
    obtain ⟨n, hn, hpos⟩ := (hevent.and (eventually_ge_atTop (1 : ℕ))).exists
    refine hn.trans ((div_le_iff₀ ?_).2 ?_)
    · exact_mod_cast (show 0 < n by omega)
    · exact_mod_cast hbound n
  let a := sSup L
  refine ⟨a, tendsto_order.2 ⟨?_, ?_⟩⟩
  · intro b hb'
    obtain ⟨r, hr, hrr⟩ := exists_lt_of_lt_csSup hnon hb'
    have hevent : ∀ᶠ n in atTop, r ≤ f n := hr
    exact hevent.mono fun _ hn => hrr.trans_le hn
  · intro b hb'
    obtain ⟨r, hleft, hright⟩ := exists_rat_btwn hb'
    rcases slope_comparison e C h step r with hr | hr
    · have hm : (r : ℝ) ∈ L := hr.mono fun _ hn => hn.le
      exact False.elim ((not_lt_of_ge (le_csSup hb hm)) hleft)
    · exact hr.mono fun _ hn => hn.trans hright

private theorem no_infinite_small_fibers (e : ℕ → ℕ) (C : ℕ) (he : e 0 = 0)
    (step : ∀ n, e n ≤ e (n + 1) ∧ e (n + 1) ≤ e n + C) :
    ¬ ∀ N, SmallFibers e N := by
  intro h
  obtain ⟨a, ha⟩ := slope_tendsto e C h he step
  obtain ⟨p, q, hq, _, happ⟩ := Real.exists_int_int_abs_mul_sub_le a (n := 39) (by decide)
  have happ' : |(q : ℝ) * a - p| ≤ 1 / 40 := by norm_num at happ ⊢; exact happ
  have hlim : Tendsto (fun n : ℕ => (q : ℝ) * ((e n : ℝ) / n) - p) atTop
      (𝓝 ((q : ℝ) * a - p)) := (tendsto_const_nhds.mul ha).sub tendsto_const_nhds
  have hsmall : ∀ᶠ n : ℕ in atTop, |(q : ℝ) * ((e n : ℝ) / n) - p| < 1 / 20 :=
    (tendsto_order.1 hlim.abs).2 _ (happ'.trans_lt (by norm_num))
  obtain ⟨M, hM⟩ := eventually_atTop.1 hsmall
  let n := 20 * (M + 1)
  let s := Finset.Icc (M + 1) n
  let t := Finset.Icc (-(M + 1 : ℤ)) (M + 1 : ℤ)
  have hmap : ∀ i ∈ s, drift e p q i ∈ t := by
    intro i hi
    have ⟨hi₁, hi₂⟩ := Finset.mem_Icc.mp hi
    have hip : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
    have hsub := hM i (by omega)
    have hdiv : (q : ℝ) * ((e i : ℝ) / i) - p =
        ((q : ℝ) * e i - (p : ℝ) * i) / i := by
      rw [← mul_div_assoc, sub_div, mul_div_cancel_right₀ _ (ne_of_gt hip)]
    rw [hdiv, abs_div, abs_of_pos hip, div_lt_iff₀ hip] at hsub
    have hi₂' : (i : ℝ) ≤ 20 * ((M : ℝ) + 1) := by
      exact_mod_cast hi₂
    have ht' : |(q : ℝ) * e i - (p : ℝ) * i| ≤ (M : ℝ) + 1 := by linarith
    have ht : |drift e p q i| ≤ (M + 1 : ℤ) := by
      exact_mod_cast ht'
    exact Finset.mem_Icc.mpr (abs_le.mp ht)
  have hc := Finset.card_le_mul_card_image_of_maps_to hmap 5 (fun z _ =>
    fiber_card_le e h s p q z hq)
  simp only [s, t, Nat.card_Icc, Int.card_Icc] at hc
  dsimp [n] at hc
  omega

private def path {C : ℕ} (a : ℕ → Fin (C + 1)) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, (a i : ℕ)

private theorem smallFibers_congr {e f : ℕ → ℕ} {N : ℕ}
    (h : ∀ n ≤ N, e n = f n) : SmallFibers e N ↔ SmallFibers f N := by
  have eq (p q z : ℤ) :
      ((Finset.range (N + 1)).filter fun n => drift e p q n = z) =
      ((Finset.range (N + 1)).filter fun n => drift f p q n = z) := by
    apply Finset.filter_congr
    intro n hn
    have hn' : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [drift, drift, h n hn']
  constructor
  · intro he p q z hq
    rw [← eq]
    exact he p q z hq
  · intro hf p q z hq
    rw [eq]
    exact hf p q z hq

private theorem finite_walk (C : ℕ) :
    ∃ N, ∀ e : ℕ → ℕ, (∀ i < N, e i ≤ e (i + 1) ∧ e (i + 1) ≤ e i + C) →
      ¬ SmallFibers e N := by
  by_contra hn
  let A (N : ℕ) : Set (ℕ → Fin (C + 1)) := {a | SmallFibers (path a) N}
  have hclosed (N : ℕ) : IsClosed (A N) := by
    let slice (a : ℕ → Fin (C + 1)) (i : Fin (N + 1)) : ℕ := path a i
    have hc : Continuous slice := by
      apply continuous_pi
      intro i
      refine continuous_finsetSum (Finset.range (i : ℕ)) fun m _ => ?_
      exact (continuous_of_discreteTopology (f := fun b : Fin (C + 1) => (b : ℕ))).comp
        (continuous_apply m)
    let B : Set (Fin (N + 1) → ℕ) :=
      {r | SmallFibers (fun n => if h : n < N + 1 then r ⟨n, h⟩ else 0) N}
    have heq : A N = slice ⁻¹' B := by
      ext a
      apply smallFibers_congr
      intro n hn'
      dsimp [slice]
      rw [ite_eq_left (Nat.lt_succ_of_le hn')]
    rw [heq]
    exact (isClosed_discrete B).preimage hc
  have hdir : Directed (fun s t : Set (ℕ → Fin (C + 1)) => s ⊇ t) A := by
    have hm : ∀ i j, i ≤ j → A j ⊆ A i := by
      intro i j hij a hj p q z hq
      exact (Finset.card_le_card (Finset.filter_subset_filter _
        (Finset.range_mono (by omega)))).trans (hj p q z hq)
    intro i j
    exact ⟨max i j, hm _ _ (le_max_left _ _), hm _ _ (le_max_right _ _)⟩
  have hnon (N : ℕ) : (A N).Nonempty := by
    have hb : ∃ e : ℕ → ℕ, (∀ i < N, e i ≤ e (i + 1) ∧ e (i + 1) ≤ e i + C) ∧
        SmallFibers e N := by
      by_contra! h
      exact hn ⟨N, h⟩
    obtain ⟨e, he, he'⟩ := hb
    let a (n : ℕ) : Fin (C + 1) := ⟨min C (e (n + 1) - e n), by omega⟩
    have hpath (i : ℕ) (hi : i ≤ N) : path a i + e 0 = e i := by
      induction i with
      | zero => simp [path]
      | succ i ih =>
          have hi' : i < N := by omega
          have ⟨hl, hu⟩ := he i hi'
          have hd : e (i + 1) - e i ≤ C := by omega
          have ih' := ih (by omega)
          simp only [path, Finset.sum_range_succ] at ih' ⊢
          change (∑ j ∈ Finset.range i, (a j : ℕ)) +
            min C (e (i + 1) - e i) + e 0 = e (i + 1)
          rw [min_eq_right hd]
          omega
    refine ⟨a, fun p q z hq => ?_⟩
    refine (Finset.card_le_card (t := (Finset.range (N + 1)).filter
        fun n => drift e p q n = z + q * (e 0 : ℤ)) ?_).trans (he' p q _ hq)
    intro n hmem
    rw [Finset.mem_filter] at hmem ⊢
    refine ⟨hmem.1, ?_⟩
    have hn' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem.1)
    have hp : (path a n : ℤ) + e 0 = e n := by exact_mod_cast hpath n hn'
    unfold drift at hmem ⊢
    rw [← hp, mul_add]
    omega
  obtain ⟨a, ha⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      A hdir hnon (fun N => (hclosed N).isCompact) hclosed
  refine no_infinite_small_fibers (path a) C (by simp [path]) (fun i => ?_)
    (fun N => Set.mem_iInter.mp ha N)
  rw [path, path, Finset.sum_range_succ]
  have hle : (a i : ℕ) ≤ C := by omega
  constructor <;> omega

/-- For a bounded-increment integer graph, six vertices lie on an affine rational line.
The bound on the length of the path depends only on the bound on its increments. -/
theorem planarWalk : Erdos782Reduction.PlanarWalkTheorem := by
  intro C
  obtain ⟨N, hN⟩ := finite_walk C
  refine ⟨N, fun e he => ?_⟩
  have notSmall := hN e he
  unfold SmallFibers at notSmall
  push Not at notSmall
  obtain ⟨p, q, z, hq, hcard⟩ := notSmall
  let s := (Finset.range (N + 1)).filter fun n => drift e p q n = z
  have hc : 6 ≤ s.card := Nat.succ_le_of_lt hcard
  let j : Fin 6 → ℕ := fun v => s.orderEmbOfFin rfl (Fin.castLE hc v)
  have hinj : Function.Injective j :=
    (s.orderEmbOfFin rfl).injective.comp (Fin.castLEEmb hc).injective
  have hj (v : Fin 6) : j v ∈ s := by
    exact Finset.orderEmbOfFin_mem _ _ _
  have nonempty : s.Nonempty := ⟨j 0, hj 0⟩
  let b := s.min' nonempty
  have hb : b ∈ s := Finset.min'_mem _ _
  have hl (n : ℕ) (hn : n ∈ s) : b ≤ n := Finset.min'_le _ _ hn
  have hu (n : ℕ) (hn : n ∈ s) : n ≤ N := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)
  have hz (n : ℕ) (hn : n ∈ s) : drift e p q n = z := (Finset.mem_filter.mp hn).2
  let a : ℚ := (p : ℚ) / q
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  let h (v : Fin 6) : Fin (N + 1) := ⟨j v - b, by have := hu _ (hj v); omega⟩
  have ho (v : Fin 6) : b + (h v).val = j v := by
    have := hl _ (hj v)
    dsimp [h]
    omega
  have hline (v : Fin 6) : (e (j v) : ℚ) = e b + a * (h v).val := by
    have hez : (q : ℚ) * e (j v) - (p : ℚ) * (j v : ℚ) =
        (q : ℚ) * e b - (p : ℚ) * (b : ℚ) := by
      exact_mod_cast (hz _ (hj v)).trans (hz _ hb).symm
    dsimp [a, h]
    rw [Nat.cast_sub (hl _ (hj v))]
    field_simp [hq'.ne']
    linear_combination hez
  have hdiff (i n : ℕ) (hin : i ≤ n) (hn : n ≤ N) :
      e i ≤ e n ∧ e n ≤ e i + C * (n - i) := by
    induction n, hin using Nat.le_induction with
    | base => simp
    | succ n hin ih =>
        have ih' := ih (by omega)
        have hs := he n (by omega)
        have hsub : n + 1 - i = (n - i) + 1 := by omega
        rw [hsub, Nat.mul_add, Nat.mul_one]
        omega
  have hpositive : ∃ v, 0 < (h v).val := by
    by_contra! hy
    have h0 := ho 0
    have h1 := ho 1
    have hv0 := hy 0
    have hv1 := hy 1
    have hcontra : (0 : Fin 6) = 1 := hinj (by omega)
    exact (by decide : (0 : Fin 6) ≠ 1) hcontra
  obtain ⟨v, hv⟩ := hpositive
  have hp : (0 : ℚ) < (h v).val := by exact_mod_cast hv
  have ⟨hd₁, hd₂⟩ := hdiff b (j v) (hl _ (hj v)) (hu _ (hj v))
  have hd₁' : (e b : ℚ) ≤ e (j v) := by exact_mod_cast hd₁
  have hd₂' : (e (j v) : ℚ) ≤ e b + (C : ℚ) * (h v).val := by exact_mod_cast hd₂
  rw [hline] at hd₁' hd₂'
  have ha₁ : 0 ≤ a := by
    by_contra! han
    have := mul_neg_of_neg_of_pos han hp
    linarith
  have ha₂ : a ≤ C := by
    by_contra! han
    have := mul_lt_mul_of_pos_right han hp
    linarith
  refine ⟨b, h, a, hu _ hb, ?_, ha₁, ha₂, fun w => ?_⟩
  · intro y w hEq
    apply hinj
    rw [← ho y, ← ho w, hEq]
  · rw [ho]
    exact ⟨hu _ (hj w), hline w⟩

end Erdos782Walk
