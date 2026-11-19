module

public import PlaceBridge
public import TauCeti.FieldTheory.FunctionField.Repartition.IndexOfSpecialty

@[expose] public section

open Filter

namespace Erdos782Arithmetic

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F]

theorem mem_placeEquiv_symm_integers (hF : TauCeti.IsFunctionField k F)
    (P : Faltings.Place k F) (x : F) :
    x ∈ ((placeEquiv hF).symm P).integers ↔ x ∈ P.toSubalgebra := by
  rw [← toFaltingsPlace_mem]
  rw [← placeEquiv_apply hF, Equiv.apply_symm_apply]

/-- Reindex Tau Ceti's repartition space by the corresponding Mordell places. -/
noncomputable def repartitionEquiv (hF : TauCeti.IsFunctionField k F) :
    (↥(TauCeti.repartitionSpace k F)) ≃ₗ[k] Faltings.Adele k F := by
  let e := placeEquiv hF
  let toAdele (a : ↥(TauCeti.repartitionSpace k F)) : Faltings.Adele k F := by
    refine RestrictedProduct.mk (fun P => a.1 (e.symm P)) ?_
    change ∀ᶠ P in Filter.cofinite, a.1 (e.symm P) ∈ P.toSubalgebra
    rw [Filter.eventually_cofinite]
    have hf := Filter.eventually_cofinite.mp (TauCeti.mem_repartitionSpace_iff_integers.mp a.2)
    refine (hf.preimage e.symm.injective.injOn).subset fun P hP ha => ?_
    exact hP ((mem_placeEquiv_symm_integers hF P _).mp ha)
  let toRepartition (b : Faltings.Adele k F) : ↥(TauCeti.repartitionSpace k F) := by
    refine ⟨fun P => b (e P), ?_⟩
    apply TauCeti.mem_repartitionSpace_iff_integers.mpr
    rw [Filter.eventually_cofinite]
    have hf := Filter.eventually_cofinite.mp (RestrictedProduct.eventually _ _ b)
    refine (hf.preimage e.injective.injOn).subset fun P hP hb => ?_
    apply hP
    have hm : b (e P) ∈ (placeEquiv hF P).toSubalgebra := hb
    rw [placeEquiv_apply, toFaltingsPlace_mem] at hm
    exact hm
  refine
    { toFun := toAdele
      invFun := toRepartition
      left_inv := fun a => Subtype.ext (funext fun P => by
        change a.1 (e.symm (e P)) = a.1 P
        rw [Equiv.symm_apply_apply])
      right_inv := fun b => RestrictedProduct.ext _ _ fun P => by
        change b (e (e.symm P)) = b P
        rw [Equiv.apply_symm_apply]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp]
theorem repartitionEquiv_apply (hF : TauCeti.IsFunctionField k F)
    (a : ↥(TauCeti.repartitionSpace k F)) (P : Faltings.Place k F) :
    repartitionEquiv hF a P = a.1 ((placeEquiv hF).symm P) := rfl

private theorem mem_integral_iff (hF : TauCeti.IsFunctionField k F)
    (a : ↥(TauCeti.repartitionSpace k F)) :
    repartitionEquiv hF a ∈ Faltings.Adele.integral k F ↔
      a ∈ (TauCeti.adeleFiltration (0 : TauCeti.Divisor k F)).submoduleOf
        (TauCeti.repartitionSpace k F) := by
  rw [Faltings.Adele.mem_integral]
  change (∀ P, repartitionEquiv hF a P ∈ P.toSubalgebra) ↔
    a.1 ∈ TauCeti.adeleFiltration (0 : TauCeti.Divisor k F)
  rw [TauCeti.mem_adeleFiltration_zero_iff]
  constructor
  · intro ha Q
    have h := ha (placeEquiv hF Q)
    rw [repartitionEquiv_apply, Equiv.symm_apply_apply, placeEquiv_apply] at h
    exact (toFaltingsPlace_mem Q _).mp h
  · intro ha P
    rw [repartitionEquiv_apply]
    exact (mem_placeEquiv_symm_integers hF P _).mp (ha ((placeEquiv hF).symm P))

private theorem mem_principal_iff (hF : TauCeti.IsFunctionField k F)
    (a : ↥(TauCeti.repartitionSpace k F)) :
    repartitionEquiv hF a ∈ Faltings.Adele.principal k F ↔
      a ∈ (TauCeti.diagonalRepartitions k F).submoduleOf (TauCeti.repartitionSpace k F) := by
  rw [Faltings.Adele.mem_principal]
  change (∀ P Q, repartitionEquiv hF a P = repartitionEquiv hF a Q) ↔
    a.1 ∈ TauCeti.diagonalRepartitions k F
  rw [TauCeti.mem_diagonalRepartitions_iff]
  constructor
  · intro h
    cases isEmpty_or_nonempty (TauCeti.Place k F) with
    | inl hi => exact ⟨0, funext fun P => isEmptyElim P⟩
    | inr hn =>
        obtain ⟨P⟩ := hn
        refine ⟨a.1 P, funext fun Q => ?_⟩
        simpa using h (placeEquiv hF P) (placeEquiv hF Q)
  · rintro ⟨f, hf⟩ P Q
    simp only [repartitionEquiv_apply, ← hf, Function.const_apply]

private theorem map_eq_of_equiv_mem {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module k V] [Module k W] (e : V ≃ₗ[k] W) (U : Submodule k V) (T : Submodule k W)
    (hs : ∀ x, e x ∈ T ↔ x ∈ U) : U.map e.toLinearMap = T := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext x
  change e.symm x ∈ U ↔ x ∈ T
  simpa using (hs (e.symm x)).symm


/-- Tau Ceti's Riemann–Roch genus agrees with the genus used in the Mordell theorem. -/
theorem genus_eq (hF : TauCeti.IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) :
    Faltings.genus k F = TauCeti.genus k F := by
  let R := TauCeti.repartitionSpace k F
  let S := TauCeti.adeleFiltration (0 : TauCeti.Divisor k F)
  let T := TauCeti.diagonalRepartitions k F
  let e := repartitionEquiv hF
  have hi : (S.submoduleOf R).map e.toLinearMap = Faltings.Adele.integral k F :=
    map_eq_of_equiv_mem e _ _ (mem_integral_iff hF)
  have hp : (T.submoduleOf R).map e.toLinearMap = Faltings.Adele.principal k F :=
    map_eq_of_equiv_mem e _ _ (mem_principal_iff hF)
  have hmap : ((S ⊔ T).submoduleOf R).map e.toLinearMap =
      Faltings.Adele.integral k F ⊔ Faltings.Adele.principal k F := by
    rw [Submodule.submoduleOf_sup_of_le (TauCeti.adeleFiltration_le_repartitionSpace _)
      (TauCeti.diagonalRepartitions_le_repartitionSpace hF), Submodule.map_sup, hi, hp]
  unfold Faltings.genus
  rw [← TauCeti.finrank_quotient_repartitionSpace_zero hF hex]
  exact (Submodule.Quotient.equiv _ _ e hmap).finrank_eq.symm

end Erdos782Arithmetic
