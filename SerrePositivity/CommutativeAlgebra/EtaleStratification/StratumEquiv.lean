module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.StratumLift

/-!
# 代数同型による層の移送

## 概要
基底上の代数同型は、対応する被約主開層の標準同型を誘導する。

## 方針
代数同型と逆写像を被約層の普遍性で延ばす。

## 規約
基底のイデアルと開集合の元は固定する。

## 使われ方
Noetherian 近似の底変換同型を使って、元の代数へ層別を移す。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

/-- 代数同型は対応する層の同型を誘導し、層の射と可換。 -/
theorem exists_stratum_target_equiv
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (I : Ideal R) (g : R) :
    ∃ E : StratumRing (I.map (algebraMap R A)) (algebraMap R A g) ≃+*
        StratumRing (I.map (algebraMap R B)) (algebraMap R B g),
      E.toRingHom.comp (stratumMap (algebraMap R A) I g) = stratumMap (algebraMap R B) I g := by
  let Iₐ := I.map (algebraMap R A)
  let Iᵦ := I.map (algebraMap R B)
  let A' := StratumRing Iₐ (algebraMap R A g)
  let B' := StratumRing Iᵦ (algebraMap R B g)
  let : IsReduced A' := isReduced_stratumRing _ _
  let : IsReduced B' := isReduced_stratumRing _ _
  let f : A →+* B' := (stratumUnit Iᵦ (algebraMap R B g)).comp e.toRingHom
  let h : B →+* A' := (stratumUnit Iₐ (algebraMap R A g)).comp e.symm.toRingHom
  have hfI : Iₐ ≤ RingHom.ker f := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change stratumUnit Iᵦ (algebraMap R B g) (e (algebraMap R A x)) = 0
    rw [e.commutes]
    exact stratumUnit_ker Iᵦ _ (Ideal.mem_map_of_mem _ hx)
  have hhI : Iᵦ ≤ RingHom.ker h := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change stratumUnit Iₐ (algebraMap R A g) (e.symm (algebraMap R B x)) = 0
    rw [e.symm.commutes]
    exact stratumUnit_ker Iₐ _ (Ideal.mem_map_of_mem _ hx)
  have hfg : IsUnit (f (algebraMap R A g)) := by
    simpa only [f, RingHom.comp_apply, AlgEquiv.commutes] using stratumUnit_isUnit Iᵦ (algebraMap R B g)
  have hhg : IsUnit (h (algebraMap R B g)) := by
    simpa only [h, RingHom.comp_apply, AlgEquiv.commutes] using stratumUnit_isUnit Iₐ (algebraMap R A g)
  let F : A' →+* B' := stratumLift Iₐ (algebraMap R A g) f hfI hfg
  let H : B' →+* A' := stratumLift Iᵦ (algebraMap R B g) h hhI hhg
  have hl : Function.LeftInverse H F := by
    have he : H.comp F = RingHom.id A' := by
      apply stratumRing_hom_ext Iₐ (algebraMap R A g)
      intro x
      simp only [RingHom.comp_apply, F, H, stratumLift_unit, f, h,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgEquiv.symm_apply_apply, RingHom.id_apply]
    exact fun x ↦ RingHom.congr_fun he x
  have hr : Function.RightInverse H F := by
    have he : F.comp H = RingHom.id B' := by
      apply stratumRing_hom_ext Iᵦ (algebraMap R B g)
      intro x
      simp only [RingHom.comp_apply, F, H, stratumLift_unit, f, h,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgEquiv.apply_symm_apply, RingHom.id_apply]
    exact fun x ↦ RingHom.congr_fun he x
  refine ⟨RingEquiv.ofBijective F ⟨hl.injective, hr.surjective⟩, ?_⟩
  apply stratumRing_hom_ext I g
  intro x
  simp only [RingHom.comp_apply, stratumMap_unit]
  change F (stratumUnit Iₐ (algebraMap R A g) (algebraMap R A x)) = _
  rw [F, stratumLift_unit]
  exact congrArg (stratumUnit Iᵦ (algebraMap R B g)) (e.commutes x)

/-- 代数同型で有限エタール分解を持つ層を移す。 -/
theorem hasEtaleFactorization_stratum_of_algEquiv
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (p : ℕ) (e : A ≃ₐ[R] B) (I : Ideal R) (g : R)
    (hf : HasEtaleFactorization p (stratumMap (algebraMap R A) I g)) :
    HasEtaleFactorization p (stratumMap (algebraMap R B) I g) := by
  obtain ⟨E, hE⟩ := exists_stratum_target_equiv e I g
  have ht := hasEtaleFactorization_transport p (RingEquiv.refl (StratumRing I g)) E _ hf
  simpa only [RingEquiv.symm_refl, RingEquiv.toRingHom_refl', RingHom.comp_id, hE] using ht

end SerrePositivity.CommutativeAlgebra
