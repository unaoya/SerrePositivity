module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.Factorization
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.ReducedEtale
public import SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.PrincipalOpen
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# 有限エタール分解の主開集合への制限

## 概要
被約基底上の有限エタール・普遍同相分解は、主局所化に沿って保たれる。

## 方針
中間代数を局所化し、有限エタール性の底変換、普遍同相の局所化を使う。
p 反転後の同型は、二つの主局所化の分母を合わせて移す。

## 規約
被約性により有限エタール中間代数も被約となり、後半の普遍同相は単射になる。

## 使われ方
p 可逆な開集合への細分と、選んだ主開集合をさらに小さくする操作。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

/-- 被約基底上の分解は、主開集合への制限で保たれる。 -/
theorem hasEtaleFactorization_awayMap {A B : Type u} [CommRing A] [CommRing B]
    [IsReduced A] (p : ℕ) (f : A →+* B) (g : A) (hf : HasEtaleFactorization p f) :
    HasEtaleFactorization p (Localization.awayMap f g) := by
  obtain ⟨T, a, b, hab, hfin, het, hu, hp⟩ := hf
  let : Algebra A T := a.toAlgebra
  let : Module.Finite A T := hfin
  let : Algebra.Etale A T := het
  let : IsReduced T := isReduced_of_finite_etale A T
  have hbinj : Function.Injective b := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply bot_unique
    have hnil := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical b).mp hu.surjective_spec.denseRange
    simpa only [nilradical_eq_zero] using hnil
  let A' := Localization.Away g
  let T' := Localization.Away (a g)
  let B' := Localization.Away (f g)
  let a' : A' →+* T' := Localization.awayMap a g
  let : Algebra A' T' := a'.toAlgebra
  let : IsScalarTower A A' T' := IsScalarTower.of_algebraMap_eq fun x ↦
    (IsLocalization.map_eq _ _ _ x).symm
  let : Module.Finite A' T' := Module.Finite.of_isLocalizedModule
    (Submonoid.powers g) (IsScalarTower.toAlgHom A T T').toLinearMap
  let : Algebra.IsPushout A T A' T' :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers g) A' T T'
  have het' : a'.Etale := RingHom.Etale.isStableUnderBaseChange A T A' T' het
  let : IsLocalization.Away (b (a g)) B' := by
    rw [show b (a g) = f g from RingHom.congr_fun hab g]
    infer_instance
  let e := IsLocalization.algEquiv (Submonoid.powers (b (a g)))
    (Localization.Away (b (a g))) B'
  let b' : T' →+* B' := e.toRingHom.comp (Localization.awayMap b (a g))
  refine ⟨CommRingCat.of T', a', b', ?_, inferInstance, het', ?_, ?_⟩
  · apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext x
    simp only [RingHom.comp_apply, a', b', Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq, AlgEquiv.commutes]
    rw [RingHom.congr_fun hab x]
  · exact isUniversalHomeomorphism_comp _ _ (isUniversalHomeomorphism_awayMap b (a g) hu)
      (isUniversalHomeomorphism_of_bijective e.toRingHom e.bijective)
  · change Function.Bijective (invertPrimeMap p
      (e.toRingHom.comp (Localization.awayMap b (a g))))
    rw [invertPrimeMap_comp]
    apply (invertPrimeMap_bijective p e.toRingHom e.bijective).comp
    apply invertPrimeMap_awayMap_bijective p b (a g) hbinj
    apply Localization.awayMap_surjective_of_dvd b (dvd_mul_left (p : T) (a g))
    apply Localization.awayMap_surjective_iff.mpr
    simpa only [map_natCast] using (invertPrimeMap_surjective_iff p b).mp hp.surjective

end SerrePositivity.CommutativeAlgebra
