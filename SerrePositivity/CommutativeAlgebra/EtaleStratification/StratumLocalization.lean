module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.FactorizationLocalization
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Ideal

/-!
# 層の主開集合による細分

## 概要
層でさらに h を反転する操作は、元の基底で g h を反転する層と同型。

## 方針
二段階の主局所化の標準同型と、元の環の像上の可換性を使う。

## 規約
閉集合を定めるイデアルは固定し、開集合の元だけを変える。

## 使われ方
p 可逆な部分への細分。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

/-- 被約閉集合の主開層は被約。 -/
theorem isReduced_stratumRing {R : Type u} [CommRing R] (I : Ideal R) (g : R) :
    IsReduced (StratumRing I g) := by
  let : IsReduced (R ⧸ I.radical) :=
    (Ideal.isRadical_iff_quotient_reduced I.radical).mp (Ideal.radical_isRadical I)
  apply nilradical_eq_bot_iff.mp
  have h := IsLocalization.map_radical
    (Submonoid.powers (Ideal.Quotient.mk I.radical g)) (StratumRing I g)
      (⊥ : Ideal (R ⧸ I.radical))
  have hr : (⊥ : Ideal (R ⧸ I.radical)).radical = ⊥ := nilradical_eq_zero _
  change (⊥ : Ideal (StratumRing I g)).radical = ⊥
  simpa only [hr, Ideal.map_bot] using h.symm

/-- 二段階の主局所化は積の主局所化。 -/
theorem isLocalization_stratum_mul {R : Type u} [CommRing R] (I : Ideal R) (g h : R) :
    IsLocalization.Away (Ideal.Quotient.mk I.radical (g * h))
      (Localization.Away (stratumUnit I g h)) := by
  let T := Localization.Away (stratumUnit I g h)
  let : IsLocalization.Away
      (algebraMap (R ⧸ I.radical) (StratumRing I g) (Ideal.Quotient.mk I.radical h)) T :=
    inferInstanceAs (IsLocalization.Away (stratumUnit I g h) T)
  rw [map_mul]
  exact IsLocalization.Away.mul' (StratumRing I g) T
    (Ideal.Quotient.mk I.radical g) (Ideal.Quotient.mk I.radical h)

/-- g h の層と、g の層でさらに h を反転した環の標準同型。 -/
def stratumLocalizationEquiv {R : Type u} [CommRing R] (I : Ideal R) (g h : R) :
    StratumRing I (g * h) ≃+* Localization.Away (stratumUnit I g h) := by
  letI := isLocalization_stratum_mul I g h
  exact (IsLocalization.algEquiv
    (Submonoid.powers (Ideal.Quotient.mk I.radical (g * h))) (StratumRing I (g * h))
      (Localization.Away (stratumUnit I g h))).toRingEquiv

@[simp]
theorem stratumLocalizationEquiv_unit {R : Type u} [CommRing R] (I : Ideal R) (g h x : R) :
    stratumLocalizationEquiv I g h (stratumUnit I (g * h) x) =
      algebraMap (StratumRing I g) (Localization.Away (stratumUnit I g h)) (stratumUnit I g x) := by
  letI := isLocalization_stratum_mul I g h
  change stratumLocalizationEquiv I g h
    (algebraMap (R ⧸ I.radical) _ (Ideal.Quotient.mk I.radical x)) = _
  exact (IsLocalization.algEquiv _ _ _).commutes _

/-- 目標側の二段階局所化にも、元の環からの局所化構造を入れる。 -/
theorem isLocalization_stratum_target_mul {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (g h : R) :
    IsLocalization.Away (Ideal.Quotient.mk (I.map f).radical (f (g * h)))
      (Localization.Away (stratumMap f I g (stratumUnit I g h))) := by
  let T := Localization.Away (stratumMap f I g (stratumUnit I g h))
  let : IsLocalization.Away
      (algebraMap (S ⧸ (I.map f).radical) (StratumRing (I.map f) (f g))
        (Ideal.Quotient.mk (I.map f).radical (f h))) T := by
    change IsLocalization.Away (stratumUnit (I.map f) (f g) (f h)) T
    rw [← stratumMap_unit f I g h]
    infer_instance
  rw [map_mul, map_mul]
  exact IsLocalization.Away.mul' (StratumRing (I.map f) (f g)) T
    (Ideal.Quotient.mk (I.map f).radical (f g))
    (Ideal.Quotient.mk (I.map f).radical (f h))

/-- 元の射の目標側で、二段階の主局所化の標準同型。 -/
def stratumLocalizationTargetEquiv {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (g h : R) :
    StratumRing (I.map f) (f (g * h)) ≃+*
      Localization.Away (stratumMap f I g (stratumUnit I g h)) := by
  letI := isLocalization_stratum_target_mul f I g h
  exact (IsLocalization.algEquiv
    (Submonoid.powers (Ideal.Quotient.mk (I.map f).radical (f (g * h))))
    (StratumRing (I.map f) (f (g * h)))
    (Localization.Away (stratumMap f I g (stratumUnit I g h)))).toRingEquiv

@[simp]
theorem stratumLocalizationTargetEquiv_unit {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (g h : R) (y : S) :
    stratumLocalizationTargetEquiv f I g h (stratumUnit (I.map f) (f (g * h)) y) =
      algebraMap (StratumRing (I.map f) (f g))
        (Localization.Away (stratumMap f I g (stratumUnit I g h)))
          (stratumUnit (I.map f) (f g) y) := by
  letI := isLocalization_stratum_target_mul f I g h
  exact (IsLocalization.algEquiv _ _ _).commutes (Ideal.Quotient.mk (I.map f).radical y)

/-- 層の有限エタール分解は、開集合の元を積に替える細分で保たれる。 -/
theorem hasEtaleFactorization_stratum_mul {R S : Type u} [CommRing R] [CommRing S]
    (p : ℕ) (f : R →+* S) (I : Ideal R) (g h : R)
    (hf : HasEtaleFactorization p (stratumMap f I g)) :
    HasEtaleFactorization p (stratumMap f I (g * h)) := by
  let : IsReduced (StratumRing I g) := isReduced_stratumRing I g
  have hloc := hasEtaleFactorization_awayMap p (stratumMap f I g) (stratumUnit I g h) hf
  have ht := hasEtaleFactorization_transport p (stratumLocalizationEquiv I g h).symm
    (stratumLocalizationTargetEquiv f I g h).symm _ hloc
  have he : ((stratumLocalizationTargetEquiv f I g h).symm.toRingHom.comp
      (Localization.awayMap (stratumMap f I g) (stratumUnit I g h))).comp
        (stratumLocalizationEquiv I g h).toRingHom = stratumMap f I (g * h) := by
    apply stratumRing_hom_ext I (g * h)
    intro x
    apply (stratumLocalizationTargetEquiv f I g h).injective
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply,
      stratumLocalizationEquiv_unit, stratumLocalizationTargetEquiv_unit, stratumMap_unit,
      Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  simpa only [RingEquiv.symm_symm, he] using ht

end SerrePositivity.CommutativeAlgebra
