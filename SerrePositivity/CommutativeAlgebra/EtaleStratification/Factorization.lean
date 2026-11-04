module

public import SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.NilDiagonal
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite

/-!
# 被約主開層と有限エタール分解

## 概要
閉集合の被約構造上の主開層と、その射の有限エタール・普遍同相分解。

## 方針
根基による商を局所化し、指定した環準同型の分解を記述する。

## 規約
p 反転後の同型は、誘導される環準同型の全単射性で表す。

## 使われ方
有限エタール層別の延長・底変換・細分。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

/-- V(I) の被約構造上で g を反転する。R/√I は (R/I)_red の標準表示。 -/
abbrev StratumRing {R : Type u} [CommRing R] (I : Ideal R) (g : R) :=
  Localization.Away (Ideal.Quotient.mk I.radical g)

def stratumUnit {R : Type u} [CommRing R] (I : Ideal R) (g : R) : R →+* StratumRing I g :=
  (algebraMap (R ⧸ I.radical) (StratumRing I g)).comp (Ideal.Quotient.mk I.radical)

/-- 層の局所化では、選んだ元は可逆。 -/
theorem stratumUnit_isUnit {R : Type u} [CommRing R] (I : Ideal R) (g : R) :
    IsUnit (stratumUnit I g g) :=
  IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk I.radical g)

/-- 被約化で消したイデアルの元は層でも零になる。 -/
theorem stratumUnit_eq_zero {R : Type u} [CommRing R] (I : Ideal R) (g x : R)
    (hx : x ∈ I.radical) : stratumUnit I g x = 0 := by
  change algebraMap (R ⧸ I.radical) (StratumRing I g) (Ideal.Quotient.mk I.radical x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- (p g, g) による細分の後半では、g が可逆なので p g = 0 から p = 0。 -/
theorem natCast_eq_zero_stratum_of_mul_mem {R : Type u} [CommRing R]
    (I : Ideal R) (g : R) (p : ℕ) (hpg : (p : R) * g ∈ I.radical) :
    (p : StratumRing I g) = 0 := by
  have he := stratumUnit_eq_zero I g ((p : R) * g) hpg
  rw [map_mul, map_natCast] at he
  exact (stratumUnit_isUnit I g).mul_left_eq_zero.mp he

/-- (p g, g) による細分の前半では p が可逆。 -/
theorem isUnit_natCast_stratum_mul {R : Type u} [CommRing R]
    (I : Ideal R) (g : R) (p : ℕ) : IsUnit (p : StratumRing I ((p : R) * g)) := by
  have hu := stratumUnit_isUnit I ((p : R) * g)
  rw [map_mul, map_natCast] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- S では先に I を延長し、その後に根基を取って局所化する。 -/
def stratumMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (I : Ideal R) (g : R) :
    StratumRing I g →+* StratumRing (I.map f) (f g) := by
  let J := I.map f
  let q : R ⧸ I.radical →+* S ⧸ J.radical := Ideal.quotientMap J.radical f
    (Ideal.map_le_iff_le_comap.mp (Ideal.map_radical_le f))
  exact IsLocalization.Away.lift (Ideal.Quotient.mk I.radical g)
    (g := (algebraMap (S ⧸ J.radical) (StratumRing J (f g))).comp q)
    (IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk J.radical (f g)))

/-- f の p 反転で誘導される射。 -/
def invertPrimeMap {A B : Type u} [CommRing A] [CommRing B] (p : ℕ) (f : A →+* B) :
    Localization.Away (p : A) →+* Localization.Away (p : B) := by
  letI : IsLocalization.Away (f (p : A)) (Localization.Away (p : B)) := by
    rw [map_natCast]; infer_instance
  exact IsLocalization.Away.map _ _ f (p : A)

/-- 指定した射 f 自身を有限エタール射と普遍同相に分解する。 -/
def HasEtaleFactorization {A B : Type u} [CommRing A] [CommRing B] (p : ℕ) (f : A →+* B) : Prop :=
  ∃ (T : CommRingCat.{u}) (a : A →+* T) (b : T →+* B),
    letI : Algebra A T := a.toAlgebra
    b.comp a = f ∧ Module.Finite A T ∧ Algebra.Etale A T ∧ IsUniversalHomeomorphism b ∧
      Function.Bijective (invertPrimeMap p b)

@[simp]
theorem invertPrimeMap_algebraMap {A B : Type u} [CommRing A] [CommRing B]
    (p : ℕ) (f : A →+* B) (x : A) :
    invertPrimeMap p f (algebraMap A (Localization.Away (p : A)) x) =
      algebraMap B (Localization.Away (p : B)) (f x) := by
  exact IsLocalization.map_eq _ _ _ x

@[simp]
theorem invertPrimeMap_id {A : Type u} [CommRing A] (p : ℕ) :
    invertPrimeMap p (RingHom.id A) = RingHom.id (Localization.Away (p : A)) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : A))
  ext x
  simp

theorem invertPrimeMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (p : ℕ) (f : A →+* B) (g : B →+* C) :
    invertPrimeMap p (g.comp f) = (invertPrimeMap p g).comp (invertPrimeMap p f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : A))
  ext x
  simp

/-- 全単射な射は p 反転後も全単射。 -/
theorem invertPrimeMap_bijective {A B : Type u} [CommRing A] [CommRing B]
    (p : ℕ) (f : A →+* B) (hf : Function.Bijective f) :
    Function.Bijective (invertPrimeMap p f) := by
  let e := RingEquiv.ofBijective f hf
  change Function.Bijective (invertPrimeMap p e.toRingHom)
  have hl : Function.LeftInverse (invertPrimeMap p e.symm.toRingHom)
      (invertPrimeMap p e.toRingHom) := by
    intro x
    change ((invertPrimeMap p e.symm.toRingHom).comp (invertPrimeMap p e.toRingHom)) x = x
    rw [← invertPrimeMap_comp, show e.symm.toRingHom.comp e.toRingHom = RingHom.id A from
      RingHom.ext fun x ↦ e.symm_apply_apply x, invertPrimeMap_id]
    rfl
  have hr : Function.RightInverse (invertPrimeMap p e.symm.toRingHom)
      (invertPrimeMap p e.toRingHom) := by
    intro x
    change ((invertPrimeMap p e.toRingHom).comp (invertPrimeMap p e.symm.toRingHom)) x = x
    rw [← invertPrimeMap_comp, show e.toRingHom.comp e.symm.toRingHom = RingHom.id B from
      RingHom.ext fun x ↦ e.apply_symm_apply x, invertPrimeMap_id]
    rfl
  exact ⟨hl.injective, hr.surjective⟩

/-- p 反転後の全射性は、各元の p 冪倍が像に入ることと同値。 -/
theorem invertPrimeMap_surjective_iff {A B : Type u} [CommRing A] [CommRing B]
    (p : ℕ) (f : A →+* B) :
    Function.Surjective (invertPrimeMap p f) ↔
      ∀ y : B, ∃ x : A, ∃ n : ℕ, f x = (p : B) ^ n * y := by
  let : IsLocalization.Away (f (p : A)) (Localization.Away (p : B)) := by
    rw [map_natCast]
    infer_instance
  simpa only [map_natCast] using
    (IsLocalization.Away.map_surjective_iff
      (Localization.Away (p : A)) (Localization.Away (p : B)) f (p : A))

/-- 単射は p 反転後も単射。 -/
theorem invertPrimeMap_injective {A B : Type u} [CommRing A] [CommRing B]
    (p : ℕ) (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (invertPrimeMap p f) := by
  let : IsLocalization ((Submonoid.powers (p : A)).map f) (Localization.Away (p : B)) := by
    rw [Submonoid.map_powers, map_natCast]
    infer_instance
  exact IsLocalization.map_injective_of_injective _ _ _ hf

/-- g p の反転後に全射な単射は、g の反転後に p を反転して同型。 -/
theorem invertPrimeMap_awayMap_bijective {A B : Type u} [CommRing A] [CommRing B]
    (p : ℕ) (f : A →+* B) (g : A) (hf : Function.Injective f)
    (hs : Function.Surjective (Localization.awayMap f (g * p))) :
    Function.Bijective (invertPrimeMap p (Localization.awayMap f g)) := by
  refine ⟨invertPrimeMap_injective p _ ?_, ?_⟩
  · exact IsLocalization.map_injective_of_injective _ _ _ hf
  · apply (invertPrimeMap_surjective_iff p _).mpr
    have h := Localization.awayMap_awayMap_surjective f g (p : A) hs
    rw [Localization.awayMap_surjective_iff] at h
    simpa only [map_natCast] using h

/-- 同型は、恒等な有限エタール射とその同型に分解できる。 -/
theorem hasEtaleFactorization_of_bijective {A B : Type u} [CommRing A] [CommRing B]
    (p : ℕ) (f : A →+* B) (hf : Function.Bijective f) : HasEtaleFactorization p f := by
  refine ⟨CommRingCat.of A, RingHom.id A, f, rfl, inferInstance, inferInstance, ?_,
    invertPrimeMap_bijective p f hf⟩
  apply isUniversalHomeomorphism_of_nil_kernel f hf.surjective
  rw [(RingHom.injective_iff_ker_eq_bot f).mp hf.injective]
  exact bot_le

/-- 始域・終域の環同型に沿って、指定した射の分解を移す。 -/
theorem hasEtaleFactorization_transport {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (p : ℕ) (eA : A ≃+* A') (eB : B ≃+* B') (f : A →+* B)
    (hf : HasEtaleFactorization p f) :
    HasEtaleFactorization p ((eB.toRingHom.comp f).comp eA.symm.toRingHom) := by
  obtain ⟨T, a, b, hab, hfinite, hetale, hu, hp⟩ := hf
  let : Algebra A T := a.toAlgebra
  have hfina : (a.comp eA.symm.toRingHom).Finite :=
    (show a.Finite from hfinite).comp
      (RingHom.Finite.of_surjective _ eA.symm.surjective)
  have heta : (a.comp eA.symm.toRingHom).Etale :=
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective eA.symm.bijective) hetale
  have hueB : IsUniversalHomeomorphism eB.toRingHom := by
    apply isUniversalHomeomorphism_of_nil_kernel _ eB.surjective
    rw [(RingHom.injective_iff_ker_eq_bot eB.toRingHom).mp eB.injective]
    exact bot_le
  refine ⟨T, a.comp eA.symm.toRingHom, eB.toRingHom.comp b, ?_, hfina, heta,
    isUniversalHomeomorphism_comp b eB.toRingHom hu hueB, ?_⟩
  · ext x
    exact congrArg eB (RingHom.congr_fun hab (eA.symm x))
  · rw [invertPrimeMap_comp]
    exact (invertPrimeMap_bijective p eB.toRingHom eB.bijective).comp hp

end SerrePositivity.CommutativeAlgebra
