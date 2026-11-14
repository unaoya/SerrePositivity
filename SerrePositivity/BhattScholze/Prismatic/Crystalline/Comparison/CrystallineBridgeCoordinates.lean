module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridge
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCechResidue
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCoordinates
import Mathlib.RingTheory.MvPolynomial.Expand
import Mathlib.FieldTheory.Finite.Basic
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCechResidue
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCoordinates
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PolynomialFrobeniusCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineReductionPushout
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# 結晶の橋の二つの座標表示

## 概要
完備自由 δ 環の剰余の多項式座標を affine 模型への座標射と Frobenius に照合する。

## 方針
基底と反復 δ 座標で射の値を比較する。

## 規約
Frobenius は mod p で係数を固定する。

## 使われ方
結晶の橋の押し出しを Lemma 5.4 の形に移す。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "Z" => crystallineBasePrism p
local notation "hZ" => crystallineBaseBounded p
local notation "S" n => AffineIndex r (SimplexCategory.len n)
local notation "B" n => completedFreeDelta Z (S n)
local notation "D" n => completedFreeDeltaStructure Z (S n)
local notation "η" n => crystallineCompletedFreeDeltaUnit p (S n)
local notation "qB" n => crystallineModPrimeProjection p (CommRingCat.of (B n))
set_option quotPrecheck false in
local notation "qC" n => (project Z hZ r).app n

/-- 完備自由 δ Čech 余脈体から affine envelope への標準射。 -/
def crystallineAffineUnit : crystallineCechSource.{u} p r ⟶ zpCech.{u} p r where
  app n := CommRingCat.ofHom (aff p r n).η
  naturality _ _ θ := by
    apply CommRingCat.hom_ext
    exact (affineUnit_nat p r θ).symm

theorem crystallineAffineUnit_prime (n : SimplexCategory) :
    (crystallineAffineUnit.{u} p r).app n (p : (crystallineCechSource.{u} p r).obj n) =
      htGenerator (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r n := by
  change (aff p r n).η (p : B n) = (aff p r n).X.toHom.toRingHom (Z).generator
  rw [← DFunLike.congr_fun (aff p r n).base_eq (Z).generator]
  exact congrArg (aff p r n).η (((congrArg (completedFreeDeltaBase Z (S n))
    (crystallineBase_generator p)).trans (map_natCast _ p)).symm)

/-- 完備自由 δ 環から affine 模型への標準射を p により割る。 -/
abbrev crystallineAffineUnitModP : modPrimeCosimplicial p (crystallineCechSource.{u} p r) ⟶
    reducedModel (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r :=
  quotPowMap (crystallineCechSource p r) (fun n => (p : (crystallineCechSource p r).obj n))
    (fun θ => map_natCast ((crystallineCechSource p r).map θ).hom p)
    (htGenerator Z hZ r) (htGenerator_nat Z hZ r) (crystallineAffineUnit p r)
    (crystallineAffineUnit_prime p r) 1

/-- 完備自由 δ Čech 余脈体から結晶側の完備 p 除算模型への標準射。 -/
def crystallinePDUnit : crystallineCechSource.{u} p r ⟶ pdDeltaRings.{u} p r where
  app n := CommRingCat.ofHom (pdDeltaUnit p r n)
  naturality _ _ θ := by
    apply CommRingCat.hom_ext
    exact (pdDeltaMap_spec p r θ).2.symm

private theorem termResidue_mk_unit (n : SimplexCategory)
    (x : RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r n.len)) :
    termResidue.{u} p r n ((qB n) ((η n) x)) =
      MvPolynomial.rename (coordEquiv.{u} r n)
        (MvPolynomial.map (Ideal.Quotient.mk (crystallineBasePrism.{u} p).ideal) x) :=
  (termResidue_unit p r n x).trans (rawResidue_mk p r n x)

/-- affine 模型への標準射は剰余で反復 δ 座標を与える。 -/
theorem crystallineCechResidueIso_hom_deltaCoordinates :
    (crystallineCechResidueIso.{u} p r).hom ≫ deltaCoordinatesModP p r =
      crystallineAffineUnitModP p r := by
  apply NatTrans.ext
  funext n
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨f, rfl⟩ := termQuotient_surjective.{u} p r n x
  change polyToResidueApp Z hZ r n (termResidue p r n ((qB n) ((η n) f))) =
    (qC n) ((aff p r n).η ((η n) f))
  rw [termResidue_mk_unit]
  let L := (polyToResidueApp Z hZ r n).comp
    ((MvPolynomial.rename (coordEquiv.{u} r n)).toRingHom.comp
      (MvPolynomial.map (Ideal.Quotient.mk (Z).ideal)))
  let R := (qC n).hom.comp ((aff p r n).η.comp (η n))
  have h : L = R := by
    apply MvPolynomial.ringHom_ext'
    · apply RingHom.ext
      intro a
      change polyToResidueApp Z hZ r n (MvPolynomial.rename (coordEquiv.{u} r n)
        (MvPolynomial.map (Ideal.Quotient.mk (Z).ideal) (MvPolynomial.C a))) =
        (qC n) ((aff p r n).η ((η n) (MvPolynomial.C a)))
      rw [MvPolynomial.map_C, MvPolynomial.rename_C, polyToResidueApp_C, residueCoeff_mk]
      exact congrArg (qC n) (DFunLike.congr_fun (aff p r n).base_eq a).symm
    · rintro ⟨⟨⟨j,i⟩⟩,a⟩
      change polyToResidueApp Z hZ r n
        (MvPolynomial.rename (coordEquiv.{u} r n)
          (MvPolynomial.map (Ideal.Quotient.mk (Z).ideal) (MvPolynomial.X (⟨(j,i)⟩,a)))) =
        (qC n) (((aff p r n).η.comp (η n)) (MvPolynomial.X (⟨(j,i)⟩,a)))
      rw [MvPolynomial.map_X, MvPolynomial.rename_X, polyToResidueApp_X]
      apply congrArg (qC n)
      rw [relativeFreeDeltaHom_X_iterates (Z).deltaStructure (aff p r n).X.Q.deltaStructure
        ((aff p r n).η.comp (η n))
        ((aff p r n).envelope.isDeltaHom.comp (crystallineCompletedFreeDeltaUnit_isDeltaHom p _))]
      rfl
  exact DFunLike.congr_fun h f

/-- 完備自由 δ Čech 余脈体に項ごとの Frobenius を施す。 -/
def crystallineCechFrobenius : crystallineCechSource.{u} p r ⟶ crystallineCechSource.{u} p r where
  app n := CommRingCat.ofHom (D n).frobeniusLift
  naturality _ _ θ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact ((crystallineCechSourceMap_spec p r θ).1.map_frobeniusLift x).symm

/-- 完備自由 δ 環の Frobenius は剰余で多項式の相対 Frobenius。 -/
theorem crystallineCechResidueIso_frobenius_app (n : SimplexCategory) :
    (modPrimeMap p (crystallineCechFrobenius.{u} p r)).app n ≫
      (crystallineCechResidueIso.{u} p r).hom.app n =
    (crystallineCechResidueIso.{u} p r).hom.app n ≫
      (relativeFrobeniusCech p (cartierBase.{u} p) (Fin r × ℕ)).app n := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  let e := termResidue.{u} p r n
  let q := (qB n).hom
  have hp : q (p : B n) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [pow_one]
    exact Ideal.subset_span rfl
  let y : B n := x
  have hF : q ((D n).frobeniusLift y) = q y ^ p := by
    rw [DeltaStructure.frobeniusLift_apply, map_add, map_pow, map_mul, hp, zero_mul, add_zero]
  let : CharP (cartierBase.{u} p) p :=
    charP_of_injective_ringHom (f := (cartierBaseEquiv.{u} p).symm.toRingHom)
      (cartierBaseEquiv.{u} p).symm.injective p
  have hcoeff : frobenius (cartierBase.{u} p) p = RingHom.id _ := by
    ext a
    apply (cartierBaseEquiv p).injective
    change (cartierBaseEquiv p) (a ^ p) = (cartierBaseEquiv p) a
    rw [map_pow, ZMod.pow_card]
  change e (q ((D n).frobeniusLift y)) = MvPolynomial.expand p (e (q y))
  rw [hF]
  refine (map_pow e (q y) p).trans ?_
  let w : MvPolynomial ((Fin r × ℕ) × Fin (n.len + 1)) (cartierBase.{u} p) := e (q y)
  have hw : w ^ p = MvPolynomial.expand p w := by
    simpa only [hcoeff, MvPolynomial.map_id] using
      (MvPolynomial.map_frobenius_expand p (f := w)).symm
  exact hw

end SerrePositivity.BhattScholze.Prismatic
