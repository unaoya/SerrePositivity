module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBockstein
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawFrobeniusCoordinate
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridge
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCoordinates
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDIntegral
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDInclusion
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineExtraModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Poincare.CrystallineExtraContraction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDTensorPresentation
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDModelReduction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# 結晶の橋での零次生成元

## 概要
affine 座標の η⁰ と、完備 pd 模型での第 0 頂点の Frobenius 座標を照合する。

## 方針
二つの整係数の射を自由 δ 環の座標で計算し、剰余で Frobenius を p 乗にする。

## 規約
第 0 頂点を選ぶ。

## 使われ方
η¹ を Bockstein で比較する。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits SerrePositivity.Cosimplicial SerrePositivity.DerivedCompletion
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

set_option quotPrecheck false

local notation "K" => crystallineBase p
local notation "Z" => crystallineBasePrism p
local notation "hZ" => crystallineBaseBounded p
local notation "C" => pdRings p r
local notation "D" => pdDeltaRings p r
local notation "U" => Under.forget (CommRingCat.of K)
local notation "X" => reducedModel Z hZ r

/-- 第 0 頂点の完備 pd 座標。 -/
def pdCoordinateLift (j : Fin r) : (C).obj ⦋0⦌ :=
  (rawUnit p r K).app ⦋0⦌ (copy K r ⦋0⦌ j 0)

set_option maxHeartbeats 1300000 in
set_option backward.isDefEq.respectTransparency false in
private theorem pdInclusion_coordinate (j : Fin r) :
    ((pdInclusion p r).app ⦋0⦌).right (pdCoordinateLift p r j) =
      pdDeltaUnit p r ⦋0⦌ (affineVariable Z r 0 j 0) := by
  let n := ⦋0⦌
  let b := copy K r n j 0
  let f := (rawInsertPdFactor K r).app n
  have hf : f.right = extraLeft K r n := by
    let a := (extraCechArrow K r).augmentedCechConerve.hom.app n
    have h : f = (coprod.inl : _ ⟶ _) := by
      change coprod.inl ≫ coprod.map (𝟙 ((pdRawModel K r).obj n)) a = coprod.inl
      rw [coprod.inl_map, Category.id_comp]
    exact congrArg Under.Hom.right h
  have h₁ := ConcreteCategory.congr_hom (ringCatMap_comp_unit p f.right) b
  simp only [ConcreteCategory.comp_apply] at h₁
  have hh : ((insertPdFactor p K r).app n).right (pdCoordinateLift p r j) =
      (extraCompletionUnit p r).app n (extraLeft K r n b) := by
    change ringCatMap p f.right
      (principalCompletionRingCatUnit p ((pdRawModel K r).obj n).right b) =
        principalCompletionRingCatUnit p ((crystallineExtraRaw K r).obj n).right
          (extraLeft K r n b)
    exact h₁.trans (congrArg
      (principalCompletionRingCatUnit p ((crystallineExtraRaw K r).obj n).right)
      (ConcreteCategory.congr_hom hf b))
  have h₂ := ConcreteCategory.congr_hom (NatTrans.congr_app (completedToTarget_spec p r) n)
    (extraLeft K r n b)
  change (completedToTarget p r).app n
    ((extraCompletionUnit p r).app n (extraLeft K r n b)) = extraToTargetApp p r n (extraLeft K r n b) at h₂
  change (completedToTarget p r).app n (((insertPdFactor p K r).app n).right (pdCoordinateLift p r j)) = _
  rw [hh, h₂, ← rawCoordToExtra_zero p r n j 0, extraToTargetApp_coord]
  rfl

set_option maxHeartbeats 1400000 in
set_option backward.isDefEq.respectTransparency false in
private theorem affine_coordinate_reduction (j : Fin r) :
    htSec Z hZ r ⦋0⦌ (prismPolynomialUnit Z (Fin r) (MvPolynomial.X j)) =
      (project Z hZ r).app ⦋0⦌ ((aff p r ⦋0⦌).η (affineVariable Z r 0 j 0)) := by
  let M := aff p r ⦋0⦌
  change (htResidueIso Z hZ r ⦋0⦌).symm
    (M.X.sec (prismPolynomialUnit Z (Fin r) (MvPolynomial.X j))) = _
  rw [M.sec_X]
  exact rfl

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
/-- 結晶の橋と pd 包含の零次での値は、Frobenius 座標の剰余で一致する。 -/
theorem crystallineBridge_coordinate (j : Fin r) :
    (crystallineBridgeModP p r).app ⦋0⦌
      (htSec Z hZ r ⦋0⦌ (prismPolynomialUnit Z (Fin r) (MvPolynomial.X j))) =
    (pdInclusionModP p r).app ⦋0⦌
      (crystallineModPrimeProjection p ((C).obj ⦋0⦌) ((pdCoordinateLift p r j) ^ p)) := by
  rw [affine_coordinate_reduction, pdInclusionModP_eq_modPrime]
  let n := ⦋0⦌
  let q := (crystallineModPrimeProjection p ((D).obj n)).hom
  let v := affineVariable Z r 0 j 0
  let g := ((pdInclusion p r).app n).right.hom
  change q (bridgeApp p r n ((aff p r n).η v)) = q (g ((pdCoordinateLift p r j) ^ p))
  have hb := DFunLike.congr_fun (bridgeApp_spec p r n).2 v
  change bridgeApp p r n ((aff p r n).η v) = toTarget p r n v at hb
  rw [hb, map_pow g, pdInclusion_coordinate, map_pow q]
  change q ((pdDeltaUnit p r n) ((completedFreeDeltaStructure Z (AffineIndex r 0)).frobeniusLift v)) =
    q ((pdDeltaUnit p r n) v) ^ p
  have hq : q (p : (D).obj n) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [pow_one]
    exact Ideal.subset_span rfl
  let f : completedFreeDelta Z (AffineIndex r 0) →+* (D).obj n := pdDeltaUnit p r n
  change q (f ((completedFreeDeltaStructure Z (AffineIndex r 0)).frobeniusLift v)) = q (f v) ^ p
  let F := q.comp f
  change F ((completedFreeDeltaStructure Z (AffineIndex r 0)).frobeniusLift v) = F v ^ p
  have hp : F (p : completedFreeDelta Z (AffineIndex r 0)) = 0 :=
    (congrArg q (map_natCast f p)).trans hq
  rw [DeltaStructure.frobeniusLift_apply, map_add, map_pow, map_mul, hp, zero_mul, add_zero]

end SerrePositivity.BhattScholze.Prismatic
