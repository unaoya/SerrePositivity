module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineTotalRegular
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineGeneratorBridge
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDCoordinateForms
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineGeneratorBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDCoordinateForms
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRowZeroProduct
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDModelReduction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawFrobeniusCoordinate
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass

/-!
# 総複体での Frobenius 座標の整係数微分

## 概要
第 0 頂点の Frobenius 座標を総微分し、横・縦の両成分を p で割る。

## 方針
横成分は分冪の階乗、縦成分は第 0 列での多項式微分で計算する。

## 規約
総次数 0 からの縦微分の符号は正。

## 使われ方
mod p での二つの射影の Bockstein 照合。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial SerrePositivity.HomologicalAlgebra
open scoped Simplicial TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)


set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 120000 in
set_option backward.isDefEq.respectTransparency false in
private theorem pdFrobCoordinate_horizontal_dvd (j : Fin r) :
    (p : (pdRings.{u} p r).obj ⦋1⦌) ∣
      cochainDifferential (pdRings.{u} p r) 0 (pdCoordinateLift p r j ^ p) := by
  obtain ⟨y, hy⟩ := pdRaw_frobeniusCoordinate_dvd p (crystallineBase.{u} p) r j
  let U := rawUnit p r (crystallineBase.{u} p)
  have hx : U.app ⦋0⦌ (pdRawFrobeniusCoordinate p (crystallineBase.{u} p) r j) = pdCoordinateLift p r j ^ p :=
    by
      change U.app ⦋0⦌ (copy (crystallineBase.{u} p) r ⦋0⦌ j 0 ^ p) =
        U.app ⦋0⦌ (copy (crystallineBase.{u} p) r ⦋0⦌ j 0) ^ p
      exact map_pow (U.app ⦋0⦌).hom _ _
  refine ⟨U.app ⦋1⦌ y, ?_⟩
  rw [← hx, ← cochainDifferential_natural _ _ U, hy, map_mul, map_natCast]

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 120000 in
set_option backward.isDefEq.respectTransparency false in
private theorem pdFrobCoordinate_zero_form (j : Fin r) :
    pdFormsUnit p (crystallineBase.{u} p) r ⦋0⦌ 0
        (pdRawZeroCoordinate p (crystallineBase.{u} p) r j) =
      (show (pdRow p (crystallineBase.{u} p) r 0).obj ⦋0⦌ from
        (rowZeroTerm p (crystallineBase.{u} p) r ⦋0⦌).symm (pdCoordinateLift p r j ^ p)) := by
  change (_ : pdTerm p (crystallineBase.{u} p) r 0 ⊗[(crystallineBase.{u} p)]
    (⋀[crystallineBase.{u} p]^0 (CopyModule (crystallineBase.{u} p) r ⦋0⦌))) = _
  apply (rowZeroTerm p (crystallineBase.{u} p) r ⦋0⦌).injective
  rw [LinearEquiv.apply_symm_apply]
  let w := (exteriorPower.zeroEquiv (crystallineBase.{u} p) (CopyModule (crystallineBase.{u} p) r ⦋0⦌)).symm 1
  let u := pdRawCoefficientUnit p (crystallineBase.{u} p) r 0
  change (rowZeroTerm p (crystallineBase.{u} p) r ⦋0⦌) (TensorProduct.map u LinearMap.id ((baseVar (crystallineBase.{u} p) r ⦋0⦌ j ^ p) ⊗ₜ[(crystallineBase.{u} p)] w)) = _
  rw [TensorProduct.map_tmul, LinearMap.id_apply, rowZeroTerm_tmul,
    LinearEquiv.apply_symm_apply, one_smul]
  let f := (rawUnit p r (crystallineBase.{u} p)).app ⦋0⦌
  change f (baseVar (crystallineBase.{u} p) r ⦋0⦌ j ^ p) = f (copy (crystallineBase.{u} p) r ⦋0⦌ j 0) ^ p
  have h : copy (crystallineBase.{u} p) r ⦋0⦌ j 0 = baseVar (crystallineBase.{u} p) r ⦋0⦌ j := by simp [copy, vertexDiff]
  rw [h, map_pow]

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 120000 in
set_option backward.isDefEq.respectTransparency false in
private theorem pdFrobCoordinate_horizontal (j : Fin r) (y : (pdRings.{u} p r).obj ⦋1⦌)
    (hy : cochainDifferential (pdRings.{u} p r) 0 (pdCoordinateLift p r j ^ p) = (p : (pdRings.{u} p r).obj ⦋1⦌) * y) :
    (((pdDeRhamDoubleComplex p (crystallineBase.{u} p) r)).d 0 1).f 0 (pdFormsUnit p (crystallineBase.{u} p) r ⦋0⦌ 0 (pdRawZeroCoordinate p (crystallineBase.{u} p) r j)) =
      p • (rowZeroTerm p (crystallineBase.{u} p) r ⦋1⦌).symm y := by
  rw [pdFrobCoordinate_zero_form p r]
  apply (rowZeroTerm p (crystallineBase.{u} p) r ⦋1⦌).injective
  let J := pdDeRhamRowZeroIso p (crystallineBase.{u} p) r
  let x := (rowZeroTerm p (crystallineBase.{u} p) r ⦋0⦌).symm (pdCoordinateLift p r j ^ p)
  have h := ConcreteCategory.congr_hom (J.hom.comm 0 1) x
  replace h := h.symm
  simp only [ConcreteCategory.comp_apply] at h
  change (rowZeroTerm p (crystallineBase.{u} p) r ⦋1⦌) ((((pdDeRhamDoubleComplex p (crystallineBase.{u} p) r)).d 0 1).f 0 x) =
    (moduleCochains (crystallineBase.{u} p) (pdRings.{u} p r) (pdCechBase p (crystallineBase.{u} p) r)).d 0 1 ((rowZeroTerm p (crystallineBase.{u} p) r ⦋0⦌) x) at h
  rw [moduleCochains_d_apply, LinearEquiv.apply_symm_apply] at h
  change (rowZeroTerm p (crystallineBase.{u} p) r ⦋1⦌) ((((pdDeRhamDoubleComplex p (crystallineBase.{u} p) r)).d 0 1).f 0 x) = _
  rw [h, hy, map_nsmul, LinearEquiv.apply_symm_apply, nsmul_eq_mul]

private def pdTotalCoordinateZero (j : Fin r) :
    (pdDeRhamTotal p (crystallineBase.{u} p) r).X 0 :=
  insertAt (pdDeRhamDoubleComplex p (crystallineBase.{u} p) r) 0 ⟨(0,0),rfl⟩ (pdFormsUnit p (crystallineBase.{u} p) r ⦋0⦌ 0 (pdRawZeroCoordinate p (crystallineBase.{u} p) r j))

private def pdTotalCoordinateOne (j : Fin r) (y : (pdRings.{u} p r).obj ⦋1⦌) :
    (pdDeRhamTotal p (crystallineBase.{u} p) r).X 1 :=
  insertAt (pdDeRhamDoubleComplex p (crystallineBase.{u} p) r) 1 ⟨(1,0),rfl⟩ ((rowZeroTerm p (crystallineBase.{u} p) r ⦋1⦌).symm y) +
    insertAt (pdDeRhamDoubleComplex p (crystallineBase.{u} p) r) 1 ⟨(0,1),rfl⟩ (pdFormsUnit p (crystallineBase.{u} p) r ⦋0⦌ 1 (pdRawOneCoordinate p (crystallineBase.{u} p) r j))

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 120000 in
set_option backward.isDefEq.respectTransparency false in
private theorem pdTotalCoordinate_d (j : Fin r) (y : (pdRings.{u} p r).obj ⦋1⦌)
    (hy : cochainDifferential (pdRings.{u} p r) 0 (pdCoordinateLift p r j ^ p) = (p : (pdRings.{u} p r).obj ⦋1⦌) * y) :
    (pdDeRhamTotal p (crystallineBase.{u} p) r).d 0 1 (pdTotalCoordinateZero p r j) =
      p • pdTotalCoordinateOne p r j y := by
  let z := pdFormsUnit p (crystallineBase.{u} p) r ⦋0⦌ 0 (pdRawZeroCoordinate p (crystallineBase.{u} p) r j)
  have h := ConcreteCategory.congr_hom (insertAt_total_d (pdDeRhamDoubleComplex p (crystallineBase.{u} p) r) (n := 0) (a := 0) (b := 0) rfl) z
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_add, LinearMap.add_apply, pow_zero, one_zsmul] at h
  change (pdDeRhamTotal p (crystallineBase.{u} p) r).d 0 1 (pdTotalCoordinateZero p r j) = _
  unfold pdTotalCoordinateZero
  rw [h]
  have hH := pdFrobCoordinate_horizontal p r j y hy
  change ((pdDeRhamDoubleComplex p (crystallineBase.{u} p) r).d 0 1).f 0 z = _ at hH
  rw [hH]
  have hV : (((pdDeRhamDoubleComplex p (crystallineBase.{u} p) r)).X 0).d 0 1 z = p • pdFormsUnit p (crystallineBase.{u} p) r ⦋0⦌ 1 (pdRawOneCoordinate p (crystallineBase.{u} p) r j) := by
    change (pdDeRhamColumn p (crystallineBase.{u} p) r ⦋0⦌).d 0 1 z = _
    rw [column_d_eq]
    exact pdVerticalD_coordinate p (crystallineBase.{u} p) r j
  rw [hV, map_nsmul, map_nsmul, ← nsmul_add]
  rfl

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 120000 in
set_option backward.isDefEq.respectTransparency false in
private theorem pdTotalCoordinateOne_closed (j : Fin r) (y : (pdRings.{u} p r).obj ⦋1⦌)
    (hy : cochainDifferential (pdRings.{u} p r) 0 (pdCoordinateLift p r j ^ p) = (p : (pdRings.{u} p r).obj ⦋1⦌) * y) :
    (pdDeRhamTotal p (crystallineBase.{u} p) r).d 1 2 (pdTotalCoordinateOne p r j y) = 0 := by
  apply pdTotal_eq_zero_of_p_smul p r 2
  rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← pdTotalCoordinate_d p r j y hy,
    ← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]
  rfl

end SerrePositivity.BhattScholze.Prismatic
