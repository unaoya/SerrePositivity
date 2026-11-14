module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineTotalCoordinate
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCrystallineReduction
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamTotalCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamTotalCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineTotalCoordinate
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCrystallineReduction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDCoordinateForms
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRowZeroProduct
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamProjectionProduct
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDRawDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumnZero
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.CommutativeAlgebra.DeRham.ExteriorCoefficientMap

/-!
# 還元した座標余鎖の二つの射影

## 概要
整係数で作った座標余鎖を還元してから、第 0 行と第 0 列への射影を計算する。

## 方針
成分の挿入と係数変換の可換性を使い、残る成分を環の剰余と通常の多項式形式で読む。

## 規約
縦の代表は第 0 頂点の座標の p−1 乗を掛けた一次形式。

## 使われ方
結晶基底での Cartier の生成元の同定。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial SerrePositivity.DeRham
  SerrePositivity.DerivedCompletion SerrePositivity.HomologicalAlgebra
open scoped Simplicial TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "K" => crystallineBase p
local notation "k" => cartierBase p

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorPowerCoefficients_unit_zero (n : ℕ) :
    let I := Fin r × Fin (n+1)
    exteriorPowerCoefficients (crystallineBase.{u} p) (cartierBase.{u} p) I 0
        ((exteriorPower.zeroEquiv K (I →₀ K)).symm 1) =
      (exteriorPower.zeroEquiv k (I →₀ k)).symm 1 := by
  dsimp only
  apply Subtype.ext
  change exteriorAlgebraCoeff K k (Fin r × Fin (n+1))
      ((exteriorPower.zeroEquiv K ((Fin r × Fin (n+1)) →₀ K)).symm 1).1 =
    ((exteriorPower.zeroEquiv k ((Fin r × Fin (n+1)) →₀ k)).symm 1).1
  simp [exteriorPower.zeroEquiv_symm_apply, ExteriorAlgebra.ιMulti_zero_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem rowZeroTerm_symm_tmul (A : Type u) [CommRing A] (n : ℕ)
    (x : pdTerm p A r n) :
    (rowZeroTerm p A r ⦋n⦌).symm x =
      x ⊗ₜ[A] (exteriorPower.zeroEquiv A (CopyModule A r ⦋n⦌)).symm 1 := by
  apply (rowZeroTerm p A r ⦋n⦌).injective
  rw [LinearEquiv.apply_symm_apply, rowZeroTerm_tmul, LinearEquiv.apply_symm_apply, one_smul]

set_option backward.isDefEq.respectTransparency false in
private theorem pdCoordinateAt_rowZero (n : ℕ) (x : (pdRings.{u} p r).obj ⦋n⦌) :
    rowZeroTerm p (cartierBase.{u} p) r ⦋n⦌
      (pdCoefficientAt p (crystallineBase.{u} p) (cartierBase.{u} p) r n 0
        ((rowZeroTerm p (crystallineBase.{u} p) r ⦋n⦌).symm x)) =
      (pdModel_modP p r).hom.app ⦋n⦌ (crystallineModPrimeProjection p ((pdRings.{u} p r).obj ⦋n⦌) x) := by
  change rowZeroTerm p (cartierBase.{u} p) r ⦋n⦌
    (TensorProduct.map (pdTermCoefficientMap p (crystallineBase.{u} p) (cartierBase.{u} p) r n)
      (exteriorPowerCoefficients (crystallineBase.{u} p) (cartierBase.{u} p) (Fin r × Fin (n+1)) 0)
      ((rowZeroTerm p (crystallineBase.{u} p) r ⦋n⦌).symm x)) = _
  rw [rowZeroTerm_symm_tmul, TensorProduct.map_tmul, exteriorPowerCoefficients_unit_zero,
    rowZeroTerm_tmul, LinearEquiv.apply_symm_apply, one_smul]
  exact (pdModel_modP_coefficient p r ⦋n⦌ x).symm

set_option backward.isDefEq.respectTransparency false in
private theorem pdColumnZero_unit (i : ℕ)
    (x : pdRawForms (cartierBase.{u} p) r ⦋0⦌ i) :
    (pdDeRhamColumnZeroIso (cartierBase.{u} p) r p (cartierBase_natCast p)).hom.f i
      (pdFormsUnit p (cartierBase.{u} p) r ⦋0⦌ i x) = zeroFormsEquiv (cartierBase.{u} p) r i x := by
  let e := pdRawFormsEquiv p (cartierBase.{u} p) r (cartierBase_natCast p) ⦋0⦌ i
  have h : pdFormsUnit p (cartierBase.{u} p) r ⦋0⦌ i = e.toLinearMap := by
    apply TensorProduct.ext'
    intro a w
    change TensorProduct.map (pdRawCoefficientUnit p (cartierBase.{u} p) r 0) LinearMap.id
        (a ⊗ₜ[k] w) = e (a ⊗ₜ[k] w)
    rw [TensorProduct.map_tmul, LinearMap.id_apply, pdRawFormsEquiv_tmul, pdRawToTerm_eq_unit]
    rfl
  rw [h]
  change zeroFormsEquiv (cartierBase.{u} p) r i (e.symm (e x)) = _
  rw [LinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem pdFormsCoefficientMap_unit_coordinate (j : Fin r) (m : ℕ) :
    pdTermCoefficientMap p (crystallineBase.{u} p) (cartierBase.{u} p) r 0
        (pdRawCoefficientUnit p (crystallineBase.{u} p) r 0 ((baseVar K r ⦋0⦌ j) ^ m)) =
      pdRawCoefficientUnit p (cartierBase.{u} p) r 0 ((baseVar k r ⦋0⦌ j) ^ m) := by
  let U (A : Type u) [CommRing A] := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw A r 0))
  change pdTermCoefficientMap p K k r 0 (U K ((baseVar K r ⦋0⦌ j)^m)) = U k ((baseVar k r ⦋0⦌ j)^m)
  rw [pdTermCoefficientMap_unit, map_pow]
  have h (A : Type u) [CommRing A] : copy A r ⦋0⦌ j 0 = baseVar A r ⦋0⦌ j := by simp [copy, vertexDiff]
  rw [← h K, ← h k, pdRawCoefficients_copy]

private def reducedCoordinateZero (j : Fin r) :
    (pdDeRhamTotal p (cartierBase.{u} p) r).X 0 :=
  pdTotalCoefficientMap p (crystallineBase.{u} p) (cartierBase.{u} p) r 0
    (pdTotalCoordinateZero p r j)

private def reducedCoordinateOne (j : Fin r) (y : (pdRings.{u} p r).obj ⦋1⦌) :
    (pdDeRhamTotal p (cartierBase.{u} p) r).X 1 :=
  pdTotalCoefficientMap p (crystallineBase.{u} p) (cartierBase.{u} p) r 1
    (pdTotalCoordinateOne p r j y)

set_option backward.isDefEq.respectTransparency false in
private theorem reducedCoordinateZero_closed (j : Fin r) :
    (pdDeRhamTotal p (cartierBase.{u} p) r).d 0 1 (reducedCoordinateZero p r j) = 0 := by
  obtain ⟨y, hy⟩ := pdFrobCoordinate_horizontal_dvd.{u} p r j
  unfold reducedCoordinateZero
  rw [← pdTotalCoefficientMap_d p (crystallineBase.{u} p) (cartierBase.{u} p) r 0,
    pdTotalCoordinate_d p r j y hy, map_nsmul, ← Nat.cast_smul_eq_nsmul (R := k),
    cartierBase_natCast, zero_smul]

set_option backward.isDefEq.respectTransparency false in
private theorem reducedCoordinateOne_closed (j : Fin r) (y : (pdRings.{u} p r).obj ⦋1⦌)
    (hy : cochainDifferential (pdRings.{u} p r) 0 (pdCoordinateLift p r j ^ p) =
      (p : (pdRings.{u} p r).obj ⦋1⦌) * y) :
    (pdDeRhamTotal p (cartierBase.{u} p) r).d 1 2 (reducedCoordinateOne p r j y) = 0 := by
  unfold reducedCoordinateOne
  rw [← pdTotalCoefficientMap_d p (crystallineBase.{u} p) (cartierBase.{u} p) r 1,
    pdTotalCoordinateOne_closed p r j y hy, map_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem reducedCoordinateZero_row (j : Fin r) :
    (pdDeRhamRowZeroIso p (cartierBase.{u} p) r).hom.f 0
      ((pdDeRhamRowZeroProjection p (cartierBase.{u} p) r).f 0 (reducedCoordinateZero p r j)) =
      (pdModel_modP p r).hom.app ⦋0⦌
        (crystallineModPrimeProjection p ((pdRings.{u} p r).obj ⦋0⦌) (pdCoordinateLift p r j ^ p)) := by
  unfold reducedCoordinateZero pdTotalCoordinateZero
  rw [pdTotalCoefficientMap_insert, pdFrobCoordinate_zero_form p r]
  let L := pdDeRhamDoubleComplex p (cartierBase.{u} p) r
  let x := (rowZeroTerm p (crystallineBase.{u} p) r ⦋0⦌).symm (pdCoordinateLift p r j ^ p)
  let f := pdCoefficientAt p (crystallineBase.{u} p) (cartierBase.{u} p) r 0 0
  change rowZeroTerm p (cartierBase.{u} p) r ⦋0⦌
    ((totalToRowZero L).f 0 (insertAt L 0 ⟨(0,0),rfl⟩ (f x))) = _
  rw [rowProjection_on]
  exact pdCoordinateAt_rowZero p r 0 _

set_option backward.isDefEq.respectTransparency false in
private theorem reducedCoordinateOne_row (j : Fin r) (y : (pdRings.{u} p r).obj ⦋1⦌) :
    (pdDeRhamRowZeroIso p (cartierBase.{u} p) r).hom.f 1
      ((pdDeRhamRowZeroProjection p (cartierBase.{u} p) r).f 1 (reducedCoordinateOne p r j y)) =
      (pdModel_modP p r).hom.app ⦋1⦌ (crystallineModPrimeProjection p ((pdRings.{u} p r).obj ⦋1⦌) y) := by
  unfold reducedCoordinateOne pdTotalCoordinateOne
  rw [map_add, pdTotalCoefficientMap_insert, pdTotalCoefficientMap_insert]
  let L := pdDeRhamDoubleComplex p (cartierBase.{u} p) r
  change rowZeroTerm p (cartierBase.{u} p) r ⦋1⦌
    ((totalToRowZero L).f 1 (insertAt L 1 ⟨(1,0),rfl⟩ _ + insertAt L 1 ⟨(0,1),rfl⟩ _)) = _
  rw [map_add, rowProjection_on, rowProjection_off L (by rfl) (by decide), add_zero]
  exact pdCoordinateAt_rowZero p r 1 y

set_option backward.isDefEq.respectTransparency false in
private theorem reducedCoordinateZero_column (j : Fin r) :
    (pdDeRhamColumnZeroIso (cartierBase.{u} p) r p (cartierBase_natCast p)).hom.f 0
      ((pdDeRhamColumnZeroProjection p (cartierBase.{u} p) r).f 0 (reducedCoordinateZero p r j)) =
      formsZeroEquiv k (formVars.{u} r) ((MvPolynomial.X (ULift.up j) : Poly k (formVars.{u} r)) ^ p) := by
  unfold reducedCoordinateZero pdTotalCoordinateZero
  rw [pdTotalCoefficientMap_insert]
  let L := pdDeRhamDoubleComplex p (cartierBase.{u} p) r
  change (pdDeRhamColumnZeroIso (cartierBase.{u} p) r p (cartierBase_natCast p)).hom.f 0
    ((totalToColumnZero L).f 0 (insertAt L 0 ⟨(0,0),rfl⟩ _)) = _
  rw [columnProjection_on]
  have h : pdCoefficientAt p (crystallineBase.{u} p) (cartierBase.{u} p) r 0 0
      (pdFormsUnit p (crystallineBase.{u} p) r ⦋0⦌ 0 (pdRawZeroCoordinate p (crystallineBase.{u} p) r j)) =
      pdFormsUnit p (cartierBase.{u} p) r ⦋0⦌ 0 (pdRawZeroCoordinate p (cartierBase.{u} p) r j) := by
    let u := pdRawCoefficientUnit p (crystallineBase.{u} p) r 0
    let v := pdRawCoefficientUnit p (cartierBase.{u} p) r 0
    let f := pdTermCoefficientMap p (crystallineBase.{u} p) (cartierBase.{u} p) r 0
    let E := exteriorPowerCoefficients (crystallineBase.{u} p) (cartierBase.{u} p) (Fin r × Fin 1) 0
    let wA := (exteriorPower.zeroEquiv K (CopyModule (crystallineBase.{u} p) r ⦋0⦌)).symm 1
    let wB := (exteriorPower.zeroEquiv k (CopyModule (cartierBase.{u} p) r ⦋0⦌)).symm 1
    change TensorProduct.map f E (TensorProduct.map u LinearMap.id ((baseVar K r ⦋0⦌ j ^ p) ⊗ₜ[K] wA)) =
      TensorProduct.map v LinearMap.id ((baseVar k r ⦋0⦌ j ^ p) ⊗ₜ[k] wB)
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.id_apply, pdFormsCoefficientMap_unit_coordinate]
    exact congrArg (fun x => v (baseVar k r ⦋0⦌ j ^ p) ⊗ₜ[k] x)
      (exteriorPowerCoefficients_unit_zero p r 0)
  rw [h, pdColumnZero_unit, zeroFormsEquiv_coordinateZero]

set_option backward.isDefEq.respectTransparency false in
private theorem reducedCoordinateOne_column (j : Fin r) (y : (pdRings.{u} p r).obj ⦋1⦌) :
    (pdDeRhamColumnZeroIso (cartierBase.{u} p) r p (cartierBase_natCast p)).hom.f 1
      ((pdDeRhamColumnZeroProjection p (cartierBase.{u} p) r).f 1 (reducedCoordinateOne p r j y)) =
      ((MvPolynomial.X (ULift.up j) : Poly k (formVars.{u} r)) ^ (p-1)) • dX k (formVars.{u} r) (ULift.up j) := by
  unfold reducedCoordinateOne pdTotalCoordinateOne
  rw [map_add, pdTotalCoefficientMap_insert, pdTotalCoefficientMap_insert]
  let L := pdDeRhamDoubleComplex p (cartierBase.{u} p) r
  change (pdDeRhamColumnZeroIso (cartierBase.{u} p) r p (cartierBase_natCast p)).hom.f 1
    ((totalToColumnZero L).f 1 (insertAt L 1 ⟨(1,0),rfl⟩ _ + insertAt L 1 ⟨(0,1),rfl⟩ _)) = _
  rw [map_add, columnProjection_off L (by rfl) (by decide), columnProjection_on, zero_add]
  have h : pdCoefficientAt p (crystallineBase.{u} p) (cartierBase.{u} p) r 0 1
      (pdFormsUnit p (crystallineBase.{u} p) r ⦋0⦌ 1 (pdRawOneCoordinate p (crystallineBase.{u} p) r j)) =
      pdFormsUnit p (cartierBase.{u} p) r ⦋0⦌ 1 (pdRawOneCoordinate p (cartierBase.{u} p) r j) := by
    let u := pdRawCoefficientUnit p (crystallineBase.{u} p) r 0
    let v := pdRawCoefficientUnit p (cartierBase.{u} p) r 0
    let f := pdTermCoefficientMap p (crystallineBase.{u} p) (cartierBase.{u} p) r 0
    let E := exteriorPowerCoefficients (crystallineBase.{u} p) (cartierBase.{u} p) (Fin r × Fin 1) 1
    let wA := pdCoordinateOne (crystallineBase.{u} p) r ⦋0⦌ (.inl j)
    let wB := pdCoordinateOne (cartierBase.{u} p) r ⦋0⦌ (.inl j)
    change TensorProduct.map f E
        (TensorProduct.map u LinearMap.id ((baseVar K r ⦋0⦌ j ^ (p-1)) ⊗ₜ[K] wA)) =
      TensorProduct.map v LinearMap.id ((baseVar k r ⦋0⦌ j ^ (p-1)) ⊗ₜ[k] wB)
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.id_apply, pdFormsCoefficientMap_unit_coordinate]
    exact congrArg (fun x => v (baseVar k r ⦋0⦌ j ^ (p-1)) ⊗ₜ[k] x)
      (pdCoordinateOne_coefficients (crystallineBase.{u} p) (cartierBase.{u} p) r ⦋0⦌ (.inl j))
  rw [h, pdColumnZero_unit, zeroFormsEquiv_coordinateOne]

end SerrePositivity.BhattScholze.Prismatic
