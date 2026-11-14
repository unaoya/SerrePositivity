module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumnZero
public import SerrePositivity.CommutativeAlgebra.DeRham.PolynomialCoordinatePower
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionLinearMap
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumnZero
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDRawDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierRepresentatives

/-!
# 第 0 頂点の Frobenius 座標の形式

## 概要
第 0 頂点の p 乗と inverse Cartier の一次代表形式を pd 列で表す。

## 方針
第 0 列の未完備表示で通常の多項式微分に帰着し、完備化単位で比較する。

## 規約
次数 0 の形式には第 0 外冪の単位をテンソルする。

## 使われ方
結晶基底の総複体での Bockstein の計算。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DeRham SerrePositivity.DerivedCompletion
open scoped Simplicial TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

private def pdRawZeroCoordinate (j : Fin r) : pdRawForms k r ⦋0⦌ 0 :=
  (baseVar k r ⦋0⦌ j ^ p) ⊗ₜ[k] (exteriorPower.zeroEquiv k (CopyModule k r ⦋0⦌)).symm 1

private def pdRawOneCoordinate (j : Fin r) : pdRawForms k r ⦋0⦌ 1 :=
  (baseVar k r ⦋0⦌ j ^ (p-1)) ⊗ₜ[k] pdCoordinateOne k r ⦋0⦌ (.inl j)

private theorem zeroTermCoefficients_X_pow (j : Fin r) (a : ℕ) :
    zeroTermCoefficients k r (baseVar k r ⦋0⦌ j ^ a) =
      (MvPolynomial.X (ULift.up j : formVars.{u} r) : Poly k (formVars.{u} r)) ^ a := by
  have h : noDifferenceCoefficients k r 1 = 1 := by
    change (freeDPBasis (Fin r × Fin 0) k).repr (1 : DividedPowerAlgebra k _) 0 = 1
    have h : freeDPMonomial (Fin r × Fin 0) k 0 = 1 := by simp [freeDPMonomial]
    rw [← h, ← freeDPBasis_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  change zeroTermCoefficients k r (Algebra.TensorProduct.includeLeft (R := k)
    (B := DividedPowerAlgebra k ((Fin r × Fin 0) →₀ k)) (MvPolynomial.X j) ^ a) = _
  rw [← map_pow]
  change zeroTermCoefficients k r ((MvPolynomial.X j ^ a) ⊗ₜ[k] (1 : DividedPowerAlgebra k _)) = _
  change noDifferenceCoefficients k r 1 • MvPolynomial.rename ULift.up (MvPolynomial.X j ^ a) = _
  rw [h, one_smul, map_pow, MvPolynomial.rename_X]

private theorem zeroFormsEquiv_coordinateZero (j : Fin r) :
    zeroFormsEquiv k r 0 (pdRawZeroCoordinate p k r j) =
      formsZeroEquiv k (formVars.{u} r) ((MvPolynomial.X (ULift.up j : formVars.{u} r) :
        Poly k (formVars.{u} r)) ^ p) := by
  let e := (zeroCopyEquiv k r).toLinearMap
  let w := (exteriorPower.zeroEquiv k (CopyModule k r ⦋0⦌)).symm 1
  have h : exteriorPower.map 0 e w = (exteriorPower.zeroEquiv k (formVars.{u} r → k)).symm 1 := by
    apply (exteriorPower.zeroEquiv k (formVars.{u} r → k)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (DFunLike.congr_fun (exteriorPower.zeroEquiv_naturality e) w).trans
      (LinearEquiv.apply_symm_apply _ _)
  rw [formsZeroEquiv_tmul]
  change zeroTermCoefficients k r (baseVar k r ⦋0⦌ j ^ p) ⊗ₜ[k] exteriorPower.map 0 e w = _
  rw [zeroTermCoefficients_X_pow, h]

private theorem zeroFormsEquiv_coordinateOne (j : Fin r) :
    zeroFormsEquiv k r 1 (pdRawOneCoordinate p k r j) =
      ((MvPolynomial.X (ULift.up j : formVars.{u} r) : Poly k (formVars.{u} r)) ^ (p-1)) •
        dX k (formVars.{u} r) (ULift.up j) := by
  change zeroTermCoefficients k r (baseVar k r ⦋0⦌ j ^ (p-1)) ⊗ₜ[k]
      exteriorPower.map 1 (zeroCopyEquiv k r).toLinearMap (pdCoordinateOne k r ⦋0⦌ (.inl j)) = _
  rw [zeroTermCoefficients_X_pow, pdCoordinateOne, exteriorPower_map_one,
    LinearEquiv.coe_coe, zeroCopyEquiv_basis]
  simp only [dX, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem pdRawVertical_coordinate (j : Fin r) :
    pdRawVertical k r ⦋0⦌ 0 (pdRawZeroCoordinate p k r j) =
      p • pdRawOneCoordinate p k r j := by
  apply (zeroFormsEquiv k r 1).injective
  rw [zeroFormsEquiv_d, map_nsmul, zeroFormsEquiv_coordinateZero, zeroFormsEquiv_coordinateOne]
  exact deRhamD_coordinate_pow k (formVars.{u} r) p (ULift.up j)

private def pdRawCoefficientUnit (n : ℕ) : pdRaw k r n →ₗ[k] pdTerm p k r n :=
  let u := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r n))
  { toFun := u.hom
    map_add' := map_add _
    map_smul' := fun a x => by
      change u (a • x) = a • u x
      have hA := Algebra.smul_def a x
      have hB := Algebra.smul_def a (u x : pdTerm p k r n)
      erw [hA, hB, map_mul]
      rfl }

private def pdFormsUnit (n : SimplexCategory) (i : ℕ) :
    pdRawForms k r n i →ₗ[k] (pdRow p k r i).obj n :=
  TensorProduct.map (pdRawCoefficientUnit p k r n.len) LinearMap.id

set_option backward.isDefEq.respectTransparency false in
private theorem pdFormsUnit_d (n : SimplexCategory) (i : ℕ) (x : pdRawForms k r n i) :
    pdVerticalD p k r n i (pdFormsUnit p k r n i x) =
      pdFormsUnit p k r n (i+1) (pdRawVertical k r n i x) := by
  let F := pdFormsUnit p k r n
  suffices h : (pdVerticalD p k r n i).hom.comp (F i) =
      (F (i+1)).comp (pdRawVertical k r n i) from DFunLike.congr_fun h x
  apply TensorProduct.ext'
  intro b w
  change pdRaw k r n.len at b
  change ⋀[k]^i (CopyModule k r n) at w
  let D := ∑ a : pdCoordinates r n.len, TensorProduct.map
    (pdPartial p k r n.len a) (wedgeOne k (CopyModule k r n) i (pdCoordinateOne k r n a))
  change D (F i (b ⊗ₜ[k] w)) = F (i+1) (pdRawVertical k r n i (b ⊗ₜ[k] w))
  simp only [D, F, pdRawVertical, pdFormsUnit, LinearMap.sum_apply, TensorProduct.map_tmul,
    map_sum]
  apply Finset.sum_congr rfl
  intro a _
  let w' := wedgeOne k (CopyModule k r n) i (pdCoordinateOne k r n a) w
  let R := pdRaw k r n.len
  let u := pdRawCoefficientUnit p k r n.len
  let d := pdRawPartial k r n.len a
  let f := pdPartial p k r n.len a
  change TensorProduct.map f (wedgeOne k (CopyModule k r n) i (pdCoordinateOne k r n a))
      (TensorProduct.map u LinearMap.id (b ⊗ₜ[k] w)) =
    TensorProduct.map u LinearMap.id (d b ⊗ₜ[k] w')
  rw [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.map_tmul,
    TensorProduct.map_tmul, LinearMap.id_apply]
  have h := principalCompletionLinearMap_unit k p (A := R) (B := R) d b
  change f (u b) = u (d b) at h
  exact congrArg (fun z => z ⊗ₜ[k] w') h

/-- 第 0 列で座標の p 乗を微分すると、一次の代表形式の p 倍を得る。 -/
private theorem pdVerticalD_coordinate (j : Fin r) :
    pdVerticalD p k r ⦋0⦌ 0 (pdFormsUnit p k r ⦋0⦌ 0 (pdRawZeroCoordinate p k r j)) =
      p • pdFormsUnit p k r ⦋0⦌ 1 (pdRawOneCoordinate p k r j) := by
  rw [pdFormsUnit_d, pdRawVertical_coordinate, map_nsmul]

end SerrePositivity.BhattScholze.Prismatic
