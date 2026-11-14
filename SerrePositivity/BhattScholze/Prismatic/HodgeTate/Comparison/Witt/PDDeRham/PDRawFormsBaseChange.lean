module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawBaseChangeLinear
public import SerrePositivity.CommutativeAlgebra.DeRham.ExteriorCoefficientMap
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
import all SerrePositivity.CommutativeAlgebra.DeRham.ExteriorCoefficientMap

/-!
# 未完備の分冪微分形式の底変換

## 概要
未完備の分冪係数と外冪のテンソルに対する係数変更が、通常の底変換を表す。

## 方針
分冪単項式と外冪の基底からテンソル積の基底を作り、係数変更が基底を保つことを使う。

## 規約
係数環の射は任意。頂点と外冪の添字は係数変更の前後で固定する。

## 使われ方
BS 著者版 Theorem 6.4 で導来完備底変換を計算するための自由模型。
-/

public noncomputable section

open SerrePositivity.DeRham
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1500

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (r n j : ℕ)

local notation "I" => (Fin r × Fin (n + 1))

/-- 未完備の分冪形式の次数別の半線形な係数変更。 -/
def pdRawFormsCoefficientMap :
    (pdRaw A r n ⊗[A] (⋀[A]^j (I →₀ A))) →ₛₗ[algebraMap A B]
      (pdRaw B r n ⊗[B] (⋀[B]^j (I →₀ B))) :=
  TensorProduct.map
    { toFun := pdRawCoefficients A B r n
      map_add' := map_add _
      map_smul' := fun a x =>
        ((pdRawCoefficients A B r n).toLinearMap.map_smul a x).trans
          (algebraMap_smul B a (pdRawCoefficients A B r n x)).symm }
    (exteriorPowerCoefficients A B I j)

/-- 同じ係数変更を、係数制限した線形写像として読む。 -/
def pdRawFormsCoefficientLinear :
    (pdRaw A r n ⊗[A] (⋀[A]^j (I →₀ A))) →ₗ[A]
      (pdRaw B r n ⊗[B] (⋀[B]^j (I →₀ B))) where
  toFun := pdRawFormsCoefficientMap A B r n j
  map_add' := map_add _
  map_smul' a x :=
    ((pdRawFormsCoefficientMap A B r n j).map_smulₛₗ a x).trans
      (algebraMap_smul B a (pdRawFormsCoefficientMap A B r n j x))

private theorem exteriorBasis_coefficients [LinearOrder I] (s : Set.powersetCard I j) :
    exteriorPowerCoefficients A B I j (((Finsupp.basisSingleOne (R := A)).exteriorPower j) s) =
      ((Finsupp.basisSingleOne (R := B)).exteriorPower j) s := by
  rw [exteriorPower.basis_apply, exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  rw [show ∀ v : Fin j → I →₀ A, exteriorPowerCoefficients A B I j
    (exteriorPower.ιMulti A j v) = exteriorPower.ιMulti B j (freeCoefficientMap A B I ∘ v)
      from exteriorPowerCoefficientMap_ιMulti A B I]
  congr 1
  funext i
  apply freeCoefficientMap_single

/-- 各未完備項の係数変更は、環の平坦性を仮定せずテンソル底変換を表す。 -/
theorem pdRawFormsCoefficientMap_isBaseChange :
    IsBaseChange B (pdRawFormsCoefficientLinear A B r n j) := by
  let e := Fintype.equivFin I
  let : LinearOrder I := LinearOrder.lift' e e.injective
  let b₀ : Module.Basis I A (I →₀ A) := Finsupp.basisSingleOne
  let c₀ : Module.Basis I B (I →₀ B) := Finsupp.basisSingleOne
  let b := (pdRawBasis A r n).tensorProduct (b₀.exteriorPower j)
  let c := (pdRawBasis B r n).tensorProduct (c₀.exteriorPower j)
  let v := (b.baseChange B).repr.trans c.repr.symm
  apply IsBaseChange.of_equiv v
  let f := (v.toLinearMap.restrictScalars A).comp (TensorProduct.mk A B _ 1)
  have hf : f = pdRawFormsCoefficientLinear A B r n j := by
    apply b.ext
    intro i
    change v (1 ⊗ₜ[A] b i) = pdRawFormsCoefficientMap A B r n j (b i)
    rw [← Module.Basis.baseChange_apply]
    have hv : v ((b.baseChange B) i) = c i := by
      change c.repr.symm ((b.baseChange B).repr ((b.baseChange B) i)) = c i
      rw [Module.Basis.repr_self, Module.Basis.repr_symm_single, one_smul]
    change v ((b.baseChange B) i) = pdRawFormsCoefficientMap A B r n j (b i)
    rw [hv]
    change (pdRawBasis B r n).tensorProduct (c₀.exteriorPower j) i =
      pdRawFormsCoefficientMap A B r n j ((pdRawBasis A r n).tensorProduct (b₀.exteriorPower j) i)
    rw [Module.Basis.tensorProduct_apply', Module.Basis.tensorProduct_apply']
    rw [pdRawFormsCoefficientMap, TensorProduct.map_tmul]
    change _ = pdRawCoefficients A B r n ((pdRawBasis A r n) i.1) ⊗ₜ[B]
      exteriorPowerCoefficients A B I j ((b₀.exteriorPower j) i.2)
    rw [pdRawCoefficients_basis, exteriorBasis_coefficients]
  intro x
  change f x = _
  exact DFunLike.congr_fun hf x

end SerrePositivity.BhattScholze.Prismatic
