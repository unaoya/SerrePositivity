module

public import SerrePositivity.CommutativeAlgebra.DeRham.CartierCoordinateIntegral
public import SerrePositivity.CommutativeAlgebra.DeRham.ExteriorCoordinateProjection
public import SerrePositivity.CommutativeAlgebra.DeRham.ExteriorTensorContraction
public import Mathlib.Algebra.Homology.Homotopy
import all SerrePositivity.CommutativeAlgebra.DeRham.Polynomial
import all SerrePositivity.CommutativeAlgebra.DeRham.ExteriorTensorContraction

/-!
# 多変数 Cartier の一座標のホモトピー

## 概要
一つの座標で重みが p の倍数でない成分を積分によって収縮する。

## 方針
座標積分と外冪の内部積をテンソルし、微分との反交換子を計算する。

## 規約
係数環は体。偏微分の係数が消える成分を残す。

## 使われ方
有限多変数の inverse Cartier。
-/

public noncomputable section

open CategoryTheory Homotopy
open scoped TensorProduct

universe u

namespace SerrePositivity.DeRham

variable (K T : Type u) [Field K] [Fintype T] [DecidableEq T]

local notation "C" => deRhamComplex K T
local notation "M" => (T → K)
local notation "b" => Pi.basisFun K T

private def H (s : T) (i j : ℕ) (h : (ComplexShape.up ℕ).Rel j i) : (C).X i ⟶ (C).X j := by
  have hi : j + 1 = i := h
  subst i
  exact ModuleCat.ofHom (tensorExteriorH b (cartierCoordinateIntegral K s) s j)

/-- 差を一座標の収縮で表す Cartier 射影。 -/
def cartierCoordinateEval (s : T) : C ⟶ C :=
  𝟙 C - nullHomotopicMap' (H K T s)

/-- 一座標の Cartier 射影は鎖の恒等写像とホモトピック。 -/
def cartierCoordinateEvalHomotopy (s : T) : Homotopy (cartierCoordinateEval K T s) (𝟙 C) := by
  let h := (nullHomotopy' («C» := deRhamComplex K T) (D := deRhamComplex K T) (H K T s)).smul (-1 : ℤ)
  simpa only [cartierCoordinateEval, neg_one_zsmul, zsmul_zero, sub_eq_add_neg, add_zero] using
    (Homotopy.refl (𝟙 C)).add h

private theorem d_eq (j : ℕ) : (C).d j (j + 1) = ModuleCat.ofHom
    (tensorExteriorD b (fun t => (MvPolynomial.pderiv (R := K) t).toLinearMap) j) := by
  dsimp only [deRhamComplex, CochainComplex.of]
  rw [CochainComplex.of_d]
  congr 1
  unfold deRhamDLinear tensorExteriorD basisWedgeOne
  simp only [Pi.basisFun_apply]

/-- 零次の一座標射影は、指定した指数が係数環で消える項を残す。 -/
theorem cartierCoordinateEval_zero (s : T) :
    (cartierCoordinateEval K T s).f 0 = ModuleCat.ofHom
      (TensorProduct.map (cartierCoordinateProjection K s 0) LinearMap.id) := by
  dsimp only [cartierCoordinateEval]
  rw [HomologicalComplex.sub_f_apply,
    nullHomotopicMap'_f_of_not_rel_right (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
      (fun i => show ¬ (ComplexShape.up ℕ).Rel i 0 from by change ¬ i + 1 = 0; omega), d_eq]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f w
  let x : forms K T 0 := f ⊗ₜ[K] w
  let D := fun (t : T) => (MvPolynomial.pderiv (R := K) t).toLinearMap
  let I := cartierCoordinateIntegral K s
  let P := cartierCoordinateProjection K s 0
  change x - tensorExteriorH b I s 0 (tensorExteriorD b D 0 x) = P f ⊗ₜ[K] w
  have h := DFunLike.congr_fun (tensorExteriorH_D_zero b D I s) x
  rw [show I.comp (D s) = LinearMap.id - P from cartierCoordinateIntegral_partial K s] at h
  change tensorExteriorH b I s 0 (tensorExteriorD b D 0 x) = (f-P f) ⊗ₜ[K] w at h
  rw [h, TensorProduct.sub_tmul]
  abel

/-- 正次数では外積に指定座標があるかで係数の Cartier 射影を使い分ける。 -/
theorem cartierCoordinateEval_succ (s : T) (j : ℕ) :
    (cartierCoordinateEval K T s).f (j + 1) = ModuleCat.ofHom
      (TensorProduct.map (cartierCoordinateProjection K s 0)
        (exteriorPower.map (j + 1) (exteriorCoordinateProjection ((b).coord s) (b s))) +
       TensorProduct.map (cartierCoordinateProjection K s 1)
        ((basisWedgeOne b j s).comp (basisContract b j s))) := by
  dsimp only [cartierCoordinateEval]
  rw [HomologicalComplex.sub_f_apply,
    nullHomotopicMap'_f (show (ComplexShape.up ℕ).Rel j (j + 1) from rfl)
      (show (ComplexShape.up ℕ).Rel (j + 1) (j + 2) from rfl), d_eq, d_eq]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f w
  let x : forms K T (j + 1) := f ⊗ₜ[K] w
  let D := fun (t : T) => (MvPolynomial.pderiv (R := K) t).toLinearMap
  let I := cartierCoordinateIntegral K s
  let P₀ := cartierCoordinateProjection K s 0
  let P₁ := cartierCoordinateProjection K s 1
  let W := (basisWedgeOne b j s).comp (basisContract b j s)
  let y := tensorExteriorD b D j (tensorExteriorH b I s j x)
  let z := tensorExteriorH b I s (j + 1) (tensorExteriorD b D (j + 1) x)
  have h := DFunLike.congr_fun (tensorExteriorD_H b D I s
    (fun t h => cartierCoordinatePartial_integral_comm K (Ne.symm h)) j) x
  rw [show (D s).comp I = LinearMap.id - P₁ from cartierCoordinatePartial_integral K s,
    show I.comp (D s) = LinearMap.id - P₀ from cartierCoordinateIntegral_partial K s] at h
  have e : (LinearMap.id - P₁) - (LinearMap.id - P₀) = P₀ - P₁ := by abel
  rw [e] at h
  change y + z = (f - P₀ f) ⊗ₜ[K] w + (P₀ f - P₁ f) ⊗ₜ[K] W w at h
  change x - (z + y) = P₀ f ⊗ₜ[K] exteriorPower.map (j + 1)
      (exteriorCoordinateProjection ((b).coord s) (b s)) w + P₁ f ⊗ₜ[K] W w
  rw [add_comm z y, h, exteriorPower_map_coordinateProjection]
  change f ⊗ₜ[K] w - ((f - P₀ f) ⊗ₜ[K] w + (P₀ f - P₁ f) ⊗ₜ[K] W w) =
    P₀ f ⊗ₜ[K] (w - W w) + P₁ f ⊗ₜ[K] W w
  rw [TensorProduct.sub_tmul, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  abel

end SerrePositivity.DeRham
