module

public import SerrePositivity.CommutativeAlgebra.DeRham.PolynomialCompletion

/-!
# 完備微分形式の外積

## 概要
完備微分形式の外積を定義し、完備化単位が外積を保つことを示す。

## 方針
テンソル積の係数拡大を一度に行い、完備した係数環の積と外冪の積をテンソルする。

## 規約
斉次な外冪の積の次数は左と右の次数の和。

## 使われ方
完備 de Rham 複体の積と Hodge–Tate 写像。
-/

public section
noncomputable section

universe u

open scoped TensorProduct

namespace SerrePositivity.DeRham

variable (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T] (p : ℕ)

local notation "E[" i "]" => (⋀[k]^i (T → k))
local notation "P" => Poly k T
local notation "Q" => completedPoly k T p

private def coeffEquiv (i : ℕ) :
    completedForms k T p i ≃ₗ[Q] Q ⊗[k] E[i] :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange k P Q Q E[i]

private def completeCoeff : P →ₗ[k] Q := IsScalarTower.toAlgHom k P Q |>.toLinearMap

private theorem coeffEquiv_unit (i : ℕ) (ω : forms k T i) :
    coeffEquiv k T p i (completedFormsUnit k T p i ω) =
      TensorProduct.map (completeCoeff k T p) (LinearMap.id : E[i] →ₗ[k] E[i]) ω := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | tmul f v =>
    change coeffEquiv k T p i (1 ⊗ₜ[P] (f ⊗ₜ[k] v)) = _
    rw [coeffEquiv, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, TensorProduct.map_tmul]
    simp only [Algebra.smul_def, mul_one, completeCoeff, AlgHom.toLinearMap_apply,
      IsScalarTower.toAlgHom_apply, LinearMap.id_apply]

/-- 概要：完備化した多項式の微分形式上の外積。
方針：完備多項式環の積と外冪の積をテンソルする。
規約：係数拡大をまとめる標準同型で元の定義域に戻す。
使われ方：完備 de Rham 複体と Hodge–Tate 写像。 -/
def completedWedge {i j : ℕ} (ω : completedForms k T p i) (η : completedForms k T p j) :
    completedForms k T p (i + j) :=
  (coeffEquiv k T p (i + j)).symm
    (TensorProduct.map₂ (LinearMap.mul k Q) (exteriorWedge k (T → k) i j)
      (coeffEquiv k T p i ω) (coeffEquiv k T p j η))

private theorem completeCoeff_wedge {i j : ℕ} (ω : forms k T i) (η : forms k T j) :
    TensorProduct.map (completeCoeff k T p) (LinearMap.id : E[i + j] →ₗ[k] E[i + j])
      (wedge k T ω η) =
    TensorProduct.map₂ (LinearMap.mul k Q) (exteriorWedge k (T → k) i j)
      (TensorProduct.map (completeCoeff k T p) (LinearMap.id : E[i] →ₗ[k] E[i]) ω)
      (TensorProduct.map (completeCoeff k T p) (LinearMap.id : E[j] →ₗ[k] E[j]) η) := by
  unfold wedge
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul f a =>
    induction η using TensorProduct.inductionOn with
    | add b c hb hc => simp only [map_add, hb, hc]
    | tmul g b =>
      simp only [TensorProduct.map₂_apply_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
      change (IsScalarTower.toAlgHom k P Q (f * g)) ⊗ₜ[k] exteriorWedge k (T → k) i j a b =
        (IsScalarTower.toAlgHom k P Q f * IsScalarTower.toAlgHom k P Q g) ⊗ₜ[k]
          exteriorWedge k (T → k) i j a b
      rw [map_mul]

/-- 多項式形式からの完備化単位は外積と可換。 -/
theorem completedWedge_unit {i j : ℕ} (ω : forms k T i) (η : forms k T j) :
    completedWedge k T p (completedFormsUnit k T p i ω) (completedFormsUnit k T p j η) =
      completedFormsUnit k T p (i + j) (wedge k T ω η) := by
  apply (coeffEquiv k T p (i + j)).injective
  rw [completedWedge, LinearEquiv.apply_symm_apply, coeffEquiv_unit, coeffEquiv_unit,
    coeffEquiv_unit, completeCoeff_wedge]

end SerrePositivity.DeRham
