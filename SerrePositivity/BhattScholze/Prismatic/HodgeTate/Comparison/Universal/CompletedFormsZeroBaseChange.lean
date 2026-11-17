module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CompletedPolynomialZeroBaseChange
public import SerrePositivity.CommutativeAlgebra.DeRham.CartierWeight
public import SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import all SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierWeight
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierWeight

/-!
# 元の完備形式のpで零化された係数への通常底変換

## 概要
元の完備微分形式の通常係数拡大を、同じ単項式・外積の基底を保って通常形式へ同定する。

## 方針
元の完備多項式係数の同型と、同じ外冪基底の係数拡大をテンソルの結合で合成する。

## 規約
平坦性は仮定しない。元の完備化単位の基底ベクトルの像を明示する。

## 使われ方
元の被覆上の形式の同型と、元の標準HT写像の零次・一次の照合。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open SerrePositivity.DeRham SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (k l T : Type u) [CommRing k] [CommRing l] [Algebra k l]
variable [Fintype T] [LinearOrder T] (p : ℕ) (hp : (p : l) = 0)
include hp

/-- 元の完備形式の通常係数拡大は、同じ元の多項式・外積基底の単位を保つ線形同型を持つ。 -/
theorem exists_completedFormsZeroBaseChangeEquiv (i : ℕ) :
    ∃ e : (l ⊗[k] completedForms k T p i) ≃ₗ[l] forms l T i,
      ∀ v : (T →₀ ℕ) × Set.powersetCard T i,
        e ((1 : l) ⊗ₜ[k] completedFormsUnit k T p i (polynomialFormsBasis k T i v)) =
          polynomialFormsBasis l T i v := by
  let C := completedPoly k T p
  let E := ⋀[k]^i (T → k)
  let E' := ⋀[l]^i (T → l)
  let b := (Pi.basisFun k T).exteriorPower i
  let b' := (Pi.basisFun l T).exteriorPower i
  let ex : (l ⊗[k] E) ≃ₗ[l] E' := (b.baseChange l).equiv b' (Equiv.refl _)
  have hx (v : Set.powersetCard T i) : ex ((1 : l) ⊗ₜ[k] b v) = b' v := by
    simpa only [ex, Module.Basis.baseChange_apply, Equiv.refl_apply] using
      Module.Basis.equiv_apply (b.baseChange l) v b' (Equiv.refl _)
  obtain ⟨ec, hc⟩ := exists_completedPolyZeroBaseChangeEquiv k l T p hp
  let e := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl l l)
      (completedFormsCoeffEquiv k T p i) ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.assoc k k l l C E).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr ec.toLinearEquiv (LinearEquiv.refl k E) ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k l l (MvPolynomial T l) E).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl l (MvPolynomial T l)) ex
  refine ⟨e, ?_⟩
  intro v
  rw [polynomialFormsBasis, Module.Basis.tensorProduct_apply', MvPolynomial.coe_basisMonomials]
  simp only [e, LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, completedFormsCoeffEquiv_unit_tmul,
    TensorProduct.AlgebraTensorModule.assoc_symm_tmul]
  change (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl l (MvPolynomial T l)) ex)
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange k l l (MvPolynomial T l) E).symm
      (ec ((1 : l) ⊗ₜ[k] principalCompletionUnitRingHom _ _ (MvPolynomial.monomial v.1 1)) ⊗ₜ[k] b v.2)) = _
  rw [hc, one_smul, MvPolynomial.map_monomial, map_one,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, hx]
  rw [polynomialFormsBasis, Module.Basis.tensorProduct_apply', MvPolynomial.coe_basisMonomials]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
