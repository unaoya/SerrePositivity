module

public import SerrePositivity.BhattScholze.DeltaRootFiniteTor
public import SerrePositivity.HomologicalAlgebra.KoszulTensorConeComparison
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # 有限根関係の係数付きKoszulホモロジー

係数環Aの任意加群Nに対し、B⊗_A N上の根関係Koszul複体を
既存の反復錐モデルとTorの自然比較で計算する。係数側(p,d)の正則性は不要。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (b : σ → A) {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s)
variable (N : Type u) [AddCommGroup N] [Module A N]

/-- 根関係の係数付きKoszulホモロジーと実商のTorとの既存比較の合成。 -/
def deltaRootFiniteKoszulCoefficientTorEquiv (i : ℕ) :
    (((koszulModuleFunctor (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
      (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N))).homology
      (-(i : ℤ))) ≃ₗ[MvPolynomial σ A]
      TorModule (MvPolynomial σ A) i (MvPolynomial σ A ⧸
        Ideal.span (Set.range fun j ↦ deltaRootRelationFamily (p := p) b (s j)))
        (TensorProduct A (MvPolynomial σ A) N) :=
  (((koszulModuleTorComparison (fun j ↦ deltaRootRelationFamily (p := p) b (s j))
    (deltaRootRelation_fin_isKoszulResolution b s hs) i).app
    (ModuleCat.of (MvPolynomial σ A)
      (TensorProduct A (MvPolynomial σ A) N))).symm.toLinearEquiv).trans
    (torModuleComm i (TensorProduct A (MvPolynomial σ A) N) _)

/-- 零次数ホモロジーは、実根関係商と係数加群の通常テンソル積。 -/
def deltaRootFiniteKoszulCoefficientHomologyZeroEquiv :
    (((koszulModuleFunctor (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
      (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N))).homology 0)
      ≃ₗ[MvPolynomial σ A] TensorProduct A (MvPolynomial σ A ⧸
        Ideal.span (Set.range fun j ↦ deltaRootRelationFamily (p := p) b (s j))) N :=
  ((deltaRootFiniteKoszulCoefficientTorEquiv b s hs N 0).trans
    (torModuleZeroEquiv (MvPolynomial σ A) _ _)).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A (MvPolynomial σ A) (MvPolynomial σ A) _ N)

include hs

/-- 任意係数加群を拡大した根関係Koszul複体の負次数ホモロジーは零加群。 -/
theorem deltaRootFiniteKoszulCoefficientHomology_subsingleton (i : ℕ) :
    Subsingleton (((koszulModuleFunctor
      (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
      (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N))).homology
      (-((i + 1 : ℕ) : ℤ))) := by
  let := deltaRootFiniteQuotient_tor_baseChange_subsingleton (p := p) b s N i
  exact (deltaRootFiniteKoszulCoefficientTorEquiv b s hs N (i + 1)).injective.subsingleton

/-- 同じ消滅を共通の圏論的IsZeroで供給する。 -/
theorem deltaRootFiniteKoszulCoefficientHomology_isZero (i : ℕ) :
    IsZero (((koszulModuleFunctor
      (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
      (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N))).homology
      (-((i + 1 : ℕ) : ℤ))) := by
  let := deltaRootFiniteKoszulCoefficientHomology_subsingleton (p := p) b s hs N i
  exact ModuleCat.isZero_of_subsingleton _

/-- 任意係数イデアルIの通常商を係数としても負次数Koszulホモロジーは零。 -/
theorem deltaRootFiniteKoszulQuotientCoefficientHomology_isZero
    (I : Ideal A) (i : ℕ) :
    IsZero (((koszulModuleFunctor
      (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
      (ModuleCat.of (MvPolynomial σ A)
        (TensorProduct A (MvPolynomial σ A) (A ⧸ I)))).homology
      (-((i + 1 : ℕ) : ℤ))) :=
  deltaRootFiniteKoszulCoefficientHomology_isZero b s hs (A ⧸ I) i

end SerrePositivity.BhattScholze
