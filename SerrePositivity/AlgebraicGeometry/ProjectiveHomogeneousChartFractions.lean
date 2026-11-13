module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousChartRestriction

/-!
概要：次数零チャートの線形同型を、任意の斉次分数で計算する。
方針：通常の加群局所化への単射で比較し、分子と分母が一致することを使う。
規約：チャートの元の表示を入力し、分母の非零性は要求しない。
使われ方：次数を保つ係数写像と実際の Proj の切断の引き戻しの照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R S : Type u} {ι : Type} [CommRing R] [CommRing S]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable (G : ℕ → Submodule R S) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 次数零のチャートの線形同型は、分子と分母の冪を保つ。 -/
theorem projectiveHomogeneousChartLinearEquiv_fraction (T : Finset ι) (n : ℕ)
    (m : S) (hm : m ∈ G (n • T.card))
    (z : (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T)
    (hz : z.val = LocalizedModule.mk m (projDenominator (projectiveLaurentDenominator R T) n)) :
    projectiveHomogeneousChartLinearEquiv G T z =
      HomogeneousLocalization.Away.mk G (projectivePolynomialDenominatorImage_mem G T) n m hm := by
  have hi : Function.Injective (projectiveHomogeneousAwayToModule G
      (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T))) :=
    (projectiveSelfLocalizationLinearEquiv (R := R) _).symm.injective.comp
      (HomogeneousLocalization.val_injective _)
  apply hi
  rw [projectiveHomogeneousChartLinearEquiv_toModule, hz,
    projectiveScalarModuleAwayLinearEquiv_mk, projectiveHomogeneousAwayToModule_mk]

/-- 斉次分数での表示から、元の多項式加群の局所化での表示を取り戻す。 -/
theorem projectiveHomogeneousChartLinearEquiv_fraction_reflect (T : Finset ι) (n : ℕ)
    (m : S) (hm : m ∈ G (n • T.card))
    (z : (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T)
    (hz : projectiveHomogeneousChartLinearEquiv G T z =
      HomogeneousLocalization.Away.mk G (projectivePolynomialDenominatorImage_mem G T) n m hm) :
    z.val = LocalizedModule.mk m (projDenominator (projectiveLaurentDenominator R T) n) := by
  apply (projectiveScalarModuleAwayLinearEquiv (R := R)
    (S := S) (projectiveLaurentDenominator R T)).injective
  rw [← projectiveHomogeneousChartLinearEquiv_toModule, hz,
    projectiveHomogeneousAwayToModule_mk, projectiveScalarModuleAwayLinearEquiv_mk]

end SerrePositivity.AlgebraicGeometry
