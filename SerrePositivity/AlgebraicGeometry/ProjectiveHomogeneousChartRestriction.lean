module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousChart
public import SerrePositivity.AlgebraicGeometry.ProjectiveScalarRestrictionComparison

/-!
概要：次数零チャートの加群の制限と、Proj の標準開の環の制限を比較する。
方針：通常の局所化への単射で比較し、係数環の変更と制限の可換性を使う。
規約：標準開の分母は、次数一の変数の像の積。
使われ方：有限性を示した Čech の余境界を、構造層の切断の余境界に対応させる。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory

universe u v

variable {R : Type u} {ι : Type v} {S : Type (max u v)}
variable [CommRing R] [CommRing S] [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable (G : ℕ → Submodule R S) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance (f : S) : Module R (HomogeneousLocalization.Away G f) :=
  projectiveHomogeneousAwayModule G f

/-- 次数零チャートの比較と通常の加群局所化への写像は可換。 -/
theorem projectiveHomogeneousChartLinearEquiv_toModule (T : Finset ι)
    (z : (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T) :
    projectiveHomogeneousAwayToModule G
        (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T))
        (projectiveHomogeneousChartLinearEquiv (ι := ι) G T z) =
      projectiveScalarModuleAwayLinearEquiv (R := R) (projectiveLaurentDenominator R T) z.val := by
  change (projectiveHomogeneousAwayLinearEquiv G
    (projectivePolynomialDenominatorImage_mem G T)
    (projectiveHomogeneousChartLinearEquiv (ι := ι) G T z)).val = _
  simp only [projectiveHomogeneousChartLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, projectiveScalarGradedAwayLinearEquiv_val]
  rfl

/-- 標準開を狭めるときの次数零斉次局所化の環準同型。 -/
def projectiveHomogeneousChartRestrictionRingHom {T U : Finset ι} (h : T ⊆ U) :
    HomogeneousLocalization.Away G
        (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T)) →+*
      HomogeneousLocalization.Away G
        (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R U)) :=
  HomogeneousLocalization.awayMap G (projectivePolynomialDenominatorImage_mem G (U \ T))
    (by rw [← map_mul, projectiveLaurentDenominator_sdiff R h])

/-- 局所化加群から移したチャートの制限は、斉次局所化の環の制限と一致する。 -/
theorem projectiveHomogeneousChartDiagram_map {T U : Finset ι} (h : T ⊆ U)
    (z : (projectiveHomogeneousChartDiagram (ι := ι) G).obj T) :
    ((projectiveHomogeneousChartDiagram (ι := ι) G).map (homOfLE h)).hom z =
      projectiveHomogeneousChartRestrictionRingHom G h z := by
  have hL : Function.Injective (projectiveHomogeneousAwayToModule G
      (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R U))) :=
    (projectiveSelfLocalizationLinearEquiv (R := R)
      (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R U))).symm.injective.comp
        (HomogeneousLocalization.val_injective _)
  apply hL
  change projectiveHomogeneousAwayToModule G _
      (projectiveHomogeneousChartLinearEquiv (ι := ι) G U
        (((projectiveNatGradedModuleChartDiagram (ι := ι) G 0).map (homOfLE h)).hom
          ((projectiveHomogeneousChartLinearEquiv (ι := ι) G T).symm z))) = _
  rw [projectiveHomogeneousChartLinearEquiv_toModule,
    projectiveHomogeneousChartRestrictionRingHom,
    projectiveHomogeneousAwayToModule_restriction G (projectivePolynomialDenominatorImage_mem G T)]
  change projectiveScalarModuleAwayLinearEquiv (R := R) (projectiveLaurentDenominator R U)
      (projectiveModuleAwayRestriction
        (show projectiveLaurentDenominator R T ∣ projectiveLaurentDenominator R U from
          ⟨_, (projectiveLaurentDenominator_sdiff R h).symm⟩)
        ((projectiveHomogeneousChartLinearEquiv (ι := ι) G T).symm z).val) = _
  rw [projectiveScalarModuleAwayLinearEquiv_restriction
    (projectiveLaurentDenominator_sdiff R h).symm]
  congr 1
  simpa only [LinearEquiv.apply_symm_apply] using
    (projectiveHomogeneousChartLinearEquiv_toModule G T
      ((projectiveHomogeneousChartLinearEquiv (ι := ι) G T).symm z)).symm

end SerrePositivity.AlgebraicGeometry
