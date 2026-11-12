module

public import SerrePositivity.AlgebraicGeometry.GradedOriginalProjCechMaps
public import SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeFrobeniusEvaluation

/-!
概要：共通基底で計算した Frobenius を、各段の元の Proj の切断へ戻す。
方針：正規化した次数の局所化の p 乗の計算と、carrier の同型の乗法性を使う。
規約：各段の基底環を共通基底と同一視せず、元の Proj を使う。
使われ方：動く基底の filtered colimit と実際の Frobenius の整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {R S : Type u} {σ : Type v} {ι : Type}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [SetLike σ S] [AddSubgroupClass σ S] [SMulMemClass σ R S]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]
variable (p : ℕ) (hp : p.Prime) [ExpChar R p] (hz : (p : S) = 0)
variable (G : ℕ → σ) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 共通基底のチャートの Frobenius は、元の grading の斉次局所化の p 乗と一致。 -/
theorem gradedOriginalChartLinearEquiv_frobenius (T : Finset ι)
    (z : (projectiveNatGradedModuleChartDiagram (ι := ι)
      (gradedScalarComponents (R := R) G) 0).obj T) :
    (gradedScalarAwayIso (R := R) G _).hom.hom
      (projectiveHomogeneousChartLinearEquiv (gradedScalarComponents (R := R) G) T
        (projectiveNatGradedChartZeroFrobenius p hp hz (gradedScalarComponents (R := R) G) T z)) =
    ((gradedScalarAwayIso (R := R) G _).hom.hom
      (projectiveHomogeneousChartLinearEquiv (gradedScalarComponents (R := R) G) T z)) ^ p := by
  rw [projectiveHomogeneousChartLinearEquiv_frobenius, map_pow]

/-- 共通基底での計算を元の Proj の切断へ戻しても、Frobenius は実際の p 乗。 -/
theorem gradedOriginalProjNativeChart_frobenius (T : Finset ι)
    (z : (projectiveNatGradedModuleChartDiagram (ι := ι)
      (gradedScalarComponents (R := R) G) 0).obj T) :
    (Proj.awayToSection G (algebraMap (MvPolynomial ι R) S
      (projectiveLaurentDenominator R T))).hom
      ((gradedScalarAwayIso (R := R) G _).hom.hom
        (projectiveHomogeneousChartLinearEquiv (gradedScalarComponents (R := R) G) T
          (projectiveNatGradedChartZeroFrobenius p hp hz
            (gradedScalarComponents (R := R) G) T z))) =
    ((Proj.awayToSection G (algebraMap (MvPolynomial ι R) S
      (projectiveLaurentDenominator R T))).hom
      ((gradedScalarAwayIso (R := R) G _).hom.hom
        (projectiveHomogeneousChartLinearEquiv (gradedScalarComponents (R := R) G) T z))) ^ p := by
  rw [gradedOriginalChartLinearEquiv_frobenius, map_pow]

end SerrePositivity.AlgebraicGeometry
