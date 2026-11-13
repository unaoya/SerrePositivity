module

public import SerrePositivity.AlgebraicGeometry.ReesClosedLocalizedThickeningFrobenius
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedAwayPowerMap
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradingPowerMap

/-!
概要：実際の閉厚化を経由する Frobenius を、標準開の指定次数部分へ制限する。
方針：商環の次数制御と、分子・分母の冪の公式を合成する。
規約：厚さと分母の指数は p^e 倍、捻り d も p^e*d へ移る。
使われ方：閉厚化の Čech Frobenius の因子分解の各項。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [DecidableEq ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (G : ℕ → Submodule R A) [SetLike.GradedMonoid G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

local instance reesThickeningIntGradedAction (J : Ideal A) :
    SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt (projectiveRingQuotientGrade J G)) :=
  projectiveNatGradingIntSMul (ι := ι) (projectiveRingQuotientGrade J G)

/-- 厚化を経由する反復 Frobenius の、実際の標準開の指定次数部分の写像。 -/
def reesClosedChartThickeningFrobenius (n e : ℕ) (T : Finset ι) (d : ℤ) :
    (projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) d).obj T
      →ₛₗ[frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e)]
    (projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ (p ^ e * n)).map (algebraMap R A)) G)
      (((p ^ e : ℕ) : ℤ) * d)).obj T :=
  projectiveGradedAwayPowerMap (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e))
    (reesClosedRingThickeningFrobenius I p hp hA n e) (projectiveLaurentDenominator R T) (p ^ e)
    (reesClosedRingThickeningFrobenius_algebraMap I p hp hA n e (projectiveLaurentDenominator R T))
    (reesClosedRingThickeningFrobenius_scalar I p hp hR hA n e)
    (fun j ↦ projectiveNatGradingInt
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) (d + j • (T.card : ℤ)))
    (fun j ↦ projectiveNatGradingInt
      (projectiveRingQuotientGrade ((I ^ (p ^ e * n)).map (algebraMap R A)) G)
        (((p ^ e : ℕ) : ℤ) * d + j • (T.card : ℤ)))
    (projectiveGradedChart_mul_denominator
      (projectiveNatGradingInt (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)) T d)
    (fun j x ↦ projectiveNatGradingInt_chart_map_mem_mul _ _
      (reesClosedRingThickeningFrobenius I p hp hA n e).toAddMonoidHom (p ^ e)
      (reesClosedRingThickeningFrobenius_preservesPiece I p hp hA G n e) d (T.card : ℤ) j x)

/-- 指定次数の厚化 Frobenius は、周囲の実際の局所化の写像の制限。 -/
theorem reesClosedChartThickeningFrobenius_val (n e : ℕ) (T : Finset ι) (d : ℤ)
    (z : (projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) d).obj T) :
    (reesClosedChartThickeningFrobenius I G p hp hR hA n e T d z).val =
      reesClosedLocalizedThickeningFrobenius I p hp hR hA
        (projectiveLaurentDenominator R T) n e z.val := rfl

end SerrePositivity.AlgebraicGeometry
