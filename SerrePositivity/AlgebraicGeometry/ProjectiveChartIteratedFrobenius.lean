module

public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedIteratedFrobenius
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedAwayPowerMap
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradingPowerMap

/-!
概要：捻り零の標準開の反復 Frobenius を、同じ指定次数部分の自己写像にする。
方針：斉次分数の分子と分母をともに p^e 乗する。
規約：係数環の反復 Frobenius に関して半線形であり、零環も許す。
使われ方：厚化を経由した因子分解と、整数加群上の Frobenius 系の接続。
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
variable (G : ℕ → Submodule R A) [SetLike.GradedMonoid G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

local instance iteratedFrobeniusIntGradedAction :
    SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt G) := projectiveNatGradingIntSMul (ι := ι) G

/-- 捻り零の標準開の、実際の反復 Frobenius の半線形自己写像。 -/
def projectiveChartIteratedFrobenius (T : Finset ι) (e : ℕ) :
    (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T
      →ₛₗ[frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e)]
    (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T :=
  projectiveGradedAwayPowerMap (frobeniusDirectSystemMap R p hp hR 0 e (Nat.zero_le e))
    (frobeniusDirectSystemMap A p hp hA 0 e (Nat.zero_le e))
    (projectiveLaurentDenominator R T) (p ^ e)
    (by simp only [frobeniusDirectSystemMap_apply, Nat.sub_zero])
    (by intro r; simp only [frobeniusDirectSystemMap_apply, Nat.sub_zero, map_pow])
    (fun j ↦ projectiveNatGradingInt G (0 + j • (T.card : ℤ)))
    (fun j ↦ projectiveNatGradingInt G (0 + j • (T.card : ℤ)))
    (projectiveGradedChart_mul_denominator (projectiveNatGradingInt G) T 0)
    (by
      intro j x
      have hpiece : ∀ k a, a ∈ G k →
          frobeniusDirectSystemMap A p hp hA 0 e (Nat.zero_le e) a ∈ G (p ^ e * k) := by
        intro k a ha
        simpa only [frobeniusDirectSystemMap_apply, Nat.sub_zero, nsmul_eq_mul, Nat.cast_id]
          using SetLike.pow_mem_graded (p ^ e) ha
      have h := projectiveNatGradingInt_chart_map_mem_mul G G
          (frobeniusDirectSystemMap A p hp hA 0 e (Nat.zero_le e)).toAddMonoidHom
          (p ^ e) hpiece 0 (T.card : ℤ) j x
      change frobeniusDirectSystemMap A p hp hA 0 e (Nat.zero_le e) x.val ∈
        projectiveNatGradingInt G (((p ^ e : ℕ) : ℤ) * 0 + (p ^ e * j) • (T.card : ℤ)) at h
      simpa only [mul_zero] using h)

/-- 標準開の反復 Frobenius の値は、周囲の局所化環の p^e 乗。 -/
theorem projectiveChartIteratedFrobenius_val (T : Finset ι) (e : ℕ)
    (z : (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T) :
    (projectiveChartIteratedFrobenius G p hp hR hA T e z).val = z.val ^ (p ^ e) :=
  projectiveLocalizedPowerMap_frobenius p hp hR hA
    (projectiveLaurentDenominator R T) e _ _ z.val

end SerrePositivity.AlgebraicGeometry
