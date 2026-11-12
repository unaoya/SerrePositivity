module

public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGrading

/-!
概要：自然数次数の標準開の次数零成分を、負の次数への延長なしで表示する。
方針：分母の第 k 冪の分子の次数が k 倍の分母の次数になることを使う。
規約：空の交叉も含む係数図式の各対象について述べる。
使われ方：各 IⁿM の斉次局所化の直和を、既存の標準開 Čech 図式へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry

variable {R M ι : Type*} [CommRing R] [DecidableEq ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (G : ℕ → Submodule R M)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 標準開の分母は、変数の個数の自然数次数に斉次。 -/
theorem projectiveLaurentDenominator_mem_natGrade (T : Finset ι) :
    projectiveLaurentDenominator R T ∈ MvPolynomial.homogeneousSubmodule ι R T.card := by
  rw [← projectivePolynomialGrade_natCast]
  exact projectiveLaurentDenominator_mem_polynomialGrade R T

/-- 分母を一回掛けると、次数零の分子の指定部分は次の段へ移る。 -/
theorem projectiveNatGradedChartZero_mul_denominator (T : Finset ι) (k : ℕ)
    (m : G (k * T.card)) :
    projectiveLaurentDenominator R T • m.val ∈ G ((k + 1) * T.card) := by
  have h := SetLike.GradedSMul.smul_mem
    (projectiveLaurentDenominator_mem_natGrade (R := R) T) m.property
  change projectiveLaurentDenominator R T • m.val ∈ G (T.card + k * T.card) at h
  simpa only [Nat.add_mul, one_mul, Nat.add_comm] using h

/-- 整数次数に延ばした次数零の分子は、元の自然数次数の分子と一致する。 -/
theorem projectiveNatGradedChartZero_submodule_eq (T : Finset ι) :
    projectiveGradedAway (projectiveLaurentDenominator R T)
        (fun k : ℕ ↦ projectiveNatGradingInt G (0 + k • (T.card : ℤ))) =
      projectiveGradedAway (projectiveLaurentDenominator R T)
        (fun k : ℕ ↦ G (k * T.card)) := by
  congr 1
  funext k
  rw [zero_add, nsmul_eq_mul, ← Nat.cast_mul, projectiveNatGradingInt_natCast]

/-- 自然数次数の標準開図式の次数零は、元の次数を持つ分子の局所化。 -/
def projectiveNatGradedChartZeroLinearEquiv (T : Finset ι) :
    (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T ≃ₗ[R]
      projectiveGradedAway (projectiveLaurentDenominator R T) (fun k : ℕ ↦ G (k * T.card)) :=
  LinearEquiv.ofEq _ _ (projectiveNatGradedChartZero_submodule_eq G T)

end SerrePositivity.AlgebraicGeometry
