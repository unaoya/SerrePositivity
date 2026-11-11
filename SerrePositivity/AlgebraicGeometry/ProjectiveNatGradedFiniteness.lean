module

public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGrading
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedFiniteness

/-!
概要：自然数次数の有限生成多項式加群に対する標準開 Čech の有限性。
方針：負の次数を零に延ばし、整数次数の有限性を適用する。
規約：加群は多項式環と同じ宇宙に置く。
使われ方：自然数で次数付けた Proj の構造層へ有限性を渡す。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

universe u v

variable {R : Type u} {ι : Type v} [CommRing R] [IsNoetherianRing R]
variable [LinearOrder ι] [Fintype ι]
variable {M : Type (max u v)} [AddCommGroup M] [Module R M]
variable [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
variable (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [Module.Finite (MvPolynomial ι R) M]

/-- 自然数次数の有限生成多項式加群の狭義増加 Čech コホモロジーは有限生成。
これは Stacks 30.19.2 の Hⁱ の有限性に対応する射影 Čech 版の補題。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveNatGradedOrderedCechHomology_finite (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((orderedCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q) := by
  letI := projectiveNatGradingIntDecomposition G
  letI := projectiveNatGradingIntSMul (ι := ι) G
  exact projectiveGradedOrderedCechHomology_finite (ι := ι) (projectiveNatGradingInt G) d q

/-- 自然数次数の有限生成多項式加群の全タプル Čech コホモロジーは有限生成。
これは Stacks 30.19.2 の Hⁱ の有限性に対応する射影 Čech 版の補題。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveNatGradedFullCechHomology_finite (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q) := by
  letI := projectiveNatGradingIntDecomposition G
  letI := projectiveNatGradingIntSMul (ι := ι) G
  exact projectiveGradedFullCechHomology_finite (ι := ι) (projectiveNatGradingInt G) d q

end SerrePositivity.AlgebraicGeometry
