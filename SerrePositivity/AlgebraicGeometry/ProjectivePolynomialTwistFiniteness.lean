module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChart
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechComparison

/-!
概要：多項式環の捻りの標準開 Čech コホモロジーは、Noether 環上で有限生成。
方針：Laurent 単項式の図式との自然同型に Čech 関手とコホモロジーを適用する。
規約：整数次数。全タプル版と有界な狭義増加版の両方を扱う。
使われ方：有限斉次自由表示による一般の有限生成加群への降下帰納の入力。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory

variable {ι R : Type*} [LinearOrder ι] [Fintype ι] [CommRing R] [IsNoetherianRing R]

/-- 多項式環の捻りの全タプル Čech コホモロジーは有限生成。
これは Stacks 30.19.2 の Hⁱ の有限性に対応する射影 Čech 版の補題。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectivePolynomialTwistFullCechHomology_finite (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((fullCechComplex (projectiveGradedModuleChartDiagram (ι := ι)
        (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) d)).homology q) := by
  let e := (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) q).mapIso
    ((fullCechComplexFunctor (R := R) (ι := ι)).mapIso (projectivePolynomialTwistChartIso (ι := ι) R d))
  letI : Module.Finite R
      ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) q).obj
        ((fullCechComplexFunctor (R := R) (ι := ι)).obj
          (projectiveLaurentGradedChartDiagram (ι := ι) R d))) := by
    change Module.Finite R
      ((fullCechComplex (projectiveLaurentGradedChartDiagram (ι := ι) R d)).homology q)
    exact projectiveLaurentCechHomology_finite R d q
  exact Module.Finite.of_surjective e.inv.hom
    ((ModuleCat.epi_iff_surjective e.inv).mp inferInstance)

/-- 多項式環の捻りの狭義増加 Čech コホモロジーは有限生成。
これは Stacks 30.19.2 の Hⁱ の有限性に対応する射影 Čech 版の補題。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectivePolynomialTwistOrderedCechHomology_finite (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((orderedCechComplex (projectiveGradedModuleChartDiagram (ι := ι)
        (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) d)).homology q) := by
  let D := projectiveGradedModuleChartDiagram (ι := ι)
    (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) d
  let e := fullCechOrderedHomologyIso D q
  letI : Module.Finite R ((fullCechComplex D).homology q) :=
    projectivePolynomialTwistFullCechHomology_finite d q
  exact Module.Finite.of_surjective e.hom.hom
    ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance)

end SerrePositivity.AlgebraicGeometry
