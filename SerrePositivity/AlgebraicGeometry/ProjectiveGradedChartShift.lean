module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChart
public import SerrePositivity.AlgebraicGeometry.ProjectivePolynomialTwistFiniteness

/-!
概要：加群の次数のずらしと、標準開の係数図式の指定次数のずらしを比較する。
方針：分子の次数 (d + n c) - e と (d - e) + n c を同一視する。
規約：整数次数。標準開の制限は同じ通常の局所化写像で与えられる。
使われ方：有限自由加群の各成分を、多項式環の捻りへ射影する。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory

section General

variable {ι R M : Type*} [DecidableEq ι] [Fintype ι] [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (G : ℤ → Submodule R M)
variable [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) G]

/-- 多項式環の捻りに対する次数付き作用。 -/
theorem projectivePolynomialShiftSMul (e : ℤ) :
    SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (fun n ↦ AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)) (n - e)) := by
  refine ⟨?_⟩
  intro i j a m ha hm
  change a * m ∈ AddMonoidAlgebra.gradeBy R
    (projectivePolynomialDegree (ι := ι)) (i + j - e)
  simpa only [add_sub_assoc] using SetLike.mul_mem_graded ha hm

/-- 加群の次数をずらすことは、標準開で取る次数をずらすことに対応する。 -/
def projectiveGradedChartShiftIso (e d : ℤ)
    [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (fun n ↦ G (n - e))] :
    projectiveGradedModuleChartDiagram (ι := ι) (fun n ↦ G (n - e)) d ≅
      projectiveGradedModuleChartDiagram (ι := ι) G (d - e) := by
  let hq (T : Finset ι) :
      projectiveGradedAway (projectiveLaurentDenominator R T)
          (fun n : ℕ ↦ G (d + n • (T.card : ℤ) - e)) =
        projectiveGradedAway (projectiveLaurentDenominator R T)
          (fun n : ℕ ↦ G (d - e + n • (T.card : ℤ))) := by
    congr 1
    funext n
    congr 1
    omega
  refine NatIso.ofComponents (fun T ↦ (LinearEquiv.ofEq _ _ (hq T)).toModuleIso) ?_
  intro T U h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  rfl

end General

section Polynomial

variable {ι R : Type*} [LinearOrder ι] [Fintype ι] [CommRing R] [IsNoetherianRing R]

/-- 多項式環の次数をずらして得る標準開 Čech コホモロジーも有限生成。
これは Stacks 30.19.2 の Hⁱ の有限性に対応する射影 Čech 版の補題。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveShiftedPolynomialOrderedCechHomology_finite
    (e d : ℤ)
    [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (fun n ↦ AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)) (n - e))]
    (q : ℕ) :
    Module.Finite R ((orderedCechComplex (projectiveGradedModuleChartDiagram (ι := ι)
      (fun n ↦ AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)) (n - e))
      d)).homology q) := by
  let A := AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))
  let D := projectiveGradedModuleChartDiagram (ι := ι) (fun n ↦ A (n - e)) d
  let D' := projectiveGradedModuleChartDiagram (ι := ι) A (d - e)
  let eChart : D ≅ D' := projectiveGradedChartShiftIso (ι := ι) A e d
  let eComplex : orderedCechComplex D ≅ orderedCechComplex D' :=
    (orderedCechComplexFunctor (R := R) (ι := ι)).mapIso eChart
  let eHomology : (orderedCechComplex D).homology q ≅ (orderedCechComplex D').homology q :=
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) q).mapIso eComplex
  letI : Module.Finite R ((orderedCechComplex D').homology q) :=
    projectivePolynomialTwistOrderedCechHomology_finite (ι := ι) (d - e) q
  change Module.Finite R ((orderedCechComplex D).homology q)
  exact Module.Finite.of_surjective eHomology.inv.hom
    ((ModuleCat.epi_iff_surjective eHomology.inv).mp inferInstance)

end Polynomial

end SerrePositivity.AlgebraicGeometry
