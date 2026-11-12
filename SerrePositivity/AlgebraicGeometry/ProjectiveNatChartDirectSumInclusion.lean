module

public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartDirectSum
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartDirectSumInclusion

/-!
概要：自然数次数の標準開 Čech 直和比較は、各成分の包含を保つ。
方針：零延長による整数次数の比較と、既存の包含の公式を使う。
規約：直和同値は自然数の Proj 次数を保ち、外部の直和添字を固定する。
使われ方：各 IⁿM の包含を Rees の Čech コホモロジーの直和比較へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped DirectSum

universe u
variable {R : Type u} [CommRing R] {ι κ : Type} [DecidableEq ι] [Fintype ι] [DecidableEq κ]
variable {F : κ → Type u} [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
variable [∀ i, Module (MvPolynomial ι R) (F i)]
variable [∀ i, IsScalarTower R (MvPolynomial ι R) (F i)]
variable {N : Type u} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable (G : ∀ i, ℕ → Submodule R (F i)) (H : ℕ → Submodule R N)
variable (e : (⨁ i, F i) ≃ₗ[MvPolynomial ι R] N)
variable (he : ∀ d x, e x ∈ H d ↔ x ∈ projectiveDirectSumSubmodule (fun i ↦ G i d))

variable [∀ i, SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) (G i)]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]

/-- 自然数次数で、各成分の包含を標準開の図式へ渡す。 -/
def projectiveNatGradedModuleChartInclusion (d : ℤ) (i : κ) :=
  letI : ∀ j, SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt (G j)) := fun j ↦ projectiveNatGradingIntSMul (ι := ι) (G j)
  letI := projectiveNatGradingIntSMul (ι := ι) H
  projectiveGradedModuleChartInclusion (R := R) (ι := ι) (κ := κ) (F := F) (N := N)
    (fun j ↦ projectiveNatGradingInt (G j)) (projectiveNatGradingInt H) e
    (projectiveNatGradingInt_directSum_mem_iff G H e he) d i

/-- 自然数次数の Čech 直和比較は各成分からの包含を保つ。
原典 Stacks 30.20.1 の Hⁱ の直和比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveNatGradedModuleChartDirectSumCechHomologyIso_inclusion
    (d : ℤ) (q : ℕ) (i : κ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (fullCechComplexMap (projectiveNatGradedModuleChartInclusion G H e he d i)) ≫
      (projectiveNatGradedModuleChartDirectSumCechHomologyIso G H e he d q).hom =
    ModuleCat.ofHom (DirectSum.lof R κ
      (fun j ↦ (fullCechComplex
        (projectiveNatGradedModuleChartDiagram (ι := ι) (G j) d)).homology q) i) := by
  letI : ∀ j, SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt (G j)) := fun j ↦ projectiveNatGradingIntSMul (ι := ι) (G j)
  letI := projectiveNatGradingIntSMul (ι := ι) H
  exact projectiveGradedModuleChartDirectSumCechHomologyIso_inclusion
    (R := R) (ι := ι) (κ := κ) (F := F) (N := N)
    (fun j ↦ projectiveNatGradingInt (G j)) (projectiveNatGradingInt H) e
    (projectiveNatGradingInt_directSum_mem_iff G H e he) d q i

end SerrePositivity.AlgebraicGeometry
