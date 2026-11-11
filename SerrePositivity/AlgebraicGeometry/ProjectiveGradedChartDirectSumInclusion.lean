module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartDirectSum
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedTransportInclusion
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechDiagramInclusion

/-!
概要：次数付き加群の標準開直和比較は、各成分の包含を保つ。
方針：斉次局所化の包含公式を図式へまとめ、既存の Čech 包含の公式へ渡す。
規約：直和同値が Proj 次数を保つことを仮定し、Rees 次数は外部添字で扱う。
使われ方：Rees の各次数の包含とコホモロジーの直和比較との両立性。
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
variable (G : ∀ i, ℤ → Submodule R (F i)) (H : ℤ → Submodule R N)
variable [∀ i, SetLike.GradedSMul
  (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) (G i)]
variable [SetLike.GradedSMul
  (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) H]
variable (e : (⨁ i, F i) ≃ₗ[MvPolynomial ι R] N)
variable (he : ∀ d x, e x ∈ H d ↔ x ∈ projectiveDirectSumSubmodule (fun i ↦ G i d))

include he

/-- 直和同値と各成分の包含の合成は、Proj 次数を保つ。 -/
theorem projectiveGradedModuleChartInclusion_mem (i : κ) (n : ℤ)
    (m : F i) (hm : m ∈ G i n) :
    e (DirectSum.lof (MvPolynomial ι R) κ F i m) ∈ H n := by
  apply (he n _).mpr
  rw [mem_projectiveDirectSumSubmodule]
  intro j
  by_cases h : j = i
  · subst j
    simpa only [DirectSum.lof_apply] using hm
  · simp only [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne i j m h]
    exact (G j n).zero_mem

/-- 各成分の包含を標準開の図式へ渡す。 -/
def projectiveGradedModuleChartInclusion (d : ℤ) (i : κ) :=
  projectiveGradedModuleChartMap (ι := ι) (G i) H d
    (e.toLinearMap.comp (DirectSum.lof (MvPolynomial ι R) κ F i))
    (projectiveGradedModuleChartInclusion_mem G H e he i)

/-- 標準開の直和比較は、元の各成分の包含を係数図式の直和の包含へ写す。 -/
theorem projectiveGradedModuleChartDirectSumIso_inclusion (d : ℤ) (i : κ) :
    projectiveGradedModuleChartInclusion G H e he d i ≫
      (projectiveGradedModuleChartDirectSumIso G H e he d).hom =
    projectiveCechDirectSumDiagramInclusion
      (fun j ↦ projectiveGradedModuleChartDiagram (ι := ι) (G j) d) i := by
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact projectiveGradedLocalizedDirectSumTransport_inclusion
    (projectiveLaurentDenominator R T)
    (fun j k ↦ G j (d + k • (T.card : ℤ))) (fun k ↦ H (d + k • (T.card : ℤ)))
    e (fun k x ↦ he (d + k • (T.card : ℤ)) x)
    (fun j ↦ projectiveGradedChart_mul_denominator (G j) T d) i z

/-- 各成分の包含についての、標準開 Čech コホモロジー直和比較の公式。
原典 Stacks 30.20.1 の Hⁱ の直和比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveGradedModuleChartDirectSumCechHomologyIso_inclusion
    (d : ℤ) (q : ℕ) (i : κ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (fullCechComplexMap (projectiveGradedModuleChartInclusion G H e he d i)) ≫
      (projectiveGradedModuleChartDirectSumCechHomologyIso G H e he d q).hom =
    ModuleCat.ofHom (DirectSum.lof R κ
      (fun j ↦ (fullCechComplex
        (projectiveGradedModuleChartDiagram (ι := ι) (G j) d)).homology q) i) := by
  have hc := congrArg
    (fun a ↦ (fullCechComplexFunctor (R := R) (ι := ι)).map a)
    (projectiveGradedModuleChartDirectSumIso_inclusion G H e he d i)
  simp only [Functor.map_comp] at hc
  dsimp only [fullCechComplexFunctor] at hc
  simp only [projectiveGradedModuleChartDirectSumCechHomologyIso,
    Iso.trans_hom, Functor.mapIso_hom, fullCechComplexFunctor]
  rw [← Category.assoc, ← Functor.map_comp, hc]
  exact projectiveCechDirectSumDiagramInclusion_homology
    (R := R) (κ := κ) (ι := ι)
    (fun j ↦ projectiveGradedModuleChartDiagram (ι := ι) (G j) d) i q

end SerrePositivity.AlgebraicGeometry
