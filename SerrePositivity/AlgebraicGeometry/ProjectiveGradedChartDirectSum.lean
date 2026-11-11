module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedTransportRestriction
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChart
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechDirectSumHomology

/-!
概要：次数を保つ直和の加群同値を、標準開の係数図式と Čech コホモロジーへ移す。
方針：斉次局所化の直和比較を各交叉に使い、制限との自然性で図式の同型にまとめる。
規約：基底環は固定し、加群の整数次数と外部直和の添字を区別する。
使われ方：原典 Stacks 30.20.1 の Hⁱ の直和に対応する、Čech 版の Rees 比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
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

/-- 次数を対応させる直和の加群同値は、標準開の係数図式の同型を与える。 -/
def projectiveGradedModuleChartDirectSumIso (d : ℤ) :
    projectiveGradedModuleChartDiagram (ι := ι) H d ≅
      projectiveCechDirectSumDiagram (fun i ↦ projectiveGradedModuleChartDiagram (ι := ι) (G i) d) :=
  NatIso.ofComponents (fun T ↦
    (projectiveGradedLocalizedDirectSumTransport (projectiveLaurentDenominator R T)
      (fun i k ↦ G i (d + k • (T.card : ℤ)))
      (fun k ↦ H (d + k • (T.card : ℤ))) e
      (fun k x ↦ he (d + k • (T.card : ℤ)) x)
      (fun i ↦ projectiveGradedChart_mul_denominator (G i) T d)).toModuleIso) (by
    intro T U h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (projectiveGradedLocalizedDirectSumTransport_restriction
      (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm
      (fun i k ↦ G i (d + k • (T.card : ℤ)))
      (fun i k ↦ G i (d + k • (U.card : ℤ)))
      (fun k ↦ H (d + k • (T.card : ℤ)))
      (fun k ↦ H (d + k • (U.card : ℤ))) e
      (fun k x ↦ he (d + k • (T.card : ℤ)) x)
      (fun k x ↦ he (d + k • (U.card : ℤ)) x)
      (fun i ↦ projectiveGradedChart_mul_denominator (G i) T d)
      (fun i ↦ projectiveGradedChart_mul_denominator (G i) U d)
      (fun i ↦ projectiveGradedChart_mul_mem (G i) (leOfHom h) d)
      (projectiveGradedChart_mul_mem H (leOfHom h) d) z).symm)

/-- 直和と同値な次数付き加群の標準開 Čech コホモロジーは、各成分の直和と同型。
原典 Stacks 30.20.1 の Hⁱ の直和に対応する Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveGradedModuleChartDirectSumCechHomologyIso (d : ℤ) (q : ℕ) :
    (fullCechComplex (projectiveGradedModuleChartDiagram (ι := ι) H d)).homology q ≅
      ModuleCat.of R (⨁ i,
        (fullCechComplex (projectiveGradedModuleChartDiagram (ι := ι) (G i) d)).homology q) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso
    ((fullCechComplexFunctor (R := R) (ι := ι)).mapIso
      (projectiveGradedModuleChartDirectSumIso (R := R) (ι := ι) (κ := κ)
        (F := F) (N := N) G H e he d)) ≪≫
    projectiveCechDirectSumHomologyIso (R := R) (κ := κ) (ι := ι)
      (fun i ↦ projectiveGradedModuleChartDiagram (ι := ι) (G i) d) q

end SerrePositivity.AlgebraicGeometry
