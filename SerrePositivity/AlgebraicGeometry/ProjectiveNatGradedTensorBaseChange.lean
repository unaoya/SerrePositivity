module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFlatBaseChange
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedFiniteness
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartMap

/-!
概要：自然数次数の標準開の Čech 計算を、実際のテンソル係数へ移す。
方針：標準開図式を extendScalars で移し、flat な比較と射影有限性を適用する。
規約：比較先は各標準開の係数をテンソル積した図式であり、基底変更後の次数付き加群との照合は別に行う。
使われ方：Noether な元の基底から、Noether 性を仮定しない flat な係数環へ有限性を渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R B M : Type u} {ι : Type} [CommRing R] [CommRing B]
variable [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (φ : R →+* B) (G : ℕ → Submodule R M)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 各標準開の係数を実際に B とテンソル積した図式。 -/
def projectiveNatGradedTensorChartDiagram (d : ℤ) : Finset ι ⥤ ModuleCat.{u} B :=
  projectiveNatGradedModuleChartDiagram (ι := ι) G d ⋙ ModuleCat.extendScalars φ

/-- 標準開 Čech コホモロジーのテンソル積と、テンソル係数の Čech 計算との同型。
原典 Stacks 30.5.2(2) の Hⁱ の flat 底変換に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveNatGradedTensorCechIso (hφ : φ.Flat) (d : ℤ) (q : ℕ) :
    (ModuleCat.extendScalars φ).obj
        ((fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q) ≅
      (fullCechComplex (projectiveNatGradedTensorChartDiagram (ι := ι) φ G d)).homology q :=
  projectiveCechFlatBaseChangeIso φ (projectiveNatGradedModuleChartDiagram (ι := ι) G d) hφ q

section Naturality
variable {N : Type u} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable (H : ℕ → Submodule R N)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (f : M →ₗ[MvPolynomial ι R] N) (hf : ∀ j, ∀ m ∈ G j, f m ∈ H j)

/-- テンソル係数の標準開 Čech 比較は、次数を保つ加群写像に自然。
原典 Stacks 30.5.2(2) の Hⁱ の底変換の自然性に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveNatGradedTensorCechIso_naturality (hφ : φ.Flat) (d : ℤ) (q : ℕ) :
    (ModuleCat.extendScalars φ).map
        (projectiveNatGradedModuleCechHomologyMap G H f hf d q) ≫
      (projectiveNatGradedTensorCechIso (ι := ι) φ H hφ d q).hom =
    (projectiveNatGradedTensorCechIso (ι := ι) φ G hφ d q).hom ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) q).map
        (fullCechComplexMap (Functor.whiskerRight
          (projectiveNatGradedModuleChartMap G H f hf d) (ModuleCat.extendScalars φ))) := by
  convert projectiveCechFlatBaseChangeIso_naturality φ
    (projectiveNatGradedModuleChartDiagram (ι := ι) G d) hφ
    (projectiveNatGradedModuleChartDiagram (ι := ι) H d)
    (projectiveNatGradedModuleChartMap G H f hf d) q using 1 <;> rfl

end Naturality

variable [DirectSum.Decomposition G] [IsNoetherianRing R]
variable [Module.Finite (MvPolynomial ι R) M]

/-- flat なテンソル係数の標準開 Čech コホモロジーは B 上有限生成。
B の Noether 性は仮定しない。原典 Stacks 30.19.2 と 30.5.2(2) の Hⁱ に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveNatGradedTensorCechHomology_finite (hφ : φ.Flat) (d : ℤ) (q : ℕ) :
    Module.Finite B ((fullCechComplex (projectiveNatGradedTensorChartDiagram (ι := ι) φ G d)).homology q) := by
  letI := projectiveNatGradedFullCechHomology_finite (ι := ι) G d q
  exact projectiveCechFlatBaseChange_finite φ
    (projectiveNatGradedModuleChartDiagram (ι := ι) G d) hφ q

end SerrePositivity.AlgebraicGeometry
