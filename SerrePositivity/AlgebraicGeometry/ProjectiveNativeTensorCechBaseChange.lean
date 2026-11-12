module

public import SerrePositivity.AlgebraicGeometry.ProjectiveTensorChartNaturality
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedTensorBaseChange

/-!
概要：flat なテンソル底変換を、基底変更後の実際の標準開の Čech 計算へつなぐ。
方針：係数図式の自然同型を Čech 複体とコホモロジーへ送り、既存の比較と合成する。
規約：Hⁱ は Čech 版で、B の Noether 性は仮定しない。
使われ方：射影版有限性と形式関数に要る、実際の flat 底変換の入口。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped TensorProduct
universe u
variable {R B M : Type u} {ι : Type} [CommRing R] [CommRing B]
variable [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (φ : R →+* B) (G : ℕ → Submodule R M)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 実際の基底変更後の標準開 Čech コホモロジーと、元のコホモロジーのテンソル積の同型。
原典 Stacks 30.5.2(2) の Hⁱ の flat 底変換に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveNativeTensorCechIso (hφ : φ.Flat) (d : ℤ) (q : ℕ) :
    letI := φ.toAlgebra
    (ModuleCat.extendScalars φ).obj
        ((fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q) ≅
      (fullCechComplex
        (projectiveTensorGradedModuleChartDiagram (B := B) (ι := ι) G d)).homology q := by
  letI := φ.toAlgebra
  exact projectiveNatGradedTensorCechIso (ι := ι) φ G hφ d q ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) q).mapIso
      ((fullCechComplexFunctor (R := B) (ι := ι)).mapIso
        (projectiveTensorChartDiagramIso G φ hφ d))

section Naturality
variable {N : Type u} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable (H : ℕ → Submodule R N)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (f : M →ₗ[MvPolynomial ι R] N) (hf : ∀ j, ∀ m ∈ G j, f m ∈ H j)

/-- 実際の標準開の Čech flat 底変換の比較は、次数を保つ加群写像に自然。
原典 Stacks 30.5.2(2) の Hⁱ の flat 底変換の自然性に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveNativeTensorCechIso_naturality (hφ : φ.Flat) (d : ℤ) (q : ℕ) :
    letI := φ.toAlgebra
    (ModuleCat.extendScalars φ).map
        (projectiveNatGradedModuleCechHomologyMap G H f hf d q) ≫
      (projectiveNativeTensorCechIso (ι := ι) φ H hφ d q).hom =
    (projectiveNativeTensorCechIso (ι := ι) φ G hφ d q).hom ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) q).map
        (fullCechComplexMap (projectiveTensorGradedModuleChartMap (B := B) G H f hf d)) := by
  letI := φ.toAlgebra
  let K := fullCechComplexFunctor (R := B) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) q
  let ηB := projectiveTensorGradedModuleChartMap (B := B) G H f hf d
  have hη := projectiveTensorChartDiagramIso_naturality G H f hf φ hφ d
  change (ModuleCat.extendScalars φ).map
      (projectiveNatGradedModuleCechHomologyMap G H f hf d q) ≫
        ((projectiveNatGradedTensorCechIso (ι := ι) φ H hφ d q).hom ≫
          K.map (projectiveTensorChartDiagramIso H φ hφ d).hom) =
    ((projectiveNatGradedTensorCechIso (ι := ι) φ G hφ d q).hom ≫
      K.map (projectiveTensorChartDiagramIso G φ hφ d).hom) ≫ K.map ηB
  have hK : K.map (Functor.whiskerRight (projectiveNatGradedModuleChartMap G H f hf d)
        (ModuleCat.extendScalars φ)) ≫ K.map (projectiveTensorChartDiagramIso H φ hφ d).hom =
      K.map (projectiveTensorChartDiagramIso G φ hφ d).hom ≫ K.map ηB := by
    rw [← K.map_comp, hη, K.map_comp]
  rw [← Category.assoc, projectiveNatGradedTensorCechIso_naturality, Category.assoc]
  change (projectiveNatGradedTensorCechIso (ι := ι) φ G hφ d q).hom ≫
      (K.map (Functor.whiskerRight (projectiveNatGradedModuleChartMap G H f hf d)
        (ModuleCat.extendScalars φ)) ≫ K.map (projectiveTensorChartDiagramIso H φ hφ d).hom) = _
  rw [hK, Category.assoc]

end Naturality

variable [DirectSum.Decomposition G] [IsNoetherianRing R]
variable [Module.Finite (MvPolynomial ι R) M]

/-- 実際の flat 底変換後の標準開 Čech コホモロジーは B 上有限生成。
原典 Stacks 30.19.2 と 30.5.2(2) の Hⁱ の有限性と底変換に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveNativeTensorCechHomology_finite (hφ : φ.Flat) (d : ℤ) (q : ℕ) :
    letI := φ.toAlgebra
    Module.Finite B ((fullCechComplex
      (projectiveTensorGradedModuleChartDiagram (B := B) (ι := ι) G d)).homology q) := by
  letI := φ.toAlgebra
  letI := projectiveNatGradedFullCechHomology_finite (ι := ι) G d q
  letI : Module.Finite B ((ModuleCat.extendScalars φ).obj
      ((fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q)) :=
    inferInstanceAs (Module.Finite B
      (B ⊗[R] ((fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q)))
  exact Module.Finite.equiv (projectiveNativeTensorCechIso (ι := ι) φ G hφ d q).toLinearEquiv

end SerrePositivity.AlgebraicGeometry
