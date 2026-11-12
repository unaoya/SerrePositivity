module

public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartMap
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartAdditive
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartScalarAction

/-!
概要：自然数次数の標準開・Čech 写像の恒等・合成・スカラー作用の公式。
方針：同じ基底環の整数次数へ零延長し、既存の公式と Čech 関手の合成則を使う。
規約：ここでは基底環を変えず、次数の族全体の等式による移送は行わない。
使われ方：I 進コホモロジーの像のフィルトレーションを構成する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory

universe u
variable {R M N L : Type u} {ι : Type} [CommRing R] [DecidableEq ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable [AddCommGroup L] [Module R L] [Module (MvPolynomial ι R) L]
variable [IsScalarTower R (MvPolynomial ι R) L]
variable (G : ℕ → Submodule R M) (H : ℕ → Submodule R N) (J : ℕ → Submodule R L)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) J]

/-- 自然数次数の標準開への写像は恒等写像を保つ。 -/
theorem projectiveNatGradedModuleChartMap_id (d : ℤ) :
    projectiveNatGradedModuleChartMap (ι := ι) G G LinearMap.id (fun _ _ h ↦ h) d =
      𝟙 (projectiveNatGradedModuleChartDiagram (ι := ι) G d) := by
  letI := projectiveNatGradingIntSMul (ι := ι) G
  exact projectiveGradedModuleChartMap_id (ι := ι) (projectiveNatGradingInt G) d

/-- 自然数次数の標準開への写像は合成を保つ。 -/
theorem projectiveNatGradedModuleChartMap_comp
    (f : M →ₗ[MvPolynomial ι R] N) (g : N →ₗ[MvPolynomial ι R] L)
    (hf : ∀ n, ∀ m ∈ G n, f m ∈ H n) (hg : ∀ n, ∀ m ∈ H n, g m ∈ J n) (d : ℤ) :
    projectiveNatGradedModuleChartMap (ι := ι) G H f hf d ≫
        projectiveNatGradedModuleChartMap (ι := ι) H J g hg d =
      projectiveNatGradedModuleChartMap (ι := ι) G J (g.comp f)
        (fun n m hm ↦ hg n _ (hf n m hm)) d := by
  letI := projectiveNatGradingIntSMul (ι := ι) G
  letI := projectiveNatGradingIntSMul (ι := ι) H
  letI := projectiveNatGradingIntSMul (ι := ι) J
  exact projectiveGradedModuleChartMap_comp (ι := ι)
    (projectiveNatGradingInt G) (projectiveNatGradingInt H) (projectiveNatGradingInt J)
    d f g (projectiveNatGradingInt_map_mem G H f hf) (projectiveNatGradingInt_map_mem H J g hg)

/-- 自然数次数の Čech コホモロジーへの写像も合成を保つ。
原典 Stacks 30.20.1 の Hⁱ の射に対応する Čech 版の合成則。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveNatGradedModuleCechHomologyMap_comp
    (f : M →ₗ[MvPolynomial ι R] N) (g : N →ₗ[MvPolynomial ι R] L)
    (hf : ∀ n, ∀ m ∈ G n, f m ∈ H n) (hg : ∀ n, ∀ m ∈ H n, g m ∈ J n)
    (d : ℤ) (q : ℕ) :
    projectiveNatGradedModuleCechHomologyMap (ι := ι) G H f hf d q ≫
        projectiveNatGradedModuleCechHomologyMap (ι := ι) H J g hg d q =
      projectiveNatGradedModuleCechHomologyMap (ι := ι) G J (g.comp f)
        (fun n m hm ↦ hg n _ (hf n m hm)) d q := by
  let K := fullCechComplexFunctor (R := R) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  have h := congrArg (fun a ↦ K.map a)
    (projectiveNatGradedModuleChartMap_comp (ι := ι) G H J f g hf hg d)
  simp only [Functor.map_comp] at h
  simpa only [K, Functor.comp_map, Functor.comp_obj, fullCechComplexFunctor,
    projectiveNatGradedModuleCechHomologyMap] using h

/-- 自然数次数の標準開の図式では、基底係数の写像は恒等自然変換のスカラー倍。 -/
theorem projectiveNatGradedModuleChartMap_baseScalar (a : R) (d : ℤ) :
    projectiveNatGradedModuleChartMap (ι := ι) G G
        (projectiveBaseScalarLinearMap (S := MvPolynomial ι R) a)
        (fun n m hm ↦ (G n).smul_mem a hm) d =
      a • 𝟙 (projectiveNatGradedModuleChartDiagram (ι := ι) G d) := by
  letI := projectiveNatGradingIntSMul (ι := ι) G
  exact projectiveGradedModuleChartMap_baseScalar (ι := ι) (projectiveNatGradingInt G) a d

/-- 自然数次数の Čech コホモロジーで、基底係数の写像は既存のスカラー作用。
原典 Stacks 30.20.1 の Hⁱ の係数作用に対応する Čech 版の式。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveNatGradedModuleCechHomologyMap_baseScalar (a : R) (d : ℤ) (q : ℕ) :
    projectiveNatGradedModuleCechHomologyMap (ι := ι) G G
        (projectiveBaseScalarLinearMap (S := MvPolynomial ι R) a)
        (fun n m hm ↦ (G n).smul_mem a hm) d q =
      a • 𝟙 ((fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q) := by
  letI := projectiveNatGradingIntSMul (ι := ι) G
  exact projectiveGradedModuleCechHomologyMap_baseScalar (ι := ι)
    (projectiveNatGradingInt G) a d q

end SerrePositivity.AlgebraicGeometry
