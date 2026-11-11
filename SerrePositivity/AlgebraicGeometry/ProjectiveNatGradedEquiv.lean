module

public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartMapLaws

/-!
概要：次数を保つ多項式加群の線形同型を、標準開と Čech コホモロジーへ送る。
方針：同型と逆写像に標準開の関手を適用し、恒等・合成則を使う。
規約：両方向が次数を保つことを明示する。
使われ方：二重閉厚化の係数比較を、実際の Čech 計算の同型へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R M N : Type u} {ι : Type} [CommRing R] [DecidableEq ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable (G : ℕ → Submodule R M) (H : ℕ → Submodule R N)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (e : M ≃ₗ[MvPolynomial ι R] N)
variable (he : ∀ j, ∀ m ∈ G j, e m ∈ H j)
variable (hi : ∀ j, ∀ n ∈ H j, e.symm n ∈ G j)

/-- 両方向で Proj 次数を保つ同型が誘導する、標準開の図式の同型。 -/
def projectiveNatGradedModuleChartIso (d : ℤ) :
    projectiveNatGradedModuleChartDiagram (ι := ι) G d ≅
      projectiveNatGradedModuleChartDiagram (ι := ι) H d where
  hom := projectiveNatGradedModuleChartMap G H e.toLinearMap he d
  inv := projectiveNatGradedModuleChartMap H G e.symm.toLinearMap hi d
  hom_inv_id := by
    rw [projectiveNatGradedModuleChartMap_comp]
    apply Eq.trans _ (projectiveNatGradedModuleChartMap_id (ι := ι) G d)
    congr 1
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply x
  inv_hom_id := by
    rw [projectiveNatGradedModuleChartMap_comp]
    apply Eq.trans _ (projectiveNatGradedModuleChartMap_id (ι := ι) H d)
    congr 1
    apply LinearMap.ext
    intro x
    exact e.apply_symm_apply x

/-- 次数付き加群の同型が誘導する、標準開 Čech コホモロジーの同型。
原典 Stacks 30.20.5 の Hⁱ の比較に使う Čech 版の関手性。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveNatGradedModuleCechHomologyIso (d : ℤ) (q : ℕ) :
    (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q ≅
      (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) H d)).homology q :=
  (fullCechComplexFunctor (R := R) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso
      (projectiveNatGradedModuleChartIso G H e he hi d)

/-- Čech の同型の順写像は、元の線形同型からの Čech 写像そのもの。 -/
@[simp] theorem projectiveNatGradedModuleCechHomologyIso_hom (d : ℤ) (q : ℕ) :
    (projectiveNatGradedModuleCechHomologyIso G H e he hi d q).hom =
      projectiveNatGradedModuleCechHomologyMap G H e.toLinearMap he d q := rfl

end SerrePositivity.AlgebraicGeometry
