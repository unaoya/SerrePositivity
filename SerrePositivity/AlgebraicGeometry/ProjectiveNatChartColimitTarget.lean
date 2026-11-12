module

public import SerrePositivity.AlgebraicGeometry.ProjectiveNatChartColimitIso
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartIso

/-!
概要：標準開の filtered colimit を、指定された極限の加群の次数成分へ移す。
方針：加群の極限の同型と次数成分の同定を、標準開の自然同型に移す。
規約：模型の構成自体は行わず、その加群の余極限と次数の一致を入力する。
使われ方：2g が供給する動く基底の模型と、実際の標準開の Čech 計算をつなぐ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} {ι : Type} [CommRing R] [DecidableEq ι] [Fintype ι]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (M : J ⥤ ModuleCat.{u} (MvPolynomial ι R))
local instance chartColimitTargetStageBaseModule (j : J) : Module R (M.obj j) :=
  Module.compHom (M.obj j) (algebraMap R (MvPolynomial ι R))
local instance chartColimitTargetStageBaseTower (j : J) :
    IsScalarTower R (MvPolynomial ι R) (M.obj j) :=
  IsScalarTower.of_compHom R (MvPolynomial ι R) (M.obj j)
local instance chartColimitTargetBaseModule :
    Module R (colimit M : ModuleCat.{u} (MvPolynomial ι R)) :=
  Module.compHom (colimit M : ModuleCat.{u} (MvPolynomial ι R))
    (algebraMap R (MvPolynomial ι R))
local instance chartColimitTargetBaseTower :
    IsScalarTower R (MvPolynomial ι R) (colimit M : ModuleCat.{u} (MvPolynomial ι R)) :=
  IsScalarTower.of_compHom R (MvPolynomial ι R)
    (colimit M : ModuleCat.{u} (MvPolynomial ι R))
variable (G : ∀ j, ℕ → Submodule R (M.obj j))
variable (hG : ∀ {i j} (α : i ⟶ j) (n : ℕ) (m : M.obj i),
  m ∈ G i n → (M.map α).hom m ∈ G j n)
variable [∀ j, SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) (G j)]
variable {N : Type u} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable (H : ℕ → Submodule R N)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (e : (colimit M : ModuleCat.{u} (MvPolynomial ι R)) ≃ₗ[MvPolynomial ι R] N)
variable (he : ∀ n x, e x ∈ H n ↔ x ∈ projectiveGradedColimitGrade M G n)

/-- 指定された実際の極限の加群の標準開と、各有限段の標準開の filtered colimit の同型。 -/
def projectiveNatChartColimitTargetIso (d : ℤ) :
    colimit (projectiveNatChartColimitDiagram M G hG d) ≅
      projectiveNatGradedModuleChartDiagram (ι := ι) H d := by
  letI := projectiveGradedColimitGradeGradedSMul M G hG
    (MvPolynomial.homogeneousSubmodule ι R)
  exact projectiveNatChartColimitIso M G hG d ≪≫
    projectiveNatGradedChartIso (projectiveGradedColimitGrade M G) H e he d

/-- 指定された実際の極限の係数での Čech H と、有限段の Čech H の余極限との比較。
原典 Stacks 30.6.1 の極限比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveNatCechFilteredHomologyTargetIso (d : ℤ) (q : ℕ) :
    (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) H d)).homology q ≅
      colimit (projectiveNatChartColimitDiagram M G hG d ⋙ fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q) :=
  ((fullCechComplexFunctor (R := R) (ι := ι)) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso
        (projectiveNatChartColimitTargetIso M G hG H e he d).symm ≪≫
    projectiveCechFilteredHomologyIso (projectiveNatChartColimitDiagram M G hG d) q

end SerrePositivity.AlgebraicGeometry
