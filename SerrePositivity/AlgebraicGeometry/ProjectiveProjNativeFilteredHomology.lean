module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeCechFiniteness
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatChartColimitTarget

/-!
概要：動く基底を共通の多項式環へ制限し、実際の極限の Proj の Čech H と比較する。
方針：指定された極限の次数成分での比較と、実際の構造層との比較を合成する。
規約：有限型模型の構成と余極限の環の構成は 2g の入力であり、ここでは仮定として明示する。
使われ方：2g の模型の構成と、2e の実際の標準開の filtered 比較を接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {R : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (M : J ⥤ ModuleCat.{u} (MvPolynomial ι R))
local instance projNativeFilteredStageBaseModule (j : J) : Module R (M.obj j) :=
  Module.compHom (M.obj j) (algebraMap R (MvPolynomial ι R))
local instance projNativeFilteredStageBaseTower (j : J) :
    IsScalarTower R (MvPolynomial ι R) (M.obj j) :=
  IsScalarTower.of_compHom R (MvPolynomial ι R) (M.obj j)
local instance projNativeFilteredBaseModule :
    Module R (colimit M : ModuleCat.{u} (MvPolynomial ι R)) :=
  Module.compHom (colimit M : ModuleCat.{u} (MvPolynomial ι R))
    (algebraMap R (MvPolynomial ι R))
local instance projNativeFilteredBaseTower :
    IsScalarTower R (MvPolynomial ι R) (colimit M : ModuleCat.{u} (MvPolynomial ι R)) :=
  IsScalarTower.of_compHom R (MvPolynomial ι R)
    (colimit M : ModuleCat.{u} (MvPolynomial ι R))
variable (G : ∀ j, ℕ → Submodule R (M.obj j))
variable (hG : ∀ {i j} (α : i ⟶ j) (n : ℕ) (m : M.obj i),
  m ∈ G i n → (M.map α).hom m ∈ G j n)
variable [∀ j, SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) (G j)]

variable {S : Type u} [CommRing S] [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable (H : ℕ → Submodule R S) [GradedRing H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (e : (colimit M : ModuleCat.{u} (MvPolynomial ι R)) ≃ₗ[MvPolynomial ι R] S)
variable (he : ∀ n x, e x ∈ H n ↔ x ∈ projectiveGradedColimitGrade M G n)

/-- 実際の極限の Proj の構造層の Čech H と、各有限段の次数零 Čech H の余極限の比較。
原典 Stacks 30.6.1 の極限比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。基底環の模型を作ることは、この宣言の主張に含めない。 -/
def projectiveProjNativeFilteredHomologyIso (q : ℕ) :
    (fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf (Proj H) ⋙
      ModuleCat.restrictScalars (projectiveScalarToGlobalSections H))
        (projectiveProjCechOpen (ι := ι) H))).homology q ≅
      colimit (projectiveNatChartColimitDiagram M G hG 0 ⋙ fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso
      (projectiveProjNativeNatCechComplexIso (ι := ι) H).symm ≪≫
    projectiveNatCechFilteredHomologyTargetIso M G hG H e he 0 q

end SerrePositivity.AlgebraicGeometry
