module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedAwayColimit
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedColimitGrading
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartMapLaws

/-!
概要：filtered 余極限の自然数次数から、実際の射影標準開の図式への比較を作る。
方針：標準開の分子族を整数次数の零延長で表し、斉次局所化の比較を適用する。
規約：有限個の多項式変数を固定し、有限段の写像は多項式環上線形とする。
使われ方：動く係数環の図式を共通係数へ制限した後の Čech 比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} {ι : Type} [CommRing R] [DecidableEq ι] [Fintype ι]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (M : J ⥤ ModuleCat.{u} (MvPolynomial ι R))
local instance natChartColimitStageBaseModule (j : J) : Module R (M.obj j) :=
  Module.compHom (M.obj j) (algebraMap R (MvPolynomial ι R))
local instance natChartColimitStageBaseTower (j : J) :
    IsScalarTower R (MvPolynomial ι R) (M.obj j) :=
  IsScalarTower.of_compHom R (MvPolynomial ι R) (M.obj j)
local instance natChartColimitTargetBaseModule :
    Module R (colimit M : ModuleCat.{u} (MvPolynomial ι R)) :=
  Module.compHom (colimit M : ModuleCat.{u} (MvPolynomial ι R))
    (algebraMap R (MvPolynomial ι R))
local instance natChartColimitTargetBaseTower :
    IsScalarTower R (MvPolynomial ι R) (colimit M : ModuleCat.{u} (MvPolynomial ι R)) :=
  IsScalarTower.of_compHom R (MvPolynomial ι R)
    (colimit M : ModuleCat.{u} (MvPolynomial ι R))

variable (G : ∀ j, ℕ → Submodule R (M.obj j))
variable (hG : ∀ {i j} (α : i ⟶ j) (n : ℕ) (m : M.obj i),
  m ∈ G i n → (M.map α).hom m ∈ G j n)
variable [∀ j, SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) (G j)]
/-- 有限段の実際の標準開の係数図式を並べる filtered 図式。 -/
def projectiveNatChartColimitDiagram (d : ℤ) :
    J ⥤ (Finset ι ⥤ ModuleCat.{u} R) where
  obj j := projectiveNatGradedModuleChartDiagram (G j) d
  map {i j} α := projectiveNatGradedModuleChartMap (G i) (G j)
    (M.map α).hom (hG α) d
  map_id j := by
    simpa only [M.map_id, ModuleCat.hom_id] using
      projectiveNatGradedModuleChartMap_id (ι := ι) (G j) d
  map_comp {i j k} α β := by
    simpa only [M.map_comp, ModuleCat.hom_comp] using
      (projectiveNatGradedModuleChartMap_comp (G i) (G j) (G k)
        (M.map α).hom (M.map β).hom (hG α) (hG β) d).symm

/-- 各有限段から、余極限の次数付き加群の実際の標準開への余錐。 -/
def projectiveNatChartColimitCocone (d : ℤ) :
    Cocone (projectiveNatChartColimitDiagram M G hG d) where
  pt :=
    letI := projectiveGradedColimitGradeGradedSMul M G hG
      (MvPolynomial.homogeneousSubmodule ι R)
    projectiveNatGradedModuleChartDiagram (projectiveGradedColimitGrade M G) d
  ι :=
    { app j :=
        letI := projectiveGradedColimitGradeGradedSMul M G hG
          (MvPolynomial.homogeneousSubmodule ι R)
        projectiveNatGradedModuleChartMap (G j) (projectiveGradedColimitGrade M G)
        (colimit.ι M j).hom (projectiveGradedColimitInclusion_preservesPiece M G hG j) d
      naturality {i j} α := by
        letI := projectiveGradedColimitGradeGradedSMul M G hG
          (MvPolynomial.homogeneousSubmodule ι R)
        simp only [Functor.const_obj_map, Category.comp_id]
        change projectiveNatGradedModuleChartMap (G i) (G j) (M.map α).hom (hG α) d ≫
          projectiveNatGradedModuleChartMap (G j) (projectiveGradedColimitGrade M G)
            (colimit.ι M j).hom _ d = _
        rw [projectiveNatGradedModuleChartMap_comp]
        congr 1
        exact congrArg ModuleCat.Hom.hom (colimit.w M α) }

/-- 標準開の図式全体で定義した canonical な filtered colimit 比較。 -/
def projectiveNatChartColimitMap (d : ℤ) :=
  colimit.desc _ (projectiveNatChartColimitCocone M G hG d)

/-- 標準開の分子族の余極限は、余極限の次数成分から作った分子族に一致する。 -/
theorem projectiveNatChartColimitNumerator (d : ℤ) (T : Finset ι) :
    projectiveGradedColimitGrade M
        (fun j n ↦ projectiveNatGradingInt (G j) (d + n • (T.card : ℤ))) =
      (fun n ↦ projectiveNatGradingInt (projectiveGradedColimitGrade M G)
        (d + n • (T.card : ℤ))) := by
  funext n
  exact projectiveGradedColimitGrade_int M G (fun k ↦ d + k • (T.card : ℤ)) n

end SerrePositivity.AlgebraicGeometry
