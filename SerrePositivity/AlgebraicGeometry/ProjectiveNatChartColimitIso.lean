module

public import SerrePositivity.AlgebraicGeometry.ProjectiveNatChartColimitComponent
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFilteredComplex

/-!
概要：実際の射影標準開の図式と Čech H の filtered colimit 比較。
方針：各成分の分数による同型を canonical な図式の比較射と同定する。
規約：固定した多項式変数を持つ次数付き加群の filtered 図式を扱う。
使われ方：係数環の極限を標準開の Čech 計算へつなぐ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} {ι : Type} [CommRing R] [DecidableEq ι] [Fintype ι]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (M : J ⥤ ModuleCat.{u} (MvPolynomial ι R))
local instance natChartColimitIsoStageBaseModule (j : J) : Module R (M.obj j) :=
  Module.compHom (M.obj j) (algebraMap R (MvPolynomial ι R))
local instance natChartColimitIsoStageBaseTower (j : J) :
    IsScalarTower R (MvPolynomial ι R) (M.obj j) :=
  IsScalarTower.of_compHom R (MvPolynomial ι R) (M.obj j)
local instance natChartColimitIsoTargetBaseModule :
    Module R (colimit M : ModuleCat.{u} (MvPolynomial ι R)) :=
  Module.compHom (colimit M : ModuleCat.{u} (MvPolynomial ι R))
    (algebraMap R (MvPolynomial ι R))
local instance natChartColimitIsoTargetBaseTower :
    IsScalarTower R (MvPolynomial ι R) (colimit M : ModuleCat.{u} (MvPolynomial ι R)) :=
  IsScalarTower.of_compHom R (MvPolynomial ι R)
    (colimit M : ModuleCat.{u} (MvPolynomial ι R))
variable (G : ∀ j, ℕ → Submodule R (M.obj j))
variable (hG : ∀ {i j} (α : i ⟶ j) (n : ℕ) (m : M.obj i),
  m ∈ G i n → (M.map α).hom m ∈ G j n)
variable [∀ j, SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) (G j)]

/-- 標準開の filtered colimit の canonical な比較射は各有限交叉で同型。 -/
theorem projectiveNatChartColimitMap_app_isIso (d : ℤ) (T : Finset ι) :
    IsIso ((projectiveNatChartColimitMap M G hG d).app T) := by
  let D := projectiveNatChartColimitDiagram M G hG d
  let E := preservesColimitIso ((evaluation (Finset ι) (ModuleCat.{u} R)).obj T) D
  let e := (projectiveNatChartColimitComponentEquiv M G hG d T).toModuleIso
  have he : E.inv ≫ (projectiveNatChartColimitMap M G hG d).app T = e.hom := by
    apply colimit.hom_ext
    intro j
    rw [ι_preservesColimitIso_inv_assoc]
    have hc := congrArg (fun η ↦ η.app T)
      (colimit.ι_desc (projectiveNatChartColimitCocone M G hG d) j)
    change ((colimit.ι D j).app T) ≫
      (projectiveNatChartColimitMap M G hG d).app T = _
    rw [show ((colimit.ι D j).app T) ≫
      (projectiveNatChartColimitMap M G hG d).app T =
        ((projectiveNatChartColimitCocone M G hG d).ι.app j).app T from hc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact (projectiveNatChartColimitComponentEquiv_ι_val M G hG d T j z).symm
  haveI : IsIso (E.inv ≫ (projectiveNatChartColimitMap M G hG d).app T) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left E.inv _

/-- 標準開間の制限写像を含め、図式全体の filtered colimit 比較は同型。 -/
def projectiveNatChartColimitIso (d : ℤ) :
    colimit (projectiveNatChartColimitDiagram M G hG d) ≅
      (projectiveNatChartColimitCocone M G hG d).pt := by
  haveI (T : Finset ι) : IsIso ((projectiveNatChartColimitMap M G hG d).app T) :=
    projectiveNatChartColimitMap_app_isIso M G hG d T
  haveI := NatIso.isIso_of_isIso_app (projectiveNatChartColimitMap M G hG d)
  exact asIso (projectiveNatChartColimitMap M G hG d)

/-- 実際の射影標準開の Čech H と filtered colimit の比較。
原典 Stacks 30.6.1 の Hⁱ の極限比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveNatCechFilteredHomologyIso (d : ℤ) (q : ℕ) :
    (fullCechComplex (projectiveNatChartColimitCocone M G hG d).pt).homology q ≅
      colimit (projectiveNatChartColimitDiagram M G hG d ⋙ fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q) :=
  ((fullCechComplexFunctor (R := R) (ι := ι)) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso
        (projectiveNatChartColimitIso M G hG d).symm ≪≫
    projectiveCechFilteredHomologyIso (projectiveNatChartColimitDiagram M G hG d) q

end SerrePositivity.AlgebraicGeometry
