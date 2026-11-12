module

public import SerrePositivity.AlgebraicGeometry.ProjectiveNatChartColimit
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedAwayColimitValues

/-!
概要：標準開の図式の filtered colimit 比較を、各有限交叉で同型として構成する。
方針：固定した標準開の分子族に斉次局所化の同型を適用する。
規約：分母の非零因子性や有限表示性は仮定しない。
使われ方：標準開の図式全体の比較が同型であることの証明。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} {ι : Type} [CommRing R] [DecidableEq ι] [Fintype ι]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (M : J ⥤ ModuleCat.{u} (MvPolynomial ι R))
local instance natChartColimitComponentStageBaseModule (j : J) : Module R (M.obj j) :=
  Module.compHom (M.obj j) (algebraMap R (MvPolynomial ι R))
local instance natChartColimitComponentStageBaseTower (j : J) :
    IsScalarTower R (MvPolynomial ι R) (M.obj j) :=
  IsScalarTower.of_compHom R (MvPolynomial ι R) (M.obj j)
local instance natChartColimitComponentTargetBaseModule :
    Module R (colimit M : ModuleCat.{u} (MvPolynomial ι R)) :=
  Module.compHom (colimit M : ModuleCat.{u} (MvPolynomial ι R))
    (algebraMap R (MvPolynomial ι R))
local instance natChartColimitComponentTargetBaseTower :
    IsScalarTower R (MvPolynomial ι R) (colimit M : ModuleCat.{u} (MvPolynomial ι R)) :=
  IsScalarTower.of_compHom R (MvPolynomial ι R)
    (colimit M : ModuleCat.{u} (MvPolynomial ι R))
variable (G : ∀ j, ℕ → Submodule R (M.obj j))
variable (hG : ∀ {i j} (α : i ⟶ j) (n : ℕ) (m : M.obj i),
  m ∈ G i n → (M.map α).hom m ∈ G j n)
variable [∀ j, SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) (G j)]

include hG in
/-- 次数を保つ有限段の写像は、標準開の分子族も保つ。 -/
theorem projectiveNatChartColimitNumerator_map (d : ℤ) (T : Finset ι)
    {i j : J} (α : i ⟶ j) (n : ℕ) (m : M.obj i)
    (hm : m ∈ projectiveNatGradingInt (G i) (d + n • (T.card : ℤ))) :
    (M.map α).hom m ∈ projectiveNatGradingInt (G j) (d + n • (T.card : ℤ)) :=
  projectiveNatGradingInt_map_mem (G i) (G j) (M.map α).hom (hG α) _ m hm

/-- 各有限段の標準開の分子族は、その標準開の分母倍で次の項へ移る。 -/
theorem projectiveNatChartColimitNumerator_step (d : ℤ) (T : Finset ι) (j : J)
    (n : ℕ) (m : projectiveNatGradingInt (G j) (d + n • (T.card : ℤ))) :
    projectiveLaurentDenominator R T • m.val ∈
      projectiveNatGradingInt (G j) (d + (n + 1) • (T.card : ℤ)) := by
  letI := projectiveNatGradingIntSMul (ι := ι) (G j)
  exact projectiveGradedChart_mul_denominator (projectiveNatGradingInt (G j)) T d n m

/-- 標準開の成分図式を、固定した分母の斉次局所化の図式と明示的に同定する。 -/
def projectiveNatChartColimitComponentDiagramIso (d : ℤ) (T : Finset ι) :
    projectiveNatChartColimitDiagram M G hG d ⋙
        (evaluation (Finset ι) (ModuleCat.{u} R)).obj T ≅
      projectiveGradedAwayColimitDiagram M
        (fun j n ↦ projectiveNatGradingInt (G j) (d + n • (T.card : ℤ)))
        (fun α ↦ projectiveNatChartColimitNumerator_map M G hG d T α)
        (projectiveLaurentDenominator R T) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intros
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

/-- 実際の標準開の有限交叉ごとの filtered colimit 比較は線形同型。 -/
def projectiveNatChartColimitComponentEquiv (d : ℤ) (T : Finset ι) :
    (colimit (projectiveNatChartColimitDiagram M G hG d ⋙
      (evaluation (Finset ι) (ModuleCat.{u} R)).obj T) : ModuleCat.{u} R) ≃ₗ[R]
        projectiveGradedAway (projectiveLaurentDenominator R T)
          (fun n ↦ projectiveNatGradingInt (projectiveGradedColimitGrade M G)
            (d + n • (T.card : ℤ))) :=
  (HasColimit.isoOfNatIso
    (projectiveNatChartColimitComponentDiagramIso M G hG d T)).toLinearEquiv.trans
    ((projectiveGradedAwayColimitEquiv M
      (fun j n ↦ projectiveNatGradingInt (G j) (d + n • (T.card : ℤ)))
      (fun α ↦ projectiveNatChartColimitNumerator_map M G hG d T α)
      (projectiveLaurentDenominator R T)
      (projectiveNatChartColimitNumerator_step M G d T)).trans
        (LinearEquiv.ofEq _ _ (congrArg (projectiveGradedAway (projectiveLaurentDenominator R T))
          (projectiveNatChartColimitNumerator M G d T))))

/-- 図式の明示的な同定は、各有限段からの標準の射を保つ。 -/
theorem projectiveNatChartColimitComponentDiagramIso_ι (d : ℤ) (T : Finset ι)
    (j : J) (z : (projectiveNatGradedModuleChartDiagram (G j) d).obj T) :
    (HasColimit.isoOfNatIso
      (projectiveNatChartColimitComponentDiagramIso M G hG d T)).hom.hom
        ((colimit.ι (projectiveNatChartColimitDiagram M G hG d ⋙
          (evaluation (Finset ι) (ModuleCat.{u} R)).obj T) j).hom z) =
      (colimit.ι (projectiveGradedAwayColimitDiagram M
        (fun j n ↦ projectiveNatGradingInt (G j) (d + n • (T.card : ℤ)))
        (fun α ↦ projectiveNatChartColimitNumerator_map M G hG d T α)
        (projectiveLaurentDenominator R T)) j).hom z := by
  have hj : ((projectiveNatChartColimitComponentDiagramIso M G hG d T).hom.app j).hom z = z :=
    rfl
  have h := congrArg (fun f ↦ f.hom z)
    (HasColimit.ι_isoOfNatIso_hom (projectiveNatChartColimitComponentDiagramIso M G hG d T) j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hj] using h

/-- 各段の標準開からの写像と、成分ごとの余極限同型は同じ局所化分数を与える。 -/
theorem projectiveNatChartColimitComponentEquiv_ι_val (d : ℤ) (T : Finset ι)
    (j : J) (z : (projectiveNatGradedModuleChartDiagram (G j) d).obj T) :
    (projectiveNatChartColimitComponentEquiv M G hG d T
      ((colimit.ι (projectiveNatChartColimitDiagram M G hG d ⋙
        (evaluation (Finset ι) (ModuleCat.{u} R)).obj T) j).hom z)).val =
      ((((projectiveNatChartColimitCocone M G hG d).ι.app j).app T).hom z).val := by
  change ((projectiveNatChartColimitComponentEquiv M G hG d T) _).val =
    (IsLocalizedModule.map (Submonoid.powers (projectiveLaurentDenominator R T))
      (LocalizedModule.mkLinearMap _ (M.obj j))
      (LocalizedModule.mkLinearMap _ (colimit M : ModuleCat.{u} (MvPolynomial ι R)))
      (colimit.ι M j).hom) z.val
  simp only [projectiveNatChartColimitComponentEquiv, LinearEquiv.trans_apply,
    CategoryTheory.Iso.toLinearEquiv_apply, LinearEquiv.coe_ofEq_apply]
  rw [projectiveNatChartColimitComponentDiagramIso_ι]
  exact projectiveGradedAwayColimitEquiv_ι_value M
    (fun j n ↦ projectiveNatGradingInt (G j) (d + n • (T.card : ℤ)))
    (fun α ↦ projectiveNatChartColimitNumerator_map M G hG d T α)
    (projectiveLaurentDenominator R T)
    (projectiveNatChartColimitNumerator_step M G d T) j z

end SerrePositivity.AlgebraicGeometry
