module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreePointUnderlyingFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNormalizedEvaluationComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeReplacementComparison

/-!
概要：元の正規化barと同じstrict実現の全関手比較を、一点係数の評価から作る。
方針：一点定数関手の評価を全射で照合し、既存の正規化・全複体・増大の比較を合成する。
規約：元の同じ正規化射影と増大を使い、対象ごとの逆を新たに選ばない。
使われ方：3b-3 R6 U38、元の実現関手と計算したapexの比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SerrePositivity.DifferentialGraded
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

local instance : HasCoproducts.{0} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape
local instance : HasCoproducts.{u} (Complex A) := fun _ =>
  HomologicalComplex.instHasColimitsOfShape

/-- U38の係数移送の法則の分割：一点定数関手の評価は元の同じ複体関手。 -/
lemma strictSemifreePointValue_evaluation :
    (semifreePointConstant A).onClosed ⋙
      (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
        (dgModuleSemifreeProperty A PUnit.{1})).onClosed ⋙
      moduleEvaluation A PUnit.{1} PUnit.unit = semifreeUnderlyingComplex A := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  change (complexClosedHomEquiv A _ _)
    (ForgetEnrichment.homOf (Complex A)
      ((ForgetEnrichment.homTo (Complex A)
        ((semifreeComplexInclusion A).onClosed.map f) ≫
          (ringConstantHomIso A _ _).inv) ≫ (ringConstantHomIso A _ _).hom)) = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, ForgetEnrichment.homOf_homTo]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- U38の係数移送の法則：元の図式と全自然変換の係数評価を保つ。 -/
lemma strictSemifreePointUnderlyingFunctor_evaluation :
    strictSemifreePointUnderlyingFunctor A ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj
        (moduleEvaluation A PUnit.{1} PUnit.unit) =
      strictSemifreeUnderlyingComplex A .simplicial := by
  have h := congrArg
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ
      (ClosedCategory A (Semifree A)) (Complex A)).obj)
    (strictSemifreePointValue_evaluation A)
  exact h

/-- U38の同じ法則の帰結：同じbarの全複体は元の単体的置換の実現関手。 -/
lemma strictSemifreePointUnderlyingFunctor_total :
    strictSemifreePointUnderlyingFunctor A ⋙ strictBarTotalComplexFunctor A SimplexCategoryᵒᵖ =
      strictSemifreeReplacementRealization A := by
  have h := congrArg (fun F => F ⋙
    simplicialReplacementFunctor (J := SimplexCategoryᵒᵖ) (C := Complex A) ⋙
      directSumTotalFunctor A) (strictSemifreePointUnderlyingFunctor_evaluation A)
  exact h

/-- U38：元の正規化barの同じ一点評価の通常関手。 -/
def strictSemifreeNormalizedBarComplex :
    StrictSemifreeDiagram A SimplexCategoryᵒᵖ ⥤ Complex A :=
  strictSemifreePointUnderlyingFunctor A ⋙ strictBarNormalizedFunctor A SimplexCategoryᵒᵖ ⋙
    moduleEvaluation A PUnit.{1} PUnit.unit

/-- U38：元の正規化射影・全複体比較・増大による全関手同型。 -/
def strictSemifreeNormalizedBarRealizationIso :
    FunctorIso (nerveMap (strictSemifreeNormalizedBarComplex A) ≫ complexDerivedEvaluation A)
      (strictSemifreeRealizationFamily A) := by
  have e := (strictBarNormalizedTotalDerivedIso A SimplexCategoryᵒᵖ).precomp
    (nerveMap (strictSemifreePointUnderlyingFunctor A))
  change FunctorIso
    (nerveMap (strictSemifreeNormalizedBarComplex A) ≫ complexDerivedEvaluation A)
    (nerveMap (strictSemifreePointUnderlyingFunctor A ⋙
      strictBarTotalComplexFunctor A SimplexCategoryᵒᵖ) ≫ complexDerivedEvaluation A) at e
  rw [strictSemifreePointUnderlyingFunctor_total] at e
  exact e ≪≫ strictSemifreeReplacementRealizationIso A

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
