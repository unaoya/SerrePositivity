module
public import SerrePositivity.InfinityCategories.Stable.KanModels.KanEnrichedEdgewisePointHom
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDoubleEvaluation

/-! # 元の左右 edgewise 実現同型の二重評価と、同じ指定成分の一致 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
  {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J)

/-- 元の右実現同型は、同じ豊穣共同比較の実現同型の端点表示だけを変えたもの。 -/
theorem kanEnrichedEdgewiseRightRealizationIso_heq :
    HEq D.edgewiseRightRealizationIso
      (D.edgewiseRightComparison.realizationIso (fun j X =>
        isQCatEquivalence_of_trivialKanFibration (edgewiseRight ((D.obj j).obj X.val).obj))) := by
  unfold KanEnrichedDiagram.edgewiseRightRealizationIso
  dsimp only [_root_.id]
  have hcast {α β : Sort (u + 2)} (h : α = β) (x : α) : HEq (Eq.mp h x) x := by
    cases h
    rfl
  exact hcast _ _

/-- 同じ右指定成分は、元の右大域同型の同じ二重評価による像と HEq。 -/
theorem kanEnrichedEdgewiseRightComponent_heq_doubleMap
    (X : EdgewiseEnrichedObject C) (j : J) :
    HEq (kanEnrichedEdgewiseRightComponent D X j)
      (VertexIso.map D.edgewiseRightRealizationIso (kanEnrichedDoubleEvaluation X j)) := by
  have h := kanEnrichedRealizationComponentIso_heq_doubleMap D.edgewiseRightComparison
    (fun k Y => isQCatEquivalence_of_trivialKanFibration
      (edgewiseRight ((D.obj k).obj Y.val).obj)) X j
  have hm := F2.vertexIso_map_heq_of_heq D.edgewiseRightRealizationIso
    (D.edgewiseRightComparison.realizationIso (fun k Y =>
      isQCatEquivalence_of_trivialKanFibration (edgewiseRight ((D.obj k).obj Y.val).obj)))
    rfl (congrArg functorVertex
      (D.realization_precompose (edgewiseEnrichedRight C)).symm)
    (kanEnrichedEdgewiseRightRealizationIso_heq D) (kanEnrichedDoubleEvaluation X j)
  exact h.trans hm.symm

/-- 元の右同型の二重評価は、端点表示を揃えると同じ右指定成分に厳密に一致。 -/
theorem kanEnrichedEdgewiseRightComponent_eq_doubleMap
    (X : EdgewiseEnrichedObject C) (j : J) :
    kanEnrichedEdgewiseRightComponent D X j =
      F2.isoNormalizeEndpoints
        (VertexIso.map D.edgewiseRightRealizationIso (kanEnrichedDoubleEvaluation X j))
        (congrArg HomotopyCategory.mk (kanEnrichedDoubleEvaluation_vertex D.edgewise X j))
        (congrArg HomotopyCategory.mk
          (kanEnrichedDoubleEvaluation_precomp_vertex D (edgewiseEnrichedRight C) X j)) := by
  exact (F2.isoNormalizeEndpoints_eq_of_heq _ _ _ _
    (kanEnrichedEdgewiseRightComponent_heq_doubleMap D X j).symm).symm

/-- 元の左同型の二重評価も、同じ左指定成分を厳密に回収する。 -/
theorem kanEnrichedEdgewiseLeftComponent_eq_doubleMap
    (X : EdgewiseEnrichedObject C) (j : J) :
    kanEnrichedEdgewiseLeftComponent D X j =
      F2.isoNormalizeEndpoints
        (VertexIso.map D.edgewiseLeftRealizationIso (kanEnrichedDoubleEvaluation X j))
        (congrArg HomotopyCategory.mk (kanEnrichedDoubleEvaluation_vertex D.edgewise X j))
        (congrArg HomotopyCategory.mk (kanEnrichedDoubleEvaluation_vertex D.opposite X j)) := by
  have h := kanEnrichedRealizationComponentIso_heq_doubleMap D.edgewiseLeftComparison
    (fun k Y => isQCatEquivalence_of_trivialKanFibration
      (edgewiseLeft ((D.obj k).obj Y.val).obj)) X j
  exact (F2.isoNormalizeEndpoints_eq_of_heq _ _ _ _ h.symm).symm

end SerrePositivity.KST.Fibration
