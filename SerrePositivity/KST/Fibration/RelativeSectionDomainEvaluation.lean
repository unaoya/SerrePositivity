module
public import SerrePositivity.KST.Fibration.RelativeSectionDomainPoint
public import SerrePositivity.KST.Fibration.RelativeSectionJointVertices
public import SerrePositivity.KST.Fibration.KanEnrichedRealizationValue

/-! # 元の定義域比較の実現・共同図式を、同じ制限成分へ戻す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B : SSet.{u}} {J : Type u} [Category.{u} J]
  {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D)
  (hη : ∀ j (X : LeftFibrationObject B),
    IsQCatEquivalence (relativeFunctorOverPre X.val.hom (η.app (Opposite.op j))))

/-- 元の実現同型は、同じ共同同型の curry の端点だけを表示変更する。 -/
theorem relativeSectionRealizationComparisonIso_heq_curry :
    HEq (relativeSectionRealizationComparisonIso η hη)
      (relativeSectionJointComparisonIso η hη).curry := by
  unfold relativeSectionRealizationComparisonIso
  dsimp only [_root_.id]
  have hcast {α β : Sort (u + 2)} (h : α = β) (x : α) : HEq (Eq.mp h x) x := by
    cases h
    rfl
  exact (hcast _ _).trans (hcast _ _)

/-- 元の実現の二重成分は、同じ共同同型の元の直積成分。 -/
theorem relativeSectionRealizationComparisonIso_doubleMap
    (X : LeftFibrationObject B) (j : J) :
    HEq (VertexIso.map (relativeSectionRealizationComparisonIso η hη)
      (kanEnrichedDoubleEvaluation X j))
      (VertexIso.map (relativeSectionJointComparisonIso η hη)
        (evaluateFunctorAt (ULift.up (nerveVertex j), coherentNerveVertex X))) := by
  have hm := F2.vertexIso_map_heq_of_heq
    (relativeSectionRealizationComparisonIso η hη)
    (relativeSectionJointComparisonIso η hη).curry
    (congrArg functorVertex
      (kanEnrichedJointEvaluation_curry (relativeSectionEnrichedDiagram D)).symm)
    (congrArg functorVertex
      (kanEnrichedJointEvaluation_curry (relativeSectionEnrichedDiagram A)).symm)
    (relativeSectionRealizationComparisonIso_heq_curry η hη)
    (kanEnrichedDoubleEvaluation X j)
  exact hm.trans (functorIso_curry_doubleMap (relativeSectionJointComparisonIso η hη)
    (ULift.up (nerveVertex j)) (coherentNerveVertex X))

/-- 共同図式向きへ転置しても、同じ元の直積成分を保持する。 -/
theorem relativeSectionDiagramComparisonIso_doubleMap
    (X : LeftFibrationObject B) (j : J) :
    HEq (VertexIso.map (relativeSectionDiagramInfinityComparisonIso η hη)
      (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
        (ULift.up (nerveVertex j)) (coherentNerveVertex X)))
      (VertexIso.map (relativeSectionJointComparisonIso η hη)
        (evaluateFunctorAt (ULift.up (nerveVertex j), coherentNerveVertex X))) := by
  have ht := functorIso_transpose_doubleMap (relativeSectionRealizationComparisonIso η hη)
    (coherentNerveVertex X) (ULift.up (nerveVertex j))
  exact ht.trans (relativeSectionRealizationComparisonIso_doubleMap η hη X j)

/-- 元の共同図式比較の指定成分を、元の二つの切断空間で表示する。 -/
def relativeSectionDomainValueIso (X : LeftFibrationObject B) (j : J) :=
  F2.isoNormalizeEndpoints
    (VertexIso.map (relativeSectionDiagramInfinityComparisonIso η hη)
      (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
        (ULift.up (nerveVertex j)) (coherentNerveVertex X)))
    (congrArg HomotopyCategory.mk (relativeSectionDiagramInfinity_double_vertex D X j))
    (congrArg HomotopyCategory.mk (relativeSectionDiagramInfinity_double_vertex A X j))

/-- 同じ成分は、元の実制限射を持つ指定係数成分と厳密に一致する。 -/
theorem relativeSectionDomainValueIso_eq (X : LeftFibrationObject B) (j : J) :
    relativeSectionDomainValueIso η hη X j = relativeSectionDomainComponentIso η hη X j := by
  have hc : HEq (relativeSectionDomainComponentIso η hη X j)
      (VertexIso.map (relativeSectionJointComparisonIso η hη)
        (evaluateFunctorAt (ULift.up (nerveVertex j), coherentNerveVertex X))) :=
    (F2.iso_endpoints_heq _
      (congrArg HomotopyCategory.mk
        (kanEnrichedJointEvaluation_vertex (relativeSectionEnrichedDiagram D) X j))
      (congrArg HomotopyCategory.mk
        (kanEnrichedJointEvaluation_vertex (relativeSectionEnrichedDiagram A) X j))).trans
      (functorIsoValue_heq_map _ _)
  exact F2.isoNormalizeEndpoints_eq_of_heq _ _ _ _
    ((relativeSectionDiagramComparisonIso_doubleMap η hη X j).trans hc.symm)

end SerrePositivity.KST.Fibration
