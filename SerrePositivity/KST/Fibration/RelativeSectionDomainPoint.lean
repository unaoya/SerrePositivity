module
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedJointPointHom
public import SerrePositivity.KST.Fibration.DoubleEvaluationCurry

/-! # 定義域制限の元の共同同型は、同じ切断の制限像の点を保持する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B : SSet.{u}} {J : Type u} [Category.{u} J]
  {A D : Jᵒᵖ ⥤ Over B} (η : A ⟶ D)
  (hη : ∀ j (X : LeftFibrationObject B),
    IsQCatEquivalence (relativeFunctorOverPre X.val.hom (η.app (Opposite.op j))))

/-- 元の共同制限同型の同じ指定成分を、元の二つの Kan 値で表示する。 -/
def relativeSectionDomainComponentIso (X : LeftFibrationObject B) (j : J) :
    VertexIso (spaceInfinityVertex (((relativeSectionEnrichedDiagram D).obj j).obj X))
      (spaceInfinityVertex (((relativeSectionEnrichedDiagram A).obj j).obj X)) :=
  (eqToIso (congrArg HomotopyCategory.mk
    (kanEnrichedJointEvaluation_vertex (relativeSectionEnrichedDiagram D) X j))).symm ≪≫
      functorIsoValue (relativeSectionJointComparisonIso η hη)
        (ULift.up (nerveVertex j), coherentNerveVertex X) ≪≫
      eqToIso (congrArg HomotopyCategory.mk
        (kanEnrichedJointEvaluation_vertex (relativeSectionEnrichedDiagram A) X j))

/-- 同じ成分の射は、元の切断制限射の coherent な辺の類。 -/
theorem relativeSectionDomainComponentIso_hom (X : LeftFibrationObject B) (j : J) :
    (relativeSectionDomainComponentIso η hη X j).hom =
      Truncated.HomotopyCategory.homMk
        (((coherentNerveEdge ((relativeFunctorOverPreComparison
          (η.app (Opposite.op j))).val X)).ofEq
          (spaceInfinityVertex_eq_coherent
            (((relativeSectionEnrichedDiagram D).obj j).obj X)).symm
          (spaceInfinityVertex_eq_coherent
            (((relativeSectionEnrichedDiagram A).obj j).obj X)).symm).toTruncated) := by
  simp only [relativeSectionDomainComponentIso, Iso.trans_hom, Iso.symm_hom, eqToIso.inv,
    eqToIso.hom, _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue_hom]
  rw [show (relativeSectionJointComparisonIso η hη).hom = Truncated.HomotopyCategory.homMk
    (relativeSectionJointComparisonEdge η).toTruncated from rfl,
    _root_.SerrePositivity.InfinityCategories.F1.Transport.functorHomEvaluate_edge_hom]
  exact homMk_transport
    (kanEnrichedJointEvaluation_vertex (relativeSectionEnrichedDiagram D) X j)
    (kanEnrichedJointEvaluation_vertex (relativeSectionEnrichedDiagram A) X j)
    _ _ (relativeSectionJointComparisonEdge_at η j X)

/-- 指定制限成分は、元の切断の点を同じ実制限射の像へ送る。 -/
theorem relativeSectionDomainComponentIso_pointHom (X : LeftFibrationObject B) (j : J)
    (v : (((relativeSectionEnrichedDiagram D).obj j).obj X).obj _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram D).obj j).obj X)).symm v) ≫
      (relativeSectionDomainComponentIso η hη X j).hom =
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram A).obj j).obj X)).symm
        ((relativeFunctorOverPre X.val.hom (η.app (Opposite.op j))).app
          (Opposite.op ⦋0⦌) v)) := by
  rw [relativeSectionDomainComponentIso_hom]
  exact kanPointHom_comp_of_edge
    ((relativeFunctorOverPreComparison (η.app (Opposite.op j))).val X) _ rfl v

end SerrePositivity.KST.Fibration
