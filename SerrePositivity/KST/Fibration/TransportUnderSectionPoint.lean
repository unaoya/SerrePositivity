module
public import SerrePositivity.KST.Fibration.RelativeSectionDomainEvaluation
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexUnderRealization

/-! # 元の under 切断比較の指定成分は、同じ切断の実制限像を保持する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B : SSet.{u}} (X : LeftFibrationObject B) (c : TransportSimplexCategory B)

/-- 元の under 共同比較そのものの同じ二重成分を、元の切断 Kan 値で表示する。 -/
def transportUnderJointComponentIso :=
  relativeSectionDomainValueIso (transportSimplexUnderDomainTransformation B)
    (fun s p => transportSimplexUnderPre_isQCatEquivalence p.val.hom s) X c

/-- 表示変更後も、元の under 共同同型の同じ指定二重成分を保持する。 -/
theorem transportUnderJointComponentIso_heq_doubleMap :
    HEq (transportUnderJointComponentIso X c)
      (VertexIso.map (transportSimplexUnderJointIso B)
        (_root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation (Y := SpaceInfinity.{u})
          (ULift.up (nerveVertex c)) (coherentNerveVertex X))) := by
  unfold transportUnderJointComponentIso relativeSectionDomainValueIso F2.isoNormalizeEndpoints
  exact F2.iso_endpoints_heq _ _ _

/-- 同じ指定成分は、元の under 実現比較の同じ対象・添字での二重評価でもある。 -/
theorem transportUnderJointComponentIso_heq_realizationMap :
    HEq (transportUnderJointComponentIso X c)
      (VertexIso.map (transportSimplexUnderRealizationIso B)
        (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation X c)) := by
  let η := transportSimplexUnderDomainTransformation B
  have hη : ∀ s (p : LeftFibrationObject B),
      IsQCatEquivalence (relativeFunctorOverPre p.val.hom (η.app (Opposite.op s))) :=
    fun s p => transportSimplexUnderPre_isQCatEquivalence p.val.hom s
  exact (transportUnderJointComponentIso_heq_doubleMap X c).trans
    ((relativeSectionDiagramComparisonIso_doubleMap η hη X c).trans
      (relativeSectionRealizationComparisonIso_doubleMap η hη X c).symm)

/-- 同じ指定成分は、元の切断点を元の under 定義域への制限像へ送る。 -/
theorem transportUnderJointComponentIso_pointHom
    (v : (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj X).obj
      _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj X)).symm v) ≫
      (transportUnderJointComponentIso X c).hom =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)).obj c).obj X)).symm
        ((relativeFunctorOverPre X.val.hom
          ((transportSimplexUnderDomainTransformation B).app (Opposite.op c))).app
            (Opposite.op ⦋0⦌) v)) := by
  unfold transportUnderJointComponentIso
  rw [relativeSectionDomainValueIso_eq]
  exact relativeSectionDomainComponentIso_pointHom _ _ X c v

end SerrePositivity.KST.Fibration
