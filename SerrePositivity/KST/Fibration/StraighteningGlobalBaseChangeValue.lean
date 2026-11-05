module
public import SerrePositivity.KST.Fibration.StraighteningBaseChangeSectionCharts

/-! # 元の大域底変換の実成分を、同じ全単体上の左右の切断比較で表示する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} (k : D ⟶ B)

/-- 大域底変換の元の二重成分を、同じ制限成分の端点で表示する。 -/
def straighteningGlobalBaseChangeValueIso (X : LeftFibrationObject B)
    (c : TransportSimplexCategory D) :=
  F2.isoNormalizeEndpoints
    (VertexIso.map (leftStraighteningSectionJointDiagram_baseChangeIso k)
      (_root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation (Y := SpaceInfinity.{u})
        (ULift.up ((transportSimplexFirstVertexMap D).app (Opposite.op ⦋0⦌)
          (nerveVertex c))) (coherentNerveVertex X)))
    (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Stable.Straightening.doubleFunctorEvaluation_precomp_vertex
      ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningSectionJointDiagram B)
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D))
      (ULift.up (nerveVertex c)) (coherentNerveVertex X)))
    (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Stable.Straightening.doubleFunctorEvaluation_precomp_vertex
      (leftStraighteningSectionJointDiagram D ≫
        (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D))
      (ULift.up (nerveVertex c)) (coherentNerveVertex X)))

/-- 表示変更後も、同じ大域成分は元の指定制限成分に一致する。 -/
theorem straighteningGlobalBaseChangeValueIso_eq [Quasicategory D]
    (X : LeftFibrationObject B) (c : TransportSimplexCategory D) :
    straighteningGlobalBaseChangeValueIso k X c =
      VertexIso.map (_root_.SerrePositivity.InfinityCategories.Stable.Straightening.straighteningJointBaseChangeRestrictionIso k)
        (_root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation (Y := SpaceInfinity.{u})
          (ULift.up (nerveVertex c)) (coherentNerveVertex X)) :=
  F2.isoNormalizeEndpoints_eq_of_heq _ _ _ _
    (leftStraighteningJointBaseChangeDoubleMap k X c)

/-- 実対象図式の同じ成分は、端点表示を除けば同じ大域成分そのもの。 -/
theorem leftStraighteningDiagramBaseChange_heq_globalValue {E : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (c : TransportSimplexCategory D) :
    HEq (VertexIso.map (leftStraighteningInfinityDiagram_baseChangeIso p k)
      (evaluateFunctorAt (ULift.up ((transportSimplexFirstVertexMap D).app
        (Opposite.op ⦋0⦌) (nerveVertex c)))))
      (straighteningGlobalBaseChangeValueIso k (leftFibrationObjectOf p) c) := by
  have hn : HEq (straighteningGlobalBaseChangeValueIso k (leftFibrationObjectOf p) c)
      (VertexIso.map (leftStraighteningSectionJointDiagram_baseChangeIso k)
        (_root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation (Y := SpaceInfinity.{u})
          (ULift.up ((transportSimplexFirstVertexMap D).app (Opposite.op ⦋0⦌)
            (nerveVertex c))) (leftFibrationInfinityVertex p))) := by
    unfold straighteningGlobalBaseChangeValueIso F2.isoNormalizeEndpoints
    exact F2.iso_endpoints_heq _ _ _
  exact (leftStraighteningInfinityDiagram_baseChangeIso_heq_jointMap p k
    ((transportSimplexFirstVertexMap D).app (Opposite.op ⦋0⦌) (nerveVertex c))).trans hn.symm

/-- 元の大域底変換の同じ指定成分で、同じ pullback 切断の点を回収する。 -/
theorem straighteningGlobalBaseChangeValueIso_pointHom [Quasicategory D]
    (X : LeftFibrationObject B) (c : TransportSimplexCategory D)
    (v : ((((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).precompose
      (leftFibrationBaseChangeEnriched k)).obj c).obj X).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram
        (transportSimplexDomainFunctor D ⋙ Over.map k)).obj c).obj X)).symm
          ((relativeFunctorBaseChangeForward X.val.hom k
            ((transportSimplexDomainFunctor D).obj (Opposite.op c)).hom).app
              (Opposite.op ⦋0⦌) v)) ≫
      (straighteningBaseChangeLeftChart k X c).inv ≫
        (straighteningGlobalBaseChangeValueIso k X c).hom =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      ((((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).precompose
        (leftFibrationBaseChangeEnriched k)).obj c).obj X)).symm v) ≫
      (straighteningBaseChangeRightChart k X c).inv := by
  rw [straighteningGlobalBaseChangeValueIso_eq]
  exact straighteningBaseChangeSectionCharts_pointHom k X c v

end SerrePositivity.KST.Fibration
