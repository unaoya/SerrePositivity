module
public import SerrePositivity.InfinityCategories.Stable.Straightening.StraighteningUnderRealizationChart
import SerrePositivity.InfinityCategories.Stable.Straightening.StraighteningUnderRealizationChart
public import SerrePositivity.KST.Fibration.StraighteningUnderSectionChart

/-! # 元の under 実現比較全体を、元の共同比較の同じ指定成分として回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w v' w'
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B : SSet.{u}}

/-- 実現側の元の分類値は、同じ共同制限の分類値と一致する。 -/
theorem straighteningRestrict_source_vertex
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B) :
    (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation X c).app (Opposite.op ⦋0⦌)
        (functorVertex (leftStraighteningInfinityMap B ≫
          (pre ((SSet.uliftFunctor.{u + 1, u}).map
            (transportSimplexFirstVertexMap B))).app SpaceInfinity.{u})) =
      (_root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation (Y := SpaceInfinity.{u})
        (ULift.up (nerveVertex c)) (coherentNerveVertex X)).app (Opposite.op ⦋0⦌)
          (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
            (transportSimplexFirstVertexMap B) ≫ leftStraighteningSectionJointDiagram B)) := by
  let l := (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B)
  have hv := congrArg functorVertex
    (transposeFunctorFamily_comp l (leftStraighteningSectionJointDiagram B)).symm
  have he := congrArg ((_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation X c).app (Opposite.op ⦋0⦌)) hv
  exact he.trans (doubleFunctorEvaluation_transpose_vertex
    (l ≫ leftStraighteningSectionJointDiagram B) (ULift.up (nerveVertex c))
    (coherentNerveVertex X))

/-- 制限実現側の中間値は、元の単体切断空間の標準頂点。 -/
theorem straighteningRestrict_target_vertex
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B) :
    (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation X c).app (Opposite.op ⦋0⦌)
        (functorVertex (internalHomFlipHomEquiv
          ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (TransportSimplexCategory B)))
          (LeftFibrationInfinity B) SpaceInfinity.{u} (transportSimplexSectionInfinity B))) =
      spaceInfinityVertex
        (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj X) :=
  (doubleFunctorEvaluation_transpose_vertex (transportSimplexSectionInfinity B)
    (ULift.up (nerveVertex c)) (coherentNerveVertex X)).trans
      (relativeSectionDiagramInfinity_double_vertex (transportSimplexDomainFunctor B) X c)

/-- 元の under 実現同型の指定成分を、同じ共同分類値と under 切断空間で表示する。 -/
def straighteningUnderRealizationChart (X : LeftFibrationObject B)
    (c : TransportSimplexCategory B) :=
  F2.isoNormalizeEndpoints
    (VertexIso.map (leftStraighteningInfinityMap_underRealizationIso B)
      (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation X c))
    (congrArg HomotopyCategory.mk (straighteningRestrict_source_vertex X c))
    (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation_vertex
      (relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)) X c))

/-- 元の under 実現比較全体は、元の初頂点切断比較と同じ実制限成分の合成。 -/
theorem straighteningUnderRealizationChart_factor
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B) :
    straighteningUnderRealizationChart X c =
      straighteningFirstVertexSectionChart X c ≪≫ transportUnderJointComponentIso X c := by
  let T := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation X c
  let h := congrArg (fun f => HomotopyCategory.mk (functorVertex f))
    (internalHomFlipHomEquiv_transposeFunctorFamily
      (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization)
  have hf := _root_.SerrePositivity.InfinityCategories.Stable.Straightening.mapNormalizeCompositionWithEq (hoFunctor.map T).toFunctor
    (leftStraighteningInfinityMap_restrictIso B) (transportSimplexUnderRealizationIso B) h
    (leftStraighteningInfinityMap_underRealizationIso B) rfl
    (congrArg HomotopyCategory.mk (straighteningRestrict_source_vertex X c))
    (congrArg HomotopyCategory.mk (straighteningRestrict_target_vertex X c))
    (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation_vertex
      (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)) X c))
    (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation_vertex
      (relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)) X c))
  have hr := F2.isoNormalizeEndpoints_eq_of_heq _ _
    (congrArg HomotopyCategory.mk (straighteningRestrict_source_vertex X c))
    (congrArg HomotopyCategory.mk (straighteningRestrict_target_vertex X c))
    (leftStraighteningInfinityMap_restrictIso_heq_sectionChart X c)
  have hu := F2.isoNormalizeEndpoints_eq_of_heq _ _
    (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation_vertex
      (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)) X c))
    (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanEnrichedDoubleEvaluation_vertex
      (relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)) X c))
    (transportUnderJointComponentIso_heq_realizationMap X c).symm
  exact hf.trans (congrArg₂ (fun e f => e ≪≫ f) hr hu)

/-- 元の実現比較と元の共同比較は、指定した同じ成分へ厳密に一致する。 -/
theorem straighteningUnderRealizationChart_eq_joint
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B) :
    straighteningUnderRealizationChart X c = straighteningFirstVertexUnderChart X c :=
  (straighteningUnderRealizationChart_factor X c).trans
    (straighteningFirstVertexUnderChart_factor X c).symm

/-- 元の under 実現比較の同じ指定成分が、元の切断点を同じ実制限像へ送る。 -/
theorem straighteningUnderRealizationChart_pointHom
    (X : LeftFibrationObject B) (c : TransportSimplexCategory B)
    (v : (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj X).obj
      _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj X)).symm v) ≫
      (straighteningFirstVertexSectionChart X c).inv ≫
        (straighteningUnderRealizationChart X c).hom =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)).obj c).obj X)).symm
        ((relativeFunctorOverPre X.val.hom
          ((transportSimplexUnderDomainTransformation B).app (Opposite.op c))).app
            (Opposite.op ⦋0⦌) v)) := by
  rw [straighteningUnderRealizationChart_eq_joint]
  exact straighteningFirstVertexUnderChart_pointHom X c v

end SerrePositivity.KST.Fibration
