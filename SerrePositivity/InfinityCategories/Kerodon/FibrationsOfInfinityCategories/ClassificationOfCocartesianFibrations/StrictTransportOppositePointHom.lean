module
public import SerrePositivity.KST.Fibration.KanEnrichedOppositePointHom
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.StrictTransportOppositeEvaluation

/-! # 元の strict transport の反転比較の指定成分が、元の係数点の射を保つ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  (p : E ⟶ nerve I) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]

/-- 既存の strict transport 比較の同じ成分は、元の大域反転同型の成分そのもの。 -/
theorem strictTransportOppositeComponentIso_eq_enriched (i : I) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportOppositeComponentIso p i =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanEnrichedOppositeComponentIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.strictTransportDomains I))
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportComparisonObject p) i := by
  let D := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.strictTransportDomains I)
  let X := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportComparisonObject p
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDoubleEvaluation X i
  have hm := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.vertexIso_map_heq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCoherentMap_oppositeIso I)
    D.oppositeRealizationIso
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (congrArg
      (fun F => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedInfinityMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (nerve I)) ≫ F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.strictTransportDomains_realization I).symm)) rfl
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportOppositeIso_heq (I := I)) T
  have hn : HEq (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanEnrichedOppositeComponentIso D X i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map D.oppositeRealizationIso T) :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.iso_endpoints_heq _
      (congrArg HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDoubleEvaluation_precomp_vertex D
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedRight (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (nerve I))) X i))
      (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDoubleEvaluation_vertex D.opposite X i))
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportOppositeComponentIso_heq_doubleMap p i).trans
    (hm.trans hn.symm))

/-- 既存の同じ指定反転成分は、元の係数点を反転側の同じ点へ送る。 -/
theorem strictTransportOppositeComponentIso_pointHom (i : I)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport p i) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p).obj i)).symm v) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportOppositeComponentIso p i).hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p).obj i))).symm
          (SSet.opObjEquiv.symm v)) := by
  rw [strictTransportOppositeComponentIso_eq_enriched]
  exact kanEnrichedOppositeComponentIso_pointHom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.strictTransportDomains I))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.strictTransportComparisonObject p) i v

end SerrePositivity.KST.Fibration
