module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.KanForgetDetection
public import SerrePositivity.KST.Fibration.KanClosedEvaluation
public import SerrePositivity.KST.SConstruction.PointedKanEnrichedEquivalences
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.InvertibleLeftTransport
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanWhiteheadComparison
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.NerveHomEdgeNaturality

/-! # 基点を忘れた同じ coherent 辺の可逆性は、元の点つき辺へ反映される -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 基点忘却の全 Hom 作用は、同じ元の基礎射の coherent な辺を回収する。 -/
theorem pointedKanForget_edge {X Y : PointedKanObject.{u}} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanForgetEnriched).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show pointedKanForgetEnriched.obj X ⟶
        pointedKanForgetEnriched.obj Y from f.hom.right)).edge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveMap_edge_of_homEquiv _ _ _ (pointedClosedHomInclusion_hom f.hom)

/-- 基点忘却後に同じ辺が可逆なら、元の点つき Kan 射の同じ辺も可逆。 -/
theorem pointedKan_isInvertible_of_forget {X Y : PointedKanObject.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated.map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanForgetEnriched)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show pointedKanForgetEnriched.obj X ⟶
        pointedKanForgetEnriched.obj Y from f.hom.right)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated.map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanForgetEnriched)))
      (pointedKanForget_edge f)).mp hf
  exact pointedKanObject_edge_isInvertible_of_piIsomorphism f
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanMap_piIsomorphism_of_invertible
      (X := pointedKanForgetEnriched.obj X) (Y := pointedKanForgetEnriched.obj Y) f.hom.right he)

end SerrePositivity.KST.Fibration
