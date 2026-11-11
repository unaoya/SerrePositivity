module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.BridgeFiniteCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.NativeTotalComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.TotalLegFiberComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.CoconeLegNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge

/-!
概要：元の coherent 図式の脚・辺を使う D の条件から native な余極限性を導く。
方針：全空間余錐の実脚と余錐比較に有限 π 判定を直接適用する。
規約：頂点を覆う元の添字と元の底の辺を明示し、strict 図式へ置き換えない。
使われ方：poset の nerve と宇宙を分離した D の最終目標への特殊化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

variable {B : SSet.{u}} [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
  {I : Type v} [PartialOrder I]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F)
  (r : I → B _⦋0⦌)
  (e : ∀ {i j : I}, i ≤ j → B.Edge (r i) (r j))

set_option maxHeartbeats 1000000 in
-- 元の脚・持ち上げた辺・全空間頂点の投影 Kan 型の同時照合が標準 heartbeat を超えるため。
/-- 元の全頂点を覆う添字と同じ底の辺に関する D の条件は、元の余極限性を与える。 -/
lemma isColimitCone_of_coherent_spacePiData
    (hr : Function.Surjective r)
    (h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactSpacePiData
      (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up (r i))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject c.vertex)
      (fun {_ _} hij ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue
        ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, u + 1} (e hij).toTruncated)).map F))
      (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c (ULift.up (r i))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.isColimitCone_iff_nativeTotalPiCriterion F c).mpr
  refine _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.bridge_finite_piCriterion _ _ _ _ _ h
    (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F) (ULift.up (r i))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.nativeTotalValueComparison F c) ?_ ?_ ?_
  · intro i
    exact ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.nativeTotalComparison_leg_homotopy F c (ULift.up (r i))⟩
  · intro i j hij
    exact ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.coconeLegNaturalityHomotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F)
      (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, u + 1} (e hij).toTruncated))⟩
  · intro K _ f
    obtain ⟨b, g, H⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.finite_nativeTotalLeg_detection F f
    obtain ⟨i, rfl⟩ := hr b
    exact ⟨i, g, H⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
