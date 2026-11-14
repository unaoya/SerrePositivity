module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceTriangleFiber
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SpanCoconeMappingPullback
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalEdgeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalObjects
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.EdgeCosliceIntervalMap
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveInvertedHom

/-!
概要：局所対象への span の余錐を右枝・その終点へ制限する射の全境界充填性。
方針：両枝の余錐空間の厳密な引き戻しと、辺の始点制限の自明 Kan 性を使う。
規約：元の span と指定辺を保持。pushout の脚との照合は別工程。使われ方：HTT 5.5.4.5。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
noncomputable section
variable {X : SSet.{u}} [Quasicategory X]

/-- 左枝への局所性は、span の余錐の右枝への制限の自明 Kan 性を与える。 -/
lemma spanCoconeMapping_right_trivial_of_local
    (p : (horn 2 0 : SSet.{u}) ⟶ X) (z : X _⦋0⦌)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceEdge (horn₂₀.ι₀₁ ≫ p))) z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p horn₂₀.ι₀₂ z) := by
  have := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_edge_iff_sourceRestriction_trivial _ z).mp h
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isPullback (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanCoconeMapping_isPullback p z)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap
      (horn₂₀.ι₀₁ ≫ p) (stdSimplex.δ (1 : Fin 2)) z))⟩
/-- 指定辺集合に属する左枝から、局所対象への余錐の右枝制限の全境界充填性を得る。 -/
lemma spanCoconeMapping_right_trivial_of_localObject (W : Set (X _⦋1⦌))
    (p : (horn 2 0 : SSet.{u}) ⟶ X) (he : SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ p) ∈ W)
    {z : X _⦋0⦌} (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p horn₂₀.ι₀₂ z) := by
  apply spanCoconeMapping_right_trivial_of_local p z
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isLocalForHom_homMk_iff_edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceEdge (horn₂₀.ι₀₁ ≫ p)) z).mpr
  exact hz _ he

/-- 指定左枝が属する辺集合の局所対象に対し、右枝の終点への余錐制限は自明 Kan 射。 -/
lemma spanCoconeMapping_rightTarget_trivial_of_localObject (W : Set (X _⦋1⦌))
    (p : (horn 2 0 : SSet.{u}) ⟶ X) (he : SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ p) ∈ W)
    {z : X _⦋0⦌} (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p
      (stdSimplex.δ (0 : Fin 2) ≫ horn₂₀.ι₀₂) z) := by
  have := spanCoconeMapping_right_trivial_of_localObject W p he hz
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceTriangleTarget_trivialKanFibration (horn₂₀.ι₀₂ ≫ p) z
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_restrict_comp]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p horn₂₀.ι₀₂ z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (horn₂₀.ι₀₂ ≫ p) (stdSimplex.δ (0 : Fin 2)) z))⟩

end
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
