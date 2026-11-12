module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.RepresentationPointFactorization
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.TransportComponentEdgeLift

/-!
概要：分類図式の指定余極限から、元の指定余錐脚を厳密に被覆する実際の辺を回収する。
方針：fiber の成分回収へ、既存の同じ transport の成分による辺持ち上げを適用する。
規約：元の同じ底の辺・終点・全空間を保持。使われ方：元の coslice の分裂三角形。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 元の任意の指定 fiber 点へ、元の一つの項から元の同じ余錐脚を被覆する辺が存在。 -/
lemma representationCocone_edge_factorization {E B : SSet.{u + 1}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p)
    {I : SSet.{u}} (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone R.diagram c))
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c.vertex _⦋0⦌) :
    ∃ i : ((SSet.uliftFunctor.{u + 1, u}).obj I) _⦋0⦌,
      ∃ w : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (D.app (Opposite.op ⦋0⦌) i) _⦋0⦌,
        ∃ k : E.Edge w.val t.val,
          (k.map p).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c i).edge := by
  obtain ⟨i, w, hw⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.representationCocone_point_factorization p R D c hc t
  obtain ⟨k, hk⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_edge_over_of_edgeTransport_component p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c i) w t hw
  exact ⟨i, w, k, hk⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
