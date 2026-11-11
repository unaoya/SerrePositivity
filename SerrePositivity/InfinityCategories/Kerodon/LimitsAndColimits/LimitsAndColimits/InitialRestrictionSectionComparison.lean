module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialRestrictionSectionSource
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialRestrictionHomCylinder
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomotopyEndpointTransport

/-!
概要：普遍前置の始点を、元の同じ HL・HR データの中間持ち上げへ結ぶ。
方針：保持した全辺族の比較を同じデータへ代入し、厳密な始点の一致で表示変更する。
規約：元の lift と評価・底の全時刻固定を保持。使われ方：元の制限円柱の類の回収。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {E F B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) (q : F ⟶ B) [InnerFibration q]
  (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex d)
  {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌)
  (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex c)
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "a" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeFamily p q r hr d hd e y
local notation "ha" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeFamily_fixed p q r hr d hd e y
local notation "b" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionBaseTriangle p q r hr d hd e y
local notation "h" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionBaseTriangle_target p q r hr d hd e y
local notation "D" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionHomCylinderData p q r hr d hd e y hc

/-- 普遍前置の始点から、元の制限比較円柱の同じ lift へ至る評価・底固定の比較。 -/
def initialRestrictionSectionComparison : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection p d hd y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionTotalPrecomposition p q r hr d e y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialHomEdgeCylinder.lift D) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialHomEdgeSectionInitialComparison q c hc t (SSet.Edge.δ_one_yonedaEquiv_symm e)
      y a ha b h rfl)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionSection_source p q r hr d hd e y).symm rfl

/-- 元の制限関手の fiber の像を、比較の全時刻で厳密に評価する。 -/
lemma initialRestrictionSectionComparison_evaluation :
    (initialRestrictionSectionComparison p q r hr d hd e y hc).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y = fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p y) Δ[1] ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q r hr y := by
  rw [initialRestrictionSectionComparison, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialHomEdgeSectionInitialComparison_evaluation, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeFamily_vertexFiberLift]

/-- 底も、元の同じ lift の底の全族を比較の全時刻で保持する。 -/
lemma initialRestrictionSectionComparison_base :
    (initialRestrictionSectionComparison p q r hr d hd e y hc).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y = fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p y) Δ[1] ≫
          (D).lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y := by
  rw [initialRestrictionSectionComparison, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialHomEdgeSectionInitialComparison_base]
  rfl

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
