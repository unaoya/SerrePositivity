module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointRestrictionInitialFamily
public import
  SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialEvaluationHomotopyTriangle
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomotopyEndpointTransport

/-!
概要：枝の同じ全辺族から、評価固定の始対象 Hom 比較を構成する。
方針：実際の初期制限と始対象の切断を評価上で結び、底へ射影する。
規約：中間族・全時刻の評価・raw な射影を保持。使われ方：枝と根辺の比較円柱の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : F ⟶ B) [InnerFibration q]
  (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌)
  {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌)
  (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex c)
local notation "v" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationPointHomFamily p d y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q r hr y
local notation "I" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionInitialHomFamily p q r hr d e y
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫
  Iso.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y)

/-- 指定した枝の全辺族の初期制限を、同じ評価上で始対象の切断へ比較するデータ。 -/
def pointRestrictionFullHomCylinderData : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialEvaluationCylinder q c y v hc I :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEvaluationCylinder q c y v hc I
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionInitialHomFamily_evaluation p q r hr d e y)
local notation "D" => pointRestrictionFullHomCylinderData p q r hr d e y hc

/-- 枝の元の全 Hom の族と同じ実際の辺の前合成を、保持した中間円柱の像で結ぶ。 -/
def pointRestrictionFullHomCylinder : SSet.Homotopy
    (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialHomComparison q c hc y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionHomPrecomposition p q r hr d e y) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (D).homotopy P)
    (by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialHomComparison, Category.assoc])
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionInitialHomFamily_projection p q r hr d e y)

/-- 枝の比較円柱の raw な射は、同じ全辺族に基づく中間円柱の射影である。 -/
lemma pointRestrictionFullHomCylinder_projection :
    (pointRestrictionFullHomCylinder p q r hr d e y hc).h = (D).homotopy.h ≫ P :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw _ _ _

/-- 中間比較の全時刻で、元の全 Hom の族の枝への制限を厳密に評価する。 -/
lemma pointRestrictionFullHomCylinderData_evaluation :
    (D).homotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y =
      fst _ (Δ[1] : SSet.{u}) ≫ v :=
  (D).evaluation

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
