module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialRestrictionSectionComparison
public import
  SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialEvaluationHomotopyTriangle

/-!
概要：普遍前置の始点へ至る評価固定の円柱と、その Hom への射影を構成する。
方針：前置写像の厳密な評価式から始対象の切断と比較し、既存の Hom 前合成へ射影する。
規約：底の同じ前置写像を使う。使われ方：元の HL・HR と同じ射の類の回収。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {E F B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) (q : F ⟶ B) [InnerFibration q]
  (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex d)
  {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌)
  (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex c)
local notation "Φ" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionTotalPrecomposition p q r hr d e y
local notation "L" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection p d hd y ≫ Φ
local notation "R" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q r hr y
local notation "P" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫
  Iso.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y)

/-- 普遍前置の始点を、元の制限と同じ全族の評価を全時刻固定して結ぶデータ。 -/
def initialRestrictionUniversalCylinderData : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialEvaluationCylinder q c y R hc L :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEvaluationCylinder q c y R hc L (by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionTotalPrecomposition_evaluation,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection p d hd y)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation p d y),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection_evaluation, Category.id_comp])
local notation "U" => initialRestrictionUniversalCylinderData p q r hr d hd e y hc

/-- 同じ普遍前置の始点へ至る円柱を、既存の Hom 前合成の表示へ射影する。 -/
def initialRestrictionUniversalHomCylinder : SSet.Homotopy
    (R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialHomComparison q c hc y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialHomComparison p d hd y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionHomPrecomposition p q r hr d e y) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (U).homotopy P)
    (by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialHomComparison, Category.assoc])
    ((Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection p d hd y) Φ P).trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialSection p d hd y ≫ ·)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionTotalPrecomposition_pinched p q r hr d e y)).trans
          (by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialHomComparison, Category.assoc])))

/-- Hom への円柱の射影は、同じ普遍前置を使った中間円柱の raw な像である。 -/
lemma initialRestrictionUniversalHomCylinder_projection :
    (initialRestrictionUniversalHomCylinder p q r hr d hd e y hc).h = (U).homotopy.h ≫ P :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyEndpointTransport_raw _ _ _

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
