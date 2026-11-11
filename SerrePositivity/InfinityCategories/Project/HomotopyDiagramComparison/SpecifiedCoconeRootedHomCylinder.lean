module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRootedHomFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialEvaluationHomotopyTriangle

/-!
概要：指定した元の四面体の全 Hom 比較を、評価固定の実際の中間円柱として保持する。
方針：元の四面体からの中間 Hom 族と、その厳密な評価式に自明 Kan 評価を適用する。
規約：終点と四面体の族をそのまま使い、比較円柱の評価条件を捨てない。
使われ方：共通 end の HR と元の四面体の族を同じ全 Hom 上で比較する三角形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "V" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeCommonHomFamily hp p c hc dB dC y
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y


/-- 同じ四面体の中間 Hom 族と、その評価を全時刻で固定する比較円柱。 -/
abbrev SpecifiedCoconeRootedHomCylinder := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialEvaluationCylinder q c y V hc L

/-- 元の四面体の族を比較する、評価固定条件を保持した実際の円柱データ。 -/
def specifiedCoconeRootedHomCylinder : SpecifiedCoconeRootedHomCylinder hp p c hc dB dC y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialEvaluationCylinder q c y V hc L
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedInitialHomFamily_evaluation hp p c hc dB dC y)

/-- 全 Hom の比較を、同じ評価固定中間円柱の像として構成する。 -/
def specifiedCoconeRootedHomCylinderComparison : SSet.Homotopy
    (V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpaceHomComparison c hc y)
    (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (specifiedCoconeRootedHomCylinder hp p c hc dB dC y).homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom)

/-- 公開した比較円柱は、元の中間円柱の raw な射影そのもの。 -/
lemma specifiedCoconeRootedHomCylinderComparison_projection :
    (specifiedCoconeRootedHomCylinderComparison hp p c hc dB dC y).h =
      (specifiedCoconeRootedHomCylinder hp p c hc dB dC y).homotopy.h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q c y).hom := rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
