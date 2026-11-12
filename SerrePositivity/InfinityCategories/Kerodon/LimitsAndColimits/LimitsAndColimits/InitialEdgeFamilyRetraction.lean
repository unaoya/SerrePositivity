module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativeEdgeFamilyRetraction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialDiagramHomotopyConstant

/-!
概要：実際の辺面の全族から普遍前置の像への比較を、同じ初期 Hom 空間へ移す。
方針：指定した底の切断比較を持つ全辺円柱を、その始点へ厳密に制限する。
規約：評価固定と底の元の raw な比較を保持。使われ方：枝終点と根辺初期族の照合。

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
variable {E B T : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [InnerFibration q]
  (c : E _⦋0⦌) (e : (Δ[1] : SSet.{u}) ⟶ E)
  (he : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm c)
  (y : B _⦋0⦌) (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder e)
  (ha : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) ≫ q = SSet.const y)
local notation "j" => stdSimplex.δ (0 : Fin 2)
local notation "K" => (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e j) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection e q
local notation "H" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyRetraction e q a y ha

include ha in
/-- 同じ終端を相対切断で戻した族も、元の固定終点 y 上にある。 -/
lemma initialEdgeFamilyRetraction_section_fixed :
    (K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) ≫ q = SSet.const y := by
  rw [Category.assoc (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e j), _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection_projection]
  rw [Category.assoc a, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection]
  exact ha
local notation "hK" => initialEdgeFamilyRetraction_section_fixed q e y a ha

/-- 同じ元の辺面の初期族から、同じ終端を普遍前置した族への初期 Hom 円柱。 -/
def initialEdgeFamilyRetraction : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q c e (stdSimplex.δ (1 : Fin 2)) he y a ha)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q c e (stdSimplex.δ (1 : Fin 2)) he y K hK) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamilyHomotopy q c e (stdSimplex.δ (1 : Fin 2)) he y a K ha hK H
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyRetraction_fixed e q a y ha)
local notation "I" => initialEdgeFamilyRetraction q c e he y a ha

/-- 初期 Hom の包含後は、指定した同じ全辺円柱の始点制限である。 -/
lemma initialEdgeFamilyRetraction_ι :
    (I).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y =
      (H).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction e (stdSimplex.δ (1 : Fin 2)) he :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamilyHomotopy_ι _ _ _ _ _ _ _ _ _ _ _ _

/-- 比較の全時刻で、元の全族と同じ可変終点を評価する。 -/
lemma initialEdgeFamilyRetraction_evaluation :
    (I).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation q c y =
      fst T Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift q y (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) ha := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q y
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc,
    initialEdgeFamilyRetraction_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyRetraction_projection, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]

/-- 底の包含後は、元の底の同じ切断比較円柱の始点制限そのもの。 -/
lemma initialEdgeFamilyRetraction_base :
    (I).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection q c y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyCylinder (e ≫ q) y
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyBase e q a y ha)).homotopy.h ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (e ≫ q)) y) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (e ≫ q) (stdSimplex.δ (1 : Fin 2))
              ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) he)) := by
  rw [initialEdgeFamilyRetraction, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamilyHomotopy_base,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyRetraction_base]

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
