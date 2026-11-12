module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativeEdgeFamilyBaseCylinder
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativeCosliceSpecifiedHomotopy

/-!
概要：実際の全辺族から、その終端を普遍相対切断で戻した全族へ指定底上で結ぶ。
方針：元の底の切断比較を相対 coslice に持ち上げ、終端係数を全時刻固定する。
規約：底は同じ元の円柱の raw な包含。使われ方：枝の前置像と根辺初期族の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {E B T : SSet.{u}} [Quasicategory B] (e : (Δ[1] : SSet.{u}) ⟶ E)
  (q : E ⟶ B) [InnerFibration q] (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder e) (y : B _⦋0⦌)
  (ha : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) ≫ q = SSet.const y)
local notation "j" => stdSimplex.δ (0 : Fin 2)
local notation "K" => (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e j) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection e q

/-- 元の全辺族と普遍前置像の間に、同じ底の円柱と終端固定を保つ持ち上げがある。 -/
lemma exists_relativeEdgeFamilyRetraction :
    ∃ H : SSet.Homotopy a K,
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e j = fst T Δ[1] ≫ K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e j ∧
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp e q = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyBaseCylinder e q a y ha).h := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_relativeCosliceSpecifiedHomotopy e q j _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.endpointInclusion_rightAnodyne a K
    (by simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection_target, Category.comp_id])
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyBaseCylinder e q a y ha)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyBaseCylinder_target e q a y ha)

/-- 同じ底の切断比較の上で、元の全辺族を普遍相対切断の像へ結ぶ。 -/
def relativeEdgeFamilyRetraction : SSet.Homotopy a K :=
  (exists_relativeEdgeFamilyRetraction e q a y ha).choose

/-- 比較は、元の同じ終端係数を全時刻固定する。 -/
lemma relativeEdgeFamilyRetraction_target :
    (relativeEdgeFamilyRetraction e q a y ha).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e j =
      fst T Δ[1] ≫ a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e j := by
  rw [relativeEdgeFamilyRetraction]
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection_target, Category.comp_id] using
    (exists_relativeEdgeFamilyRetraction e q a y ha).choose_spec.1

/-- 比較の底は、元の同じ切断比較の raw な円柱である。 -/
lemma relativeEdgeFamilyRetraction_base :
    (relativeEdgeFamilyRetraction e q a y ha).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp e q =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyCylinder (e ≫ q) y (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyBase e q a y ha)).homotopy.h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (e ≫ q)) y :=
  (exists_relativeEdgeFamilyRetraction e q a y ha).choose_spec.2.trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyBaseCylinder_raw e q a y ha)

/-- 比較の可変終点は、元の同じ全族の終点を全時刻固定する。 -/
lemma relativeEdgeFamilyRetraction_projection :
    (relativeEdgeFamilyRetraction e q a y ha).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e =
      fst T Δ[1] ≫ a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection e j,
    ← Category.assoc (relativeEdgeFamilyRetraction e q a y ha).h,
    relativeEdgeFamilyRetraction_target]
  simp only [Category.assoc]

/-- 元の固定終点 y の条件も、比較の全時刻で保たれる。 -/
lemma relativeEdgeFamilyRetraction_fixed :
    ((relativeEdgeFamilyRetraction e q a y ha).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) ≫ q =
      SSet.const y := by
  rw [relativeEdgeFamilyRetraction_projection]
  simpa only [Category.assoc, ha] using (SSet.comp_const (fst T Δ[1]) y)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
