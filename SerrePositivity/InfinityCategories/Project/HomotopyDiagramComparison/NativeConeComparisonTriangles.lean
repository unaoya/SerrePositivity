module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeEdgeCompatibility
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg

/-!
概要：元の同じ slice 内の比較辺と、元の native 全錐の各脚の合成三角形を回収する。
方針：既存の join 制限による三角形を、元の native 脚の全一単体へ厳密に照合する。
規約：元の全錐と指定辺を変更しない。quasicategory 性は不要。
使われ方：有限関手積錐の比較を、元の全評価脚の coherent 合成へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 二つの join 脚の表示は、端点も全一単体も同じ元の native 脚である。 -/
lemma nativeConeLeg_eq_derived {K X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (k : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c k = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg c k := by
  apply SSet.Truncated.Edge.ext
  change c.val.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion k)) =
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion k ≫ c.val)
  rw [SSet.yonedaEquiv_comp]

/-- 元の slice 比較の頂点辺と、比較先・比較元の native 脚は実際の合成三角形を持つ。 -/
def nativeConeComparisonLegTriangle {K X : SSet.{u}} {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) c d)
    (k : K _⦋0⦌) : SSet.Truncated.Edge.CompStruct
      (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg d k) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c k) := by
  rw [nativeConeLeg_eq_derived, nativeConeLeg_eq_derived]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLegCompStruct e k

/-- 元の native 脚の可換性は、同じ元の三角形のホモトピー圏での式を与える。 -/
lemma nativeConeComparisonLeg_homMk {K X : SSet.{u}} {p : K ⟶ X}
    {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) c d)
    (k : K _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk
        (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p))) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg d k) =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c k) :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk (nativeConeComparisonLegTriangle e k)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
