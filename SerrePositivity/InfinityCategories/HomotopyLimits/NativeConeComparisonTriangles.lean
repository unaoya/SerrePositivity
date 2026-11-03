module

public import SerrePositivity.InfinityCategories.Core.ConeEdgeCompatibility
public import SerrePositivity.InfinityCategories.Core.CatInfinity.NativeConeLeg

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 二つの join 脚の表示は、端点も全一単体も同じ元の native 脚である。 -/
lemma nativeConeLeg_eq_derived {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (k : K _⦋0⦌) : F2.nativeConeLeg c k = derivedConeLeg c k := by
  apply SSet.Truncated.Edge.ext
  change c.val.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (F2.coneLegInclusion k)) =
    SSet.yonedaEquiv (F2.coneLegInclusion k ≫ c.val)
  rw [SSet.yonedaEquiv_comp]

/-- 元の slice 比較の頂点辺と、比較先・比較元の native 脚は実際の合成三角形を持つ。 -/
def nativeConeComparisonLegTriangle {K X : SSet.{u}} {p : K ⟶ X} {c d : JoinCone p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (sliceOver p)) c d)
    (k : K _⦋0⦌) : SSet.Truncated.Edge.CompStruct
      (e.map ((truncation 2).map (sliceOverProjection p)))
      (F2.nativeConeLeg d k) (F2.nativeConeLeg c k) := by
  rw [nativeConeLeg_eq_derived, nativeConeLeg_eq_derived]
  exact derivedConeLegCompStruct e k

/-- 元の native 脚の可換性は、同じ元の三角形のホモトピー圏での式を与える。 -/
lemma nativeConeComparisonLeg_homMk {K X : SSet.{u}} {p : K ⟶ X}
    {c d : JoinCone p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (sliceOver p)) c d)
    (k : K _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk
        (e.map ((truncation 2).map (sliceOverProjection p))) ≫
      SSet.Truncated.HomotopyCategory.homMk (F2.nativeConeLeg d k) =
        SSet.Truncated.HomotopyCategory.homMk (F2.nativeConeLeg c k) :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk (nativeConeComparisonLegTriangle e k)

end SerrePositivity.InfinityCategories.HomotopyLimits
