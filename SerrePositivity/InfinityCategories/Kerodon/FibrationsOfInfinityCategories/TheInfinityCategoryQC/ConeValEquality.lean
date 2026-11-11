module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit

/-!
概要：全錐の射が等しい二つの指定錐の極限性の比較。
方針：図式の等式を錐の制限から導き、同じ図式の部分型の等式へ戻す。
規約：元の図式の異なる括弧付けを厳密な射の等式で比較する。
使われ方：lax pullback の端点評価と入力の像の錐の照合。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：全錐の射が等しければ指定錐の極限性は同値。
方針：制限を取って図式の等式を得て、錐の部分型の外延性を使う。
規約：極限性の証明を同型類だけの条件へ弱めない。
使われ方：射の合成・指定端点の等式による錐の輸送。 -/
lemma isLimitCone_iff_of_cone_val_eq {J X : SSet.{u}} {r s : J ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone r) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone s) (h : c.val = d.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d := by
  have hrs : r = s := c.property.symm.trans
    ((congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) J ≫ f) h).trans d.property)
  subst s
  have hcd : c = d := Subtype.ext h
  rw [hcd]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
