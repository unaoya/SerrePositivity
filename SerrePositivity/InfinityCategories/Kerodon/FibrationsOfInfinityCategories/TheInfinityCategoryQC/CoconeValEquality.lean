module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-!
概要：全余錐の射が等しい二つの指定余錐の余極限性の比較。
方針：図式の等式を左の制限から導き、部分型の等式へ戻す。
規約：異なる図式の括弧付けも厳密な射の等式で比較する。
使われ方：lax pullback の両端と入力の像の余錐の照合。

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

/-- 概要：全余錐の射が等しければ余極限性は同値。
方針：図式の制限と余錐の部分型の外延性を使う。
規約：元の指定余錐を保持する。
使われ方：端点評価と射の合成による余極限性の輸送。 -/
lemma isColimitCone_iff_of_cocone_val_eq {J X : SSet.{u}} {r s : J ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone s) (h : c.val = d.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d := by
  have hrs : r = s := c.property.symm.trans
    ((congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J (Δ[0] : SSet.{u}) ≫ f) h).trans d.property)
  subst s
  have hcd : c = d := Subtype.ext h
  rw [hcd]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
