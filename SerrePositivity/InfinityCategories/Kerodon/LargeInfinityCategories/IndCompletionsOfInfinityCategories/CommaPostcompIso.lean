module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PointSlicePostcompIso

/-!
概要：二つの同型からなる可換正方形が誘導する元の comma 写像は同型。
方針：正規化した slice 作用を含む引き戻しの同型として判定する。
規約：元の始域図式と指定終点を保持する。
使われ方：形状同型による diagram comma 制限。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：同型の可換正方形による comma 作用は同型。
方針：引き戻しの三つの同型。規約：元の写像。使われ方：制限の基底ケース。 -/
lemma commaPostcomp_isIso {A B X Y : SSet.{u}} (δ : A ⟶ X) (ε : B ⟶ Y)
    (f : A ⟶ B) (g : X ⟶ Y) (h : δ ≫ g = f ≫ ε) (x : X _⦋0⦌)
    [IsIso f] [IsIso g] : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.commaPostcomp δ ε f g h x) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSlicePostcomp_isIso g x
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.commaPostcomp δ ε f g h x =
      pullback.map δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x)) ε
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (g.app (Opposite.op ⦋0⦌) x)))
        f (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSlicePostcomp g x) g h (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSlicePostcomp_projection g x).symm := by
    apply pullback.hom_ext <;> simp [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.commaPostcomp]
  rw [he]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
