module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PointSliceIdentity

/-!
概要：任意の元の点の slice の恒等頂点は、射影で同じ元の点写像を厳密に回収する。
方針：恒等錐の全写像を uncurry し、元の点の Yoneda 表示へ戻す。
規約：元の点写像を取り替えない。
使われ方：終点面の相対比較に、同じ元の底余錐と恒等終点を渡す。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：恒等頂点の全点写像の元の射影は、同じ元の点写像。
方針：恒等錐の全写像を回収。規約：全射の等号。使われ方：終点面の固定条件。 -/
lemma pointSliceIdentity_point_projection {X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSliceIdentity p) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p = p := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ SSet.const (SSet.yonedaEquiv p) = p
  rw [SSet.comp_const, ← SSet.yonedaEquiv_symm_zero, Equiv.symm_apply_apply]
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
