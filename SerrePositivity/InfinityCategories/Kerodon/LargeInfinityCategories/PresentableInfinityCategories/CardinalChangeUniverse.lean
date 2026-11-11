module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CardinalChangeBound
public import Mathlib.SetTheory.Cardinal.Order

/-!
概要：濃度変更の明示的な冪の評価を、同じ二濃度の宇宙持ち上げへ輸送する。
方針：持ち上げた上限未満の濃度を元の宇宙に戻し、元の冪の評価を使う。
規約：より大きい新たな上限を選ばず、元の κ・μ を保持する。
使われ方：N の大きい宇宙の全 Hom 錐へ μ-filtered 極限交換を渡す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 元の濃度変更の全ての冪の評価は、任意の宇宙持ち上げで保持される。 -/
lemma IsCardinalChangeBound.lift {κ μ : Cardinal.{u}} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound (Cardinal.lift.{v} κ) (Cardinal.lift.{v} μ) := by
  refine ⟨by simpa only [Cardinal.lift_lt] using h.1, ?_⟩
  intro α β hα hβ
  obtain ⟨a, ha, rfl⟩ := Cardinal.lt_lift_iff.mp hα
  obtain ⟨b, hb, rfl⟩ := Cardinal.lt_lift_iff.mp hβ
  simpa only [← Cardinal.lift_power, Cardinal.lift_lt] using h.2 a b ha hb

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
