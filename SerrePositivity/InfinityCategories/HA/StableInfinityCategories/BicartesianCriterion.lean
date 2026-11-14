module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BicartesianChoice
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition

/-! # 双カルテジアンな fiber/cofiber の存在による安定性の判定

概要：全ての辺に双カルテジアンな fiber と cofiber があれば pointed ∞ 圏は安定。
方針：任意の零角四角形を同じ辺の選択と比較し、普遍性の選択独立性を使う。
規約：同じ実四角形で両方の普遍性を保持。使われ方：dg 加群 nerve の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 各辺の双カルテジアンな選択から任意の零角の両普遍性の同値を得る。 -/
lemma zeroTriangle_fiber_iff_cofiber_of_bicartesian_choices {X : SSet.{u}} [Quasicategory X]
    (hf : ∀ {x y : X _⦋0⦌}
      (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y),
      ∃ s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare f, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare s.square)
    (hc : ∀ {x y : X _⦋0⦌}
      (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y),
      ∃ s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare s.square)
    (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence t ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t := by
  constructor
  · intro ht
    let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ t.square))
    let s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare f := {
      toZeroTriangle := t
      right_edge := (SSet.yonedaEquiv.symm_apply_apply _).symm
      isPullback := ht }
    obtain ⟨r, hr⟩ := hf f
    exact (r.isPushout_iff s).1 hr
  · intro ht
    let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square))
    let s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f := {
      toZeroTriangle := t
      bottom_edge := (SSet.yonedaEquiv.symm_apply_apply _).symm
      isPushout := ht }
    obtain ⟨r, hr⟩ := hc f
    exact (r.isPullback_iff s).1 hr

/-- Pointed ∞ 圏の全ての辺が双カルテジアンな fiber/cofiber を持てば安定。 -/
theorem isStable_of_bicartesian_choices {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X]
    (hf : ∀ {x y : X _⦋0⦌}
      (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y),
      ∃ s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare f, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare s.square)
    (hc : ∀ {x y : X _⦋0⦌}
      (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y),
      ∃ s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare s.square) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X where
  toHasZeroVertex := inferInstance
  fiber_exists f := ⟨(hf f).choose⟩
  cofiber_exists f := ⟨(hc f).choose⟩
  fiber_iff_cofiber t := zeroTriangle_fiber_iff_cofiber_of_bicartesian_choices hf hc t

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
