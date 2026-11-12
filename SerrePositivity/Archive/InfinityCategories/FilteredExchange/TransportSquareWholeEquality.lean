module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareDataEquality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IntervalSquareConstant

/-!
概要：同じ実全四角形を持つ輸送図式は、四辺も元の指定比較も同じである。
方針：四つの境界条件と区間表示の単射性から元の四辺を回収する。
規約：全図式の一致を入力する。使われ方：元の合成四角形の比較への復帰。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ全実四角形の境界は区間表示の単射性で厳密に決定される。 -/
lemma transportIntervalSquare_eq_of_square {B P : SSet.{u}} {a b c d : B _⦋0⦌}
    (s t : TransportIntervalSquare P a b c d) (h : s.square = t.square) : s = t := by
  apply transportIntervalSquare_eq_of_data s t
  · apply intervalMappingUncurry_injective
    rw [← s.zero, ← t.zero, h]
  · apply intervalMappingUncurry_injective
    rw [← s.one, ← t.one, h]
  · apply intervalMappingUncurry_injective
    rw [← s.inner_zero, ← t.inner_zero, h]
  · apply intervalMappingUncurry_injective
    rw [← s.inner_one, ← t.inner_one, h]
  · exact h

/-- 元の実全四角形の一致は、元の定値終辺を消した指定比較の値も保持する。 -/
lemma transportIntervalSquare_constantTopIso_heq_of_square {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b d : B _⦋0⦌}
    (s t : TransportIntervalSquare P a b d d) (f : P ⟶ vertexFiber p a)
    (hs : intervalMappingUncurry s.top = SSet.const d)
    (ht : intervalMappingUncurry t.top = SSet.const d) (h : s.square = t.square) :
    HEq (s.constantTopIso p f hs) (t.constantTopIso p f ht) := by
  cases transportIntervalSquare_eq_of_square s t h
  rfl

end SerrePositivity.InfinityCategories.F2
