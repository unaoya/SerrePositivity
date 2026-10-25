module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareChosenPrecomp

/-!
概要：四辺と実四角形が同じ輸送図式の表示変更を、元の指定値へ移す。
方針：実データの等式を消去し、境界条件の証明の一意性を使う。
規約：元の transportIso を選び直さない。使われ方：普遍始点族の厳密な制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 四つの元の区間と実四角形が等しい輸送図式は同じ。 -/
lemma transportIntervalSquare_eq_of_data {B P : SSet.{u}} {a b c d : B _⦋0⦌}
    (s t : TransportIntervalSquare P a b c d)
    (hb : s.bottom = t.bottom) (ht : s.top = t.top)
    (hl : s.left = t.left) (hr : s.right = t.right) (hW : s.square = t.square) : s = t := by
  cases s
  cases t
  cases hb
  cases ht
  cases hl
  cases hr
  cases hW
  rfl

/-- 元の全図式と始点の厳密な表示変更は、元の指定四角形比較の値を保持する。 -/
lemma transportIntervalSquare_transportIso_heq_of_eq {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b c d : B _⦋0⦌}
    (s t : TransportIntervalSquare P a b c d) (f f' : P ⟶ vertexFiber p a)
    (hs : s = t) (hf : f = f') : HEq (s.transportIso p f) (t.transportIso p f') := by
  cases hs
  cases hf
  rfl

end SerrePositivity.InfinityCategories.F2
