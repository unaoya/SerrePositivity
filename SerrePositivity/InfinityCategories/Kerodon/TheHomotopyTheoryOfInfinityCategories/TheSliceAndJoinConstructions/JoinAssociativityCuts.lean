module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-!
概要：三因子の join の二つの切断位置を単体作用で引き戻す計算。
方針：先頭区間の逆像の特徴づけを用い、左区間への制限と右区間の原点移動を比較する。
規約：添字は空を許す頂点数であり、面と退化を同時に扱う。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS） の反復 slice に使う join の結合の自然性。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：切断位置を後ろへ動かすと引き戻した切断位置も後ろへ動く。
方針：先頭区間の逆像の有限集合の包含から濃度を比較する。
規約：α の始域・終域に空区間を許す。
使われ方：Kerodon §4.3.5（Tag 017V） の三因子の join の二つの切断の順序。 -/
lemma joinPullCut_mono {m n : ℕ} (α : Fin m →o Fin n) {a b : ℕ} (h : a ≤ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α b := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut
  apply Finset.card_le_card
  intro i hi
  rcases Finset.mem_filter.mp hi with ⟨hm, hi⟩
  exact Finset.mem_filter.mpr ⟨hm, lt_of_lt_of_le hi h⟩

/-- 概要：左区間に制限してから前の切断を引き戻しても元の切断の引き戻しと一致する。
方針：引き戻した切断より前の各頂点で、元の順序写像の同じ値を比較する。
規約：二つの切断位置に a≤b を要求し、空の先頭区間も含む。
使われ方：HTT §1.2.8 の左括弧の join の単体作用の再結合。 -/
lemma joinPullCut_leftMap {m n : ℕ} (α : Fin m →o Fin n) {a b : ℕ} (h : a ≤ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α b) a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.cut_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le _ _) (joinPullCut_mono α h)
  intro i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α b) a i]
  change (α ⟨i.val, lt_of_lt_of_le i.isLt (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α b)⟩).val < a ↔
    i.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff α a
    ⟨i.val, lt_of_lt_of_le i.isLt (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α b)⟩).symm

/-- 概要：右区間の原点を移して後の切断を引き戻すと二つの引き戻した切断の差になる。
方針：右区間の頂点の像が前の切断以後にあることと先頭区間の逆像の特徴づけを使う。
規約：切断位置 a≤b、差は自然数の切り捨て減算。
使われ方：HTT §1.2.8 の右括弧の join の単体作用の再結合。 -/
lemma joinPullCut_rightMap {m n : ℕ} (α : Fin m →o Fin n) {a b : ℕ} (h : a ≤ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α a) (b - a) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α b - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.cut_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le _ _) (by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α b
    omega)
  intro i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α a) (b - a) i]
  let j : Fin m := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + i.val, by have := i.isLt; omega⟩
  have hj : a ≤ (α j).val := by
    apply Nat.le_of_not_lt
    intro ha
    have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff α a j).mpr ha
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + i.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a at hi
    omega
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff α b j
  have hab := joinPullCut_mono α h
  change (α j).val - a < b - a ↔ i.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α b - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α a + i.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α b ↔ (α j).val < b at hc
  omega

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
