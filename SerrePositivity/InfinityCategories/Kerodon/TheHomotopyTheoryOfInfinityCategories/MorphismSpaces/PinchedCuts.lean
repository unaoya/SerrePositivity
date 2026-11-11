module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedIndex

/-! # 最終頂点を含む有限集合の削除と切断

概要：最終点を加えた集合の削除・左右切断・符号の個数を先頭集合の式に直す。
方針：先頭頂点と最終点で所属条件を計算する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：右 pinched 方程式の線形化。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：先頭点の削除と最終点の追加は可換。
方針：最終点と先頭点で所属条件を比較する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：削除項を線形成分へ戻す。 -/
lemma erase_withLast {n : ℕ} (J : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J).erase j.castSucc = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast (J.erase j) := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast, ne_of_gt (Fin.castSucc_lt_last j)]
  | cast i => simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast]

/-- 概要：先頭点までの左切断は先頭集合の左切断の像。
方針：最終点が左切断に入らないことと先頭埋め込みの順序保存を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：合成の先に作用する成分を定値面で計算する。 -/
lemma left_withLast {n : ℕ} (J : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J).filter (· ≤ j.castSucc) = (J.filter (· ≤ j)).image Fin.castSucc := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast, not_le_of_gt (Fin.castSucc_lt_last j)]
  | cast i => simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast]

/-- 概要：先頭点からの右切断は先頭集合の右切断に最終点を加えた集合。
方針：先頭埋め込みの順序保存と最終点の最大性を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：合成の後に作用する成分を線形成分で計算する。 -/
lemma right_withLast {n : ℕ} (J : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J).filter (j.castSucc ≤ ·) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast (J.filter (j ≤ ·)) := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast, Fin.le_last j.castSucc]
  | cast i => simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast]

/-- 概要：先頭点より大きい点の集合は元の厳密右切断に最終点を加えた集合。
方針：先頭埋め込みの順序保存と最終点が全先頭点より大きいことを使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：線形方程式の符号の指数。 -/
lemma above_withLast {n : ℕ} (J : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J).filter (j.castSucc < ·) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast (J.filter (j < ·)) := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast]
  | cast i => simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast]

/-- 概要：符号の指数は元の厳密右切断の個数より一大きい。
方針：厳密右切断の同定と最終点追加の濃度の計算を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：N0.3 の符号への同定。 -/
lemma card_above_withLast {n : ℕ} (J : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J).filter (j.castSucc < ·)).card = (J.filter (j < ·)).card + 1 := by
  rw [above_withLast, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
