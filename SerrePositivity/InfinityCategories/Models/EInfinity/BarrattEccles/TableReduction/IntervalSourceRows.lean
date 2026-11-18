module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock

/-!
模型。文献の定義との比較は後で
# 切り出した成分行の元の連続区間

概要：Berger–Fresse §1.5.7 の成分抽出が元の頂点行を同じ順に使うことを確認する。
方針：元の二行分割の take/drop を行数だけで評価する。
規約：始終行の選択長さだけを変更し、置換行自身は変更しない。
使われ方：切り出した証跡を元の shuffle 経路の頂点列へ接続する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：二つの指定要素を端とする元のリストの連続区間（BF §1.5.7）。
方針：先行部分を drop し、中間全体と終要素まで take する。
規約：両端を含む。
使われ方：成分行の元の位置と順序を確認する。 -/
lemma list_interval_at_split {α : Type*} (xs pre middle after : List α) (x y : α)
    (i j : ℕ) (hs : xs = pre ++ x :: (middle ++ y :: after))
    (hi : pre.length = i) (hj : pre.length + 1 + middle.length = j) :
    (xs.drop i).take (j - i + 1) = x :: (middle ++ [y]) := by
  rw [hs, ← hi, List.drop_append_length]
  have he : j - pre.length + 1 = (middle.length + 1) + 1 := by omega
  rw [he, List.take_succ_cons, List.take_length_add_append]
  simp only [List.take_succ_cons, List.take_zero]

/-- 概要：同じ行だけを取る元の Schedule の区間（BF §1.5.7）。
方針：指定位置からの drop の先頭を元の行の評価に直す。
規約：最終行にも適用する。
使われ方：一行成分の元の置換行を指定する。 -/
lemma rows_interval_singleton {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i : Fin (d + 1)) :
    (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).drop i.val).take 1).map Prod.fst = [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i] := by
  have hi : i.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).length := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn] using i.isLt
  rw [List.drop_eq_getElem_cons hi]
  simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.getElem_ofFn]
  rfl

/-- 概要：成分抽出の各置換行は元の Schedule の連続区間（BF §1.5.7）。
方針：始終行の長さの変更を fst で忘れ、二行分割の区間公式を使う。
規約：置換行の順序を厳密に保持する。
使われ方：複数行成分の各段を元の shuffle 頂点へ照合する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock.interval_source_rows {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {receiver donor : Fin (d + 1)} {out : List (Fin n)}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor out) (a b : ℕ) :
    (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver, a) :: (c.middle ++ [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, b)])).map Prod.fst) =
      (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).drop receiver.val).take (donor.val - receiver.val + 1)).map Prod.fst := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.list_interval_at_split _ _ _ _ _ _ _ _ c.split c.before_length c.middle_length]
  simp only [List.map_cons, List.map_append, List.map_nil]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
