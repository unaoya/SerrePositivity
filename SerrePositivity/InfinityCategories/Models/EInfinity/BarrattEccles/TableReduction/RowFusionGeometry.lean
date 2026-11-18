module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowFusionBoundary

/-!
模型。文献の定義との比較は後で
# 境界行融合の行数と元の行の保存

概要：Berger–Fresse §1.5.7 の共有行融合で行数が一つ減り、元の行順が保たれることを示す。
方針：左最終行と右先頭行を分離して実際の融合を評価する。
規約：二つのブロックは非空。選択長さの条件は不要。
使われ方：全融合表の行数と経路上の元の行列表示の照合。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*}

/-- 概要：非空ブロック二つの融合は行数を一つだけ減らす（BF §1.5.7）。
方針：左末尾と右先頭をまとめた一行を数える。
規約：自然数の減算を避けて一を左辺に足す。
使われ方：全融合表の次数＋1の行数を証明する。 -/
lemma fuseBoundary_length (left right : List (List α × ℕ)) (hl : left ≠ []) (hr : right ≠ []) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary left right).length + 1 = left.length + right.length := by
  obtain ⟨pre, he⟩ := List.getLast?_eq_some_iff.mp (List.getLast?_eq_some_getLast hl)
  have hs : ∃ pre row r, left = pre ++ [(row, r)] :=
    ⟨pre, (left.getLast hl).1, (left.getLast hl).2, he⟩
  obtain ⟨pre, row, r, rfl⟩ := hs
  cases right with
  | nil => exact (hr rfl).elim
  | cons p tail =>
    obtain ⟨other, s⟩ := p
    simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary, List.length_append, Nat.add_assoc, Nat.add_left_comm]

/-- 概要：融合後の行列は左の全行と右の先頭以外を同じ順に持つ（BF §1.5.7）。
方針：選択長さを忘れると融合行は左最終行そのものになる。
規約：共有行一致は抽出成功に必要だが、この行列表示には不要。
使われ方：全融合表と各成分の元の置換頂点列を照合する。 -/
lemma fuseBoundary_fst (left right : List (List α × ℕ)) (hl : left ≠ []) (hr : right ≠ []) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary left right).map Prod.fst = left.map Prod.fst ++ (right.map Prod.fst).tail := by
  obtain ⟨pre, he⟩ := List.getLast?_eq_some_iff.mp (List.getLast?_eq_some_getLast hl)
  have hs : ∃ pre row r, left = pre ++ [(row, r)] :=
    ⟨pre, (left.getLast hl).1, (left.getLast hl).2, he⟩
  obtain ⟨pre, row, r, rfl⟩ := hs
  cases right with
  | nil => exact (hr rfl).elim
  | cons p tail =>
    obtain ⟨other, s⟩ := p
    simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary, List.map_append, List.append_assoc]

/-- 概要：融合後の各行は両入力の行が満たす同じ条件を満たす（BF §1.5.7）。
方針：融合後の行の列の表示から元の行への所属を戻す。
規約：条件は選択長さではなく元の行に依存する。
使われ方：全融合表の全行が合成 arity と同じ長さを持つことを示す。 -/
lemma fuseBoundary_all_rows (P : List α → Prop) (left right : List (List α × ℕ))
    (hl : left ≠ []) (hr : right ≠ [])
    (hleft : ∀ row ∈ left.map Prod.fst, P row)
    (hright : ∀ row ∈ right.map Prod.fst, P row) :
    ∀ row ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary left right).map Prod.fst, P row := by
  intro row hm
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_fst left right hl hr] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hleft row hm
  · exact hright row (List.mem_of_mem_tail hm)

/-- 概要：同じ頂点を共有する二語の連結では前後どちらのコピーも省ける（BF §1.5.7）。
方針：左末尾と右先頭を分離し、同じ共有要素を付け直す。
規約：両側の語は非空。
使われ方：融合表の右先頭削除を経路頂点列の左末尾削除へ移す。 -/
lemma overlap_append {β : Type*} (left right : List β) (hl : left ≠ []) (hr : right ≠ [])
    (hj : left.getLast? = right.head?) : left ++ right.tail = left.dropLast ++ right := by
  obtain ⟨pre, he⟩ := List.getLast?_eq_some_iff.mp (List.getLast?_eq_some_getLast hl)
  have hs : ∃ pre a, left = pre ++ [a] := ⟨pre, left.getLast hl, he⟩
  obtain ⟨pre, a, rfl⟩ := hs
  cases right with
  | nil => exact (hr rfl).elim
  | cons b tail =>
    have he : a = b := by simpa using hj
    subst b
    simp only [List.tail_cons, List.dropLast_concat, List.append_assoc, List.singleton_append]

/-- 概要：境界融合の行列を共有左末尾を省く形でも表示できる（BF §1.5.7）。
方針：元の右先頭削除表示を共有行の一致で移す。
規約：行長を忘れた行列の表示。
使われ方：全融合表を実際の経路頂点列と同じ連結規則へ直す。 -/
lemma fuseBoundary_fst_dropLast (left right : List (List α × ℕ))
    (hl : left ≠ []) (hr : right ≠ [])
    (hj : (left.map Prod.fst).getLast? = (right.map Prod.fst).head?) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary left right).map Prod.fst =
      (left.map Prod.fst).dropLast ++ right.map Prod.fst := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_fst left right hl hr]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.overlap_append _ _ (fun he => hl (List.map_eq_nil_iff.mp he))
    (fun he => hr (List.map_eq_nil_iff.mp he)) hj

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
