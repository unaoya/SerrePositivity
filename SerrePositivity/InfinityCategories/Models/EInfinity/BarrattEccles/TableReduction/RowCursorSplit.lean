module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowCursorValues

/-!
模型。文献の定義との比較は後で
# 指定出力文字の前後への元の抽出行の分割

概要：Berger–Fresse §1.5.7 の成分端点で利用可能行と選択行を前後へ分割する。
方針：同じ行内位置の値の一致と take/drop の連結を使う。
規約：指定文字より後の未選択の利用可能文字も保持する。
使われ方：外側指定値の一出現への内側部分語の代入を実際の行から作る。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor

/-- 概要：元の利用可能行を指定した出力文字の前後に分ける（BF §1.5.7）。
方針：行内位置で take/drop し、その位置の文字を元の語の値へ移す。
規約：分割の後半は未選択の文字も含む。
使われ方：実際の利用可能な逆置換行の一出現の前後表示。 -/
lemma available_split {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {i : Fin (d + 1)} {v : Fin (n + d) → Fin n}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i (List.ofFn v)) (p : Fin (n + d)) (j : Fin (r.val i).val)
    (hp : p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + j.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take j.val ++
        v p :: (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).drop (j.val + 1) := by
  have hb : j.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).length := by
    have := b.bound; have := j.isLt; omega
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take j.val ++
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).drop j.val :=
      (List.take_append_drop j.val _).symm
    _ = _ := by rw [List.drop_eq_getElem_cons hb, ← b.value p j hp]

/-- 概要：元の選択行を指定した出力文字の前後に分ける（BF §1.5.7）。
方針：利用可能行の前後表示の先頭から元の行長だけを取る。
規約：行末位置では選択後半が空。
使われ方：成分端点までの選択語と、その後の同じ行の選択語を保持する。 -/
lemma selected_split {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {i : Fin (d + 1)} {v : Fin (n + d) → Fin n}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i (List.ofFn v)) (p : Fin (n + d)) (j : Fin (r.val i).val)
    (hp : p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + j.val) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take (r.val i).val =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take j.val ++ v p ::
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).drop (j.val + 1)).take
          ((r.val i).val - j.val - 1) := by
  have hb : j.val ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).length := by
    have := b.bound; have := j.isLt; omega
  have ht : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take j.val).length = j.val := by
    exact List.length_take_of_le hb
  calc
    _ = ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take j.val ++
        v p :: (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).drop (j.val + 1)).take (r.val i).val :=
      congrArg (List.take (r.val i).val) (b.available_split p j hp)
    _ = _ := by
      rw [List.take_append, ht, List.take_of_length_le (by rw [ht]; exact Nat.le_of_lt j.isLt)]
      have he : (r.val i).val - j.val = ((r.val i).val - j.val - 1) + 1 := by
        have := j.isLt; omega
      rw [he, List.take_succ_cons]
      simp only [Nat.add_sub_cancel]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor
