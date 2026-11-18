module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowCursorValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowBoundary

/-!
模型。文献の定義との比較は後で
# 行内の指定位置からの元の成功抽出

概要：Berger–Fresse §1.5.7 の成分端点が行内部にあるときの残りの抽出を構成する。
方針：端点より前の現在行の文字を除外し、現在行の残りと元の後続抽出を接続する。
規約：端点の文字は残し、行末以外の元の除外更新と厳密に一致させる。
使われ方：同じ内側行を共有する重なる分割の隣接成分を処理する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor

/-- 概要：行内位置より前を除外した利用可能行は元のその位置からの末尾（BF §1.5.7）。
方針：逆置換行の重複のなさと既存の先頭除外公式を使う。
規約：行内位置そのものの文字は除外しない。
使われ方：重なる分割の共有端点から同じ現在行を再開する。 -/
lemma available_remainder {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {i : Fin (d + 1)} {out : List (Fin n)} (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i out)
    (j : Fin (r.val i).val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (b.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take j.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).drop j.val := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_after_take _ _ (List.nodup_ofFn_ofInjective (w i).symm.injective) j.val

/-- 概要：行内位置から残りを抽出した除外更新は元の全行の更新（BF §1.5.7）。
方針：前半の take と残りの末尾以外の take を take_add で連結する。
規約：元の選択行の最後の文字を同じく残す。
使われ方：分割成分の途中から進めても元の後続状態に戻ることを確認する。 -/
lemma remainder_removed_eq {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {i : Fin (d + 1)} {out : List (Fin n)} (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i out)
    (j : Fin (r.val i).val) :
    (b.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take j.val) ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (b.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take j.val)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take ((r.val i).val - j.val - 1) =
      b.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take ((r.val i).val - 1) := by
  rw [b.available_remainder j, List.append_assoc, ← List.take_add]
  have he : j.val + ((r.val i).val - j.val - 1) = (r.val i).val - 1 := by
    have := j.isLt; omega
  rw [he]

/-- 概要：行内位置から元の現在行の残りと後続表を抽出できる（BF §1.5.7）。
方針：残り行長の成功条件と元の後続状態への一致を既存の成功規則に渡す。
規約：追加の抽出成功仮定は不要。
使われ方：重なる分割の部分語の始点から元の抽出を再開する。 -/
lemma remainder_success {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {i : Fin (d + 1)} {out : List (Fin n)} (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i out)
    (j : Fin (r.val i).val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i, (r.val i).val - j.val) :: b.after)
      (b.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take j.val) =
      some (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).drop j.val).take
        ((r.val i).val - j.val) ++ b.tail) := by
  have hr : 0 < (r.val i).val - j.val := by have := j.isLt; omega
  have hb : (r.val i).val - j.val ≤
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (b.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take j.val)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).length := by
    rw [b.available_remainder j, List.length_drop]
    have := b.bound
    omega
  have ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows b.after
      ((b.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take j.val) ++
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (b.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take j.val)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take ((r.val i).val - j.val - 1)) = some b.tail := by
    rw [b.remainder_removed_eq j]
    exact b.tail_success
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success _ _ _ _ _ hr hb ht
  simpa only [b.available_remainder j, Nat.sub_sub] using hs

/-- 概要：行内位置からの成功抽出の出力は元の語のその位置からの末尾（BF §1.5.7）。
方針：元の三ブロック出力で先行部分と行内前半を drop する。
規約：行末位置では現在行の残りは一文字。
使われ方：元の語の成分始点と再開した抽出の出力を照合する。 -/
lemma output_drop {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {i : Fin (d + 1)} {v : Fin (n + d) → Fin n}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i (List.ofFn v)) (p : Fin (n + d)) (j : Fin (r.val i).val)
    (hp : p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + j.val) :
    (List.ofFn v).drop p.val =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).drop j.val).take ((r.val i).val - j.val) ++
        b.tail := by
  calc
    _ = (b.selectedBefore.flatten ++
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take (r.val i).val ++ b.tail)).drop p.val :=
      congrArg (List.drop p.val) b.output_eq
    _ = _ := by
      rw [hp, ← b.prefix_length, List.drop_length_add_append,
        List.drop_append_of_le_length (by
          rw [List.length_take, Nat.min_eq_left b.bound]
          exact Nat.le_of_lt j.isLt), List.drop_take]

/-- 概要：行内位置から元の語のその位置以降を実際に抽出できる（BF §1.5.7）。
方針：元の後続抽出と元の語の末尾の表示を同じ行内位置で照合する。
規約：行内の位置と語全体の位置の座標一致だけを要求する。
使われ方：内側分割成分の開始位置から元の抽出を再開する。 -/
lemma remainder_success_eq_drop {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {i : Fin (d + 1)} {v : Fin (n + d) → Fin n}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i (List.ofFn v)) (p : Fin (n + d)) (j : Fin (r.val i).val)
    (hp : p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + j.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i, (r.val i).val - j.val) :: b.after)
      (b.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take j.val) =
      some ((List.ofFn v).drop p.val) := by
  rw [b.output_drop p j hp]
  exact b.remainder_success j

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor
