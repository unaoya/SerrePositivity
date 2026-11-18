module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowCursorValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowBoundary
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.LastRowSaturation

/-!
模型。文献の定義との比較は後で
# 元の最終行の最後の位置で残る一文字

概要：Berger–Fresse §1.5.7 の最後の内側位置で利用可能行が末尾一文字になることを示す。
方針：元の最終行の飽和性と行内再開の drop を使う。
規約：元の成功証跡の最終行を使い、新たな終端条件を仮定しない。
使われ方：指定値の最終除外を跨ぐ外側水平成分の転送。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor

/-- 概要：元の最終行の後続行列は空（BF §1.5.7）。
方針：元の全行数と最終行の前の行数から後続の長さを計算する。
規約：次数零の一行の表も含む。
使われ方：最終行の後続抽出と出力末尾を確定する。 -/
lemma last_after_eq_nil {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {out : List (Fin n)} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r (Fin.last d) out) : c.after = [] := by
  have hl := congrArg List.length c.split
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn, List.length_append, List.length_cons] at hl
  have hb : c.before.length = d := c.before_length
  apply List.length_eq_zero_iff.mp
  omega

/-- 概要：元の最終行の利用可能長はその実際の選択長（BF §1.5.7）。
方針：同じ cursor の先行証跡を既存の最終行飽和性へ渡す。
規約：最終行の未選択文字はない。
使われ方：最終位置での行内再開が一文字だけになることを導く。 -/
lemma last_available_length {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d} {out : List (Fin n)} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r (Fin.last d) out) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w (Fin.last d))).length = (r.val (Fin.last d)).val := by
  have he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = c.before ++ [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w (Fin.last d), (r.val (Fin.last d)).val)] := by
    simpa only [c.last_after_eq_nil] using c.split
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.last_row_available_length w r c.before he c.selectedBefore c.removed c.before_trace

/-- 概要：元の最終行の出力の後続部分は空（BF §1.5.7）。
方針：空の後続行列からの元の成功を評価する。
規約：除外状態には依存しない。
使われ方：元の最終位置を現在行の最後の列へ同定する。 -/
lemma last_tail_eq_nil {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {out : List (Fin n)} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r (Fin.last d) out) : c.tail = [] := by
  have ht := c.tail_success
  rw [c.last_after_eq_nil, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_nil, Option.some.injEq] at ht
  exact ht.symm

/-- 概要：元の最後の出力位置で進めた最終行は末尾一文字だけ（BF §1.5.7）。
方針：全出力長から最終列を求め、飽和した行をその列まで drop する。
規約：現在行の列は元の出力位置と同じ座標で指定する。
使われ方：内側の最終状態の singleton の利用可能行。 -/
lemma final_available_singleton {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {i : Fin (d + 1)} {v : Fin (n + d) → Fin n}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor w r i (List.ofFn v)) (hi : i = Fin.last d)
    (q : Fin (n + d)) (hq : q.val + 1 = n + d) (j : Fin (r.val i).val)
    (hp : q.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + j.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (c.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i)).take j.val)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i) = [v q] := by
  subst i
  have hl := congrArg List.length c.output_eq
  simp only [List.length_ofFn, List.length_append, List.length_take,
    Nat.min_eq_left c.bound, c.last_tail_eq_nil, List.length_nil, Nat.add_zero] at hl
  rw [c.prefix_length] at hl
  have hj : j.val + 1 = (r.val (Fin.last d)).val := by omega
  have hlen := c.last_available_length
  have hb : j.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w (Fin.last d))).length := by
    rw [hlen]
    exact j.isLt
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_after_take c.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w (Fin.last d))
    (List.nodup_ofFn_ofInjective (w (Fin.last d)).symm.injective) j.val,
    List.drop_eq_getElem_cons hb, ← c.value q j hp, hj, ← hlen, List.drop_length]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleRowCursor
