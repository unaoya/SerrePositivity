module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SplitUniqueness
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalDeletionPair

/-!
模型。文献の定義との比較は後で
# 順方向の削除値と逆探索の直前値

概要：Berger–Fresse §1.4.4 の受け取り行を延長した出力の直前値を計算する。
方針：変更されない先行証跡の次の行を評価し、元の選択末尾の値へ戻す。
規約：変更後の出力は実際の成功抽出のもの。
使われ方：逆構成の解放値を順方向の削除値へ同定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：正の take の指定された末尾は実際の末尾位置の値（BF §1.4.4）。
方針：take の末尾公式と指定した連結表示を比較する。
規約：長さは元のリスト長以下。
使われ方：受け取り行の前の末尾の評価を簡潔に行う。 -/
lemma take_end_value {α : Type*} (xs : List α) (r : ℕ) (hr : 0 < r)
    (hb : r ≤ xs.length) (a : α) (he : xs.take r = xs.take (r - 1) ++ [a]) :
    xs[r - 1]'(by omega) = a := by
  have hi : r - 1 < xs.length := by omega
  have ht : xs.take r = xs.take (r - 1) ++ [xs[r - 1]] := by
    have hs := List.take_succ_eq_append_getElem hi
    have heq : r - 1 + 1 = r := by omega
    simpa only [heq] using hs
  have hv := List.append_cancel_left (ht.symm.trans he)
  simpa only [List.singleton_inj] using hv

/-- 概要：延長した受け取り行の新しい行末の直前値は元の削除値（BF §1.4.4）。
方針：共通の先行抽出の次の行を旧末尾位置で評価する。
規約：元の削除値は旧受け取り行の末尾として指定する。
使われ方：順から逆の往復で探索する値を一致させる。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock.forward_released_value {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {receiver : Fin d} {donor : Fin (d + 1)} {out : List (Fin n)}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver.castSucc donor out) (ho : receiver.castSucc < donor)
    (hd : 1 < (r.val donor).val) (a : Fin n)
    (ha : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc)).take
      (r.val receiver.castSucc).val =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc)).take
          ((r.val receiver.castSucc).val - 1) ++ [a])
    (new : List (Fin n))
    (hnew : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver.castSucc
      (ne_of_gt ho) hd)) [] = some new) (p : Fin new.length)
    (hp : p.val + 1 = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver.castSucc + (r.val receiver.castSucc).val) :
    new[p.val] = a := by
  have hrows := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_transfer_blocks w r donor receiver.castSucc (ne_of_gt ho) hd
    b.before b.middle b.after b.split b.before_length b.middle_length
  have hsuccess : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (b.before ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc, (r.val receiver.castSucc).val + 1) ::
        (b.middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val - 1) :: b.after)) [] = some new := by
    simpa only [hrows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow] using hnew
  have hr := r.property.1 receiver.castSucc
  obtain ⟨hb, hv⟩ := b.before_trace.value_in_next_row (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc)
    ((r.val receiver.castSucc).val + 1) _ new hsuccess p
    ((r.val receiver.castSucc).val - 1) (by omega) (by have := b.prefix_length; omega)
  exact hv.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.take_end_value _ _ hr b.receiver_bound a ha)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
