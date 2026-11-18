module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.BlockWords
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TransferBounds

/-!
模型。文献の定義との比較は後で
# ブロックの削除後出力一致を元の Schedule へ戻す

概要：Berger–Fresse §1.4.4 の二行の比較の前へ元の先行行を連結する。
方針：二行以外の行リストの一致と先行抽出証跡を使い、削除位置を先行出力長だけずらす。
規約：元と変更後の抽出はいずれも既存 reduceRows で検証する。
使われ方：局所ブロック比較を実際の相殺相手の Schedule の成功出力へ移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：先行語を付けた後の削除位置はその長さだけずれる（BF §1.4.4）。
方針：eraseIdx の連結の右側の分岐を評価する。
規約：削除位置が語長を超える場合も同じ式が成り立つ。
使われ方：局所ブロックの削除後出力の一致を全出力へ移す。 -/
lemma eraseIdx_prefix_add {α : Type*} (pre xs : List α) (i : ℕ) :
    (pre ++ xs).eraseIdx (pre.length + i) = pre ++ xs.eraseIdx i := by
  rw [List.eraseIdx_append, ite_eq_right (by omega), Nat.add_sub_cancel_left]

/-- 概要：二行ブロックの比較から実際の変更後 Schedule の出力を構成（BF §1.4.4）。
方針：元の先行抽出を両側に連結し、削除位置の先行出力長を足す。
規約：ブロックの二つの削除後出力の一致を、全出力の具体的な位置で保持する。
使われ方：通常・最終末尾の二つの局所抽出を同じ全体の相殺対へ戻す。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock.lift_transfer {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {receiver donor : Fin (d + 1)} {out : List (Fin n)}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor out) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (hne : donor ≠ receiver) (hd : 1 < (r.val donor).val)
    (old changed : List (Fin n)) (i : ℕ)
    (hold : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver, (r.val receiver).val) ::
      (b.middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val) :: b.after)) b.removed = some old)
    (hnew : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver, (r.val receiver).val + 1) ::
      (b.middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val - 1) :: b.after)) b.removed = some changed)
    (hdel : old.eraseIdx i = changed.eraseIdx (r.val receiver).val) :
    ∃ new, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver hne hd)) [] = some new ∧
      out.eraseIdx (b.selectedBefore.flatten.length + i) =
        new.eraseIdx (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver + (r.val receiver).val) := by
  have holdFull := b.before_trace.append _ _ hold
  have hnewFull := b.before_trace.append _ _ hnew
  have holdRows : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (b.selectedBefore.flatten ++ old) := by
    rw [b.split]
    exact holdFull
  have hout : out = b.selectedBefore.flatten ++ old := Option.some.inj (h.symm.trans holdRows)
  have hsplitNew := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_transfer_blocks w r donor receiver hne hd b.before b.middle b.after
    b.split b.before_length b.middle_length
  refine ⟨b.selectedBefore.flatten ++ changed, ?_, ?_⟩
  · rw [hsplitNew]
    exact hnewFull
  · calc
      _ = (b.selectedBefore.flatten ++ old).eraseIdx
          (b.selectedBefore.flatten.length + i) := congrArg
            (fun xs => xs.eraseIdx (b.selectedBefore.flatten.length + i)) hout
      _ = b.selectedBefore.flatten ++ old.eraseIdx i := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.eraseIdx_prefix_add _ _ _
      _ = b.selectedBefore.flatten ++ changed.eraseIdx (r.val receiver).val := by rw [hdel]
      _ = _ := by rw [← b.prefix_length, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.eraseIdx_prefix_add]

/-- 概要：行長移動で受け取り行より前の開始位置は変わらない（BF §1.4.4）。
方針：元と相手の table に共通する先行行の長さの和を比較する。
規約：同じ抽出証明書の行の分割を使う。
使われ方：新しい行末の削除位置と行番号の符号を同定する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock.offset_transfer_receiver {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {receiver donor : Fin (d + 1)} {out : List (Fin n)}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor out) (hne : donor ≠ receiver)
    (hd : 1 < (r.val donor).val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver hne hd) receiver =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver := by
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_transfer_blocks w r donor receiver hne hd b.before b.middle b.after
    b.split b.before_length b.middle_length
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_prefix_sum w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver hne hd) b.before _ he
    receiver b.before_length
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_prefix_sum w r b.before _ b.split receiver b.before_length
  exact hs.symm.trans ht

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
