module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ForwardReleasedValue
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseReleasedValue
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowInterior

/-!
模型。文献の定義との比較は後で
# 順から逆の往復の先行状態

概要：Berger–Fresse §1.4.4 の順方向の受け取り行と逆構成の短縮行を照合する。
方針：同じ行末位置から行番号を同定し、行分割と先行抽出の一意性を使う。
規約：逆構成の選択方法に依存しない。
使われ方：二つの逆探索を同じ行列・初期除外状態から比較する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：順から逆の往復で短縮行・先行抽出・後続行が元と一致（BF §1.4.4）。
方針：行末の単射性と先行行数で分割を揃え、抽出証跡の一意性を適用する。
規約：後続では元の削除行だけが一文字短くなっている。
使われ方：順方向から構成した逆探索と実際の逆構成の探索を比較する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock.reverse_context {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {receiver : Fin d} {donor : Fin (d + 1)} {out : List (Fin n)}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver.castSucc donor out) (ho : receiver.castSucc < donor)
    (hd : 1 < (r.val donor).val) (new : List (Fin n)) (q : Fin new.length)
    (hq : q.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver.castSucc + (r.val receiver.castSucc).val)
    (rb : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReverseTransferData w
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver.castSucc (ne_of_gt ho) hd) new q) :
    rb.early = receiver ∧ rb.context.before = b.before ∧
      rb.context.picked = b.selectedBefore ∧ rb.context.removed = b.removed ∧
      rb.context.after = b.middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val - 1) :: b.after := by
  let r' := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver.castSucc (ne_of_gt ho) hd
  have hend : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r' receiver = q.val :=
    (b.end_transfer_receiver (ne_of_gt ho) hd).trans hq.symm
  have hearly : rb.early = receiver :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_injective r' (rb.row_end.trans hend.symm)
  have hrows : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r' = b.before ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc, (r.val receiver.castSucc).val + 1) ::
        (b.middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val - 1) :: b.after) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_transfer_blocks w r donor receiver.castSucc
      (ne_of_gt ho) hd b.before b.middle b.after b.split b.before_length b.middle_length
  have hrow : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w rb.early.castSucc, (r'.val rb.early.castSucc).val) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc, (r'.val receiver.castSucc).val) :=
    congrArg (fun i : Fin d => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i.castSucc, (r'.val i.castSucc).val)) hearly
  have hsplit : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r' = rb.context.before ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc, (r'.val receiver.castSucc).val) :: rb.context.after :=
    rb.context.split.trans (congrArg (fun p => rb.context.before ++ p :: rb.context.after) hrow)
  have hlength : rb.context.before.length = b.before.length := by
    have hlen := rb.context.before_length
    exact hlen.trans ((congrArg Fin.val hearly).trans b.before_length.symm)
  have hval : (r'.val receiver.castSucc).val = (r.val receiver.castSucc).val + 1 :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer_receiver _ _ _ _ _
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r' = _ at hsplit
  rw [hval] at hsplit
  obtain ⟨hbefore, hafter⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.split_unique_of_length rb.context.before _ b.before _
    (hsplit.symm.trans hrows) hlength
  have htrace := rb.context.trace
  rw [hbefore] at htrace
  obtain ⟨hpicked, hremoved⟩ := htrace.unique b.before_trace
  refine ⟨hearly, hbefore, hpicked, hremoved, ?_⟩
  exact (List.cons.inj hafter).2

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
