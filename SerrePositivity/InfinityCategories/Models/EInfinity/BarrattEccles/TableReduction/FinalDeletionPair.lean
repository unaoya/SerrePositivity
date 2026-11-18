module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalDeletionTransfer
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ResidualRowEnds

/-!
模型。文献の定義との比較は後で
# 最終出現削除と相手の行末削除の逆符号

概要：Berger–Fresse §1.4.4 の実際の相手の成功抽出から逆符号の正規化削除項を構成する。
方針：新しい行末の位置を計算し、削除後出力の一致と行末の交代係数を使う。
規約：係数環は任意の可換環、削除後の次数は d−1、退化出力も含む。
使われ方：残余和の二種類の削除項を相殺させる。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：行長を移した相手の行末位置は元の開始位置＋元の行長（BF §1.4.4）。
方針：先行部分の不変性と受け取り行長の増分を行末の公式へ代入する。
規約：受け取り行は非最終行。
使われ方：構成した相手で削除する位置を実際の区切りと同定する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock.end_transfer_receiver {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {receiver : Fin d} {donor : Fin (d + 1)} {out : List (Fin n)}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver.castSucc donor out) (hne : donor ≠ receiver.castSucc)
    (hd : 1 < (r.val donor).val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver.castSucc hne hd) receiver =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver.castSucc + (r.val receiver.castSucc).val := by
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_add_one (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver.castSucc hne hd)
    receiver
  rw [b.offset_transfer_receiver hne hd, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer_receiver] at he
  omega

/-- 概要：全ての残余の最終出現削除には逆符号で同じ削除後出力の項がある（BF §1.4.4）。
方針：一般の成功相手を構成し、新しい行末の係数と元の最終出現の係数を足す。
規約：相手の成功・出力一致・逆符号を追加仮定しない。
使われ方：全残余項の相殺に必要な順方向の実際の対を与える。 -/
lemma final_deletion_pair (A : Type u) [CommRing A] {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (k : Fin out.length) (hx : k ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions r out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h))
    (hf : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin out.length => out[j.val]) k)
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).Nonempty) :
    ∃ (donor : Fin (d + 1)) (receiver : Fin d) (ho : receiver.castSucc < donor)
      (hd : 1 < (r.val donor).val) (new : List (Fin n)) (q : Fin new.length),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver.castSucc (ne_of_gt ho) hd))
        [] = some new ∧
      q.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver.castSucc + (r.val receiver.castSucc).val ∧
      out.eraseIdx k.val = new.eraseIdx q.val ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin out.length => out[j.val]) k +
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin new.length => new[j.val]) q = 0 ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm A (d := d - 1) out k + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm A (d := d - 1) new q = 0 ∧
      ∃ hl : new.length = n + d,
        q ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver.castSucc (ne_of_gt ho) hd) new hl ∧
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin new.length => new[j.val]) q := by
  obtain ⟨donor, receiver, ho, hd, new, _, _, _, hcoeff, hnew, hwords⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.final_deletion_transfer w r out h k hx hf hp
  let r' := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver.castSucc (ne_of_gt ho) hd
  obtain ⟨b⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleBlock_nonempty w r receiver.castSucc donor ho out h
  have hpos := b.end_transfer_receiver (ne_of_gt ho) hd
  have hlt : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r' receiver < n + d :=
    lt_of_le_of_lt (Nat.sub_le _ _) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset_lt r' receiver.succ)
  have hlen := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r' new hnew
  let q : Fin new.length := ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r' receiver, by omega⟩
  have hq : q.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver.castSucc + (r.val receiver.castSucc).val := hpos
  have hdeleted : out.eraseIdx k.val = new.eraseIdx q.val := by simpa only [hq] using hwords
  have hqcoeff : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin new.length => new[j.val]) q =
      (-1 : ℤ) ^ receiver.val :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionCoefficient_schedule_rowEnd w r' new hnew receiver q
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_eq_prefix r' receiver).symm
  have hlong : 1 < (r'.val receiver.castSucc).val := by
    change 1 < ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver.castSucc (ne_of_gt ho) hd).val
      receiver.castSucc).val
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer_receiver]
    have := r.property.1 receiver.castSucc
    omega
  have hremaining := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_not_singleton r' receiver hlong new hlen q rfl
  have hcaesura := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.caesura_of_scheduleEnd w r' new hnew receiver q rfl
  refine ⟨donor, receiver, ho, hd, new, q, hnew, hq, hdeleted, ?_, ?_,
    hlen, hremaining, hcaesura⟩
  · rw [hcoeff, hqcoeff, neg_add_cancel]
  · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm, hcoeff, hqcoeff, hdeleted, neg_zsmul, neg_add_cancel]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
