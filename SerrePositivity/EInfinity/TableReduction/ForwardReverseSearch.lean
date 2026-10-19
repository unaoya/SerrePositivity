module

public import SerrePositivity.EInfinity.TableReduction.ForwardReverseContext
public import SerrePositivity.EInfinity.TableReduction.ForwardReleaseSearch

/-!
# 順から逆の往復の解放値と探索停止行

概要：Berger–Fresse §1.4.4 の実際の逆構成が元の削除行を延長することを示す。
方針：直前値から解放値を揃え、先行状態の一致と探索の一意性を使う。
規約：逆構成の成功や停止行を追加仮定しない。
使われ方：順から逆の Schedule の復元と残余削除の全単射へ接続する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection

/-- 概要：順から逆の往復で解放値・初期状態・延長行は元のもの（BF §1.4.4）。
方針：相手の行末直前値を読み、同じ初期状態の二つの探索の一意性を適用する。
規約：内部削除と最終末尾を同時に扱う。
使われ方：逆に移す二行が元の二行であることを保証する。 -/
lemma ScheduleBlock.reverse_search {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : Schedule n d}
    {receiver : Fin d} {donor : Fin (d + 1)} {out : List (Fin n)}
    (b : ScheduleBlock w r receiver.castSucc donor out)
    (h : reduceRows (rows w r) [] = some out) (ho : receiver.castSucc < donor)
    (hd : 1 < (r.val donor).val) (k : Fin out.length)
    (hl : scheduleOffset r donor ≤ k.val)
    (hh : k.val < scheduleOffset r donor + (r.val donor).val)
    (hf : ¬ Caesura (fun j : Fin out.length => out[j.val]) k)
    (hp : (previousOccurrences (fun j : Fin out.length => out[j.val]) k).Nonempty)
    (he : scheduleEnd r receiver =
      ((previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp).val)
    (new : List (Fin n))
    (hnew : reduceRows (rows w (deletionScheduleTransfer r donor receiver.castSucc
      (ne_of_gt ho) hd)) [] = some new) (q : Fin new.length)
    (hq : q.val = scheduleOffset r receiver.castSucc + (r.val receiver.castSucc).val)
    (rb : ReverseTransferData w
      (deletionScheduleTransfer r donor receiver.castSucc (ne_of_gt ho) hd) new q) :
    rb.a = out[k.val] ∧ rb.early = receiver ∧ rb.late = donor := by
  obtain ⟨hearly, hbefore, _, hremoved, hafter⟩ := b.reverse_context ho hd new q hq rb
  have hpos : 0 < q.val := by have := r.property.1 receiver.castSucc; omega
  let p : Fin new.length := ⟨q.val - 1, by have := q.isLt; omega⟩
  have hpq : p.val + 1 = q.val := by dsimp only [p]; omega
  have hm := Finset.max'_mem (previousOccurrences (fun j : Fin out.length => out[j.val]) k) hp
  simp only [previousOccurrences, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  have hpend : ((previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp).val +
      1 = scheduleOffset r receiver.castSucc + (r.val receiver.castSucc).val := by
    rw [← he]
    exact scheduleEnd_add_one r receiver
  have haold := b.receiver_selected_end _ k hpend hm.2
  have hvold := b.forward_released_value ho hd out[k.val] haold new hnew p (hpq.trans hq)
  have ha : rb.a = out[k.val] := (rb.released_value p hpq).symm.trans hvold
  have hfree : rb.free = b.removed ++
      (available b.removed (vertexRow w receiver.castSucc)).take
        ((r.val receiver.castSucc).val - 1) := by
    calc
      rb.free = _ := rb.free_state
      _ = _ := by
        rw [hremoved, hearly]
        simp only [deletionScheduleTransfer_receiver, Nat.add_sub_cancel]
  have hs := rb.search
  rw [ha, hafter, hfree] at hs
  have hsold := b.forward_release_search h hd k hl hh hf hp he
  obtain ⟨hearlier, _, _, _, _⟩ := hs.unique hsold
  refine ⟨ha, hearly, Fin.ext ?_⟩
  have hlate := rb.late_index
  rw [hbefore, hearlier] at hlate
  exact hlate.trans b.middle_length

end SerrePositivity.EInfinity.TableReduction
