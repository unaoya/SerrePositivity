module

public import SerrePositivity.EInfinity.TableReduction.PrefixUniqueness
public import SerrePositivity.EInfinity.TableReduction.FinalDeletionTransfer

/-!
# 順方向の中間抽出から構成する逆探索

概要：Berger–Fresse §1.4.4 の順方向の行長移動で元の削除行を逆探索が発見する。
方針：中間語の不出現を skip へ移し、元の削除位置で hit または最終 terminal とする。
規約：最終末尾の削除も含み、探索の停止を追加仮定しない。
使われ方：順から逆の往復で延長行の一意性を検証する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection

/-- 概要：順方向の相手の逆探索は元の削除行で停止（BF §1.4.4）。
方針：削除位置の前後分割で停止条件を計算し、元の中間抽出を前置する。
規約：探索開始状態は元の受け取り行直後の除外状態。
使われ方：逆探索の一意性と比較するための実際の探索証明書を与える。 -/
lemma ScheduleBlock.forward_release_search {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : Schedule n d}
    {receiver : Fin d} {donor : Fin (d + 1)} {out : List (Fin n)}
    (b : ScheduleBlock w r receiver.castSucc donor out)
    (h : reduceRows (rows w r) [] = some out) (hd : 1 < (r.val donor).val)
    (k : Fin out.length) (hl : scheduleOffset r donor ≤ k.val)
    (hh : k.val < scheduleOffset r donor + (r.val donor).val)
    (hf : ¬ Caesura (fun j : Fin out.length => out[j.val]) k)
    (hp : (previousOccurrences (fun j : Fin out.length => out[j.val]) k).Nonempty)
    (he : scheduleEnd r receiver =
      ((previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp).val) :
    ReleaseSearch out[k.val]
      (b.middle ++ (vertexRow w donor, (r.val donor).val - 1) :: b.after)
      (b.removed ++ (available b.removed (vertexRow w receiver.castSucc)).take
        ((r.val receiver.castSucc).val - 1)) b.middle b.picked b.finish
      (vertexRow w donor, (r.val donor).val - 1) b.after := by
  have hpend : ((previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp).val +
      1 = scheduleOffset r receiver.castSucc + (r.val receiver.castSucc).val := by
    rw [← he]
    exact scheduleEnd_add_one r receiver
  have hno := b.previousOccurrence_not_mem_middle k hp hpend hl
  obtain ⟨pre, post, hsplit, hprelen, hpre, _⟩ := b.donor_split k hl hh
  have hprelt : pre.length < (r.val donor).val := by omega
  have hstop : ReleaseSearch out[k.val]
      ((vertexRow w donor, (r.val donor).val - 1) :: b.after) b.finish [] [] b.finish
      (vertexRow w donor, (r.val donor).val - 1) b.after := by
    by_cases hi : pre.length < (r.val donor).val - 1
    · apply ReleaseSearch.hit
      have hj : pre.length < (available b.finish (vertexRow w donor)).length := by
        rw [hsplit, List.length_append, List.length_cons]
        omega
      have hv : (available b.finish (vertexRow w donor))[pre.length] = out[k.val] := by
        rw [List.getElem_of_eq hsplit hj]
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem_cons_zero]
      exact List.mem_take_iff_getElem.mpr ⟨pre.length, by omega, hv⟩
    · have hlastlen : (r.val donor).val = pre.length + 1 := by omega
      have hlast : donor.val = d := final_deletion_row_end_last w r out h donor k hf (by omega)
      have hrowslen := congrArg List.length b.split
      simp only [rows, List.length_ofFn, List.length_append, List.length_cons] at hrowslen
      have hmidlen := b.middle_length
      have hafter : b.after = [] := List.length_eq_zero_iff.mp (by omega)
      rw [hafter]
      apply ReleaseSearch.terminal
      · simpa only [hlastlen, Nat.add_sub_cancel, hsplit, List.take_append_length] using hpre
      · rw [hlastlen, Nat.add_sub_cancel, hsplit, List.take_length_add_append,
          List.take_succ_cons, List.take_zero]
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true]
  have ht := b.middle_trace.prepend_releaseSearch out[k.val] hno hstop
  simpa only [List.append_nil] using ht

end SerrePositivity.EInfinity.TableReduction
