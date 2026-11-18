module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.PrefixUniqueness
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalDeletionTransfer

/-!
模型。文献の定義との比較は後で
# 順方向の中間抽出から構成する逆探索

概要：Berger–Fresse §1.4.4 の順方向の行長移動で元の削除行を逆探索が発見する。
方針：中間語の不出現を skip へ移し、元の削除位置で hit または最終 terminal とする。
規約：最終末尾の削除も含み、探索の停止を追加仮定しない。
使われ方：順から逆の往復で延長行の一意性を検証する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：順方向の相手の逆探索は元の削除行で停止（BF §1.4.4）。
方針：削除位置の前後分割で停止条件を計算し、元の中間抽出を前置する。
規約：探索開始状態は元の受け取り行直後の除外状態。
使われ方：逆探索の一意性と比較するための実際の探索証明書を与える。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock.forward_release_search {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {receiver : Fin d} {donor : Fin (d + 1)} {out : List (Fin n)}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver.castSucc donor out)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) (hd : 1 < (r.val donor).val)
    (k : Fin out.length) (hl : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor ≤ k.val)
    (hh : k.val < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor + (r.val donor).val)
    (hf : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin out.length => out[j.val]) k)
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).Nonempty)
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r receiver =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp).val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch out[k.val]
      (b.middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val - 1) :: b.after)
      (b.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc)).take
        ((r.val receiver.castSucc).val - 1)) b.middle b.picked b.finish
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val - 1) b.after := by
  have hpend : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp).val +
      1 = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver.castSucc + (r.val receiver.castSucc).val := by
    rw [← he]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_add_one r receiver
  have hno := b.previousOccurrence_not_mem_middle k hp hpend hl
  obtain ⟨pre, post, hsplit, hprelen, hpre, _⟩ := b.donor_split k hl hh
  have hprelt : pre.length < (r.val donor).val := by omega
  have hstop : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch out[k.val]
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val - 1) :: b.after) b.finish [] [] b.finish
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val - 1) b.after := by
    by_cases hi : pre.length < (r.val donor).val - 1
    · apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch.hit
      have hj : pre.length < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).length := by
        rw [hsplit, List.length_append, List.length_cons]
        omega
      have hv : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor))[pre.length] = out[k.val] := by
        rw [List.getElem_of_eq hsplit hj]
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem_cons_zero]
      exact List.mem_take_iff_getElem.mpr ⟨pre.length, by omega, hv⟩
    · have hlastlen : (r.val donor).val = pre.length + 1 := by omega
      have hlast : donor.val = d := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.final_deletion_row_end_last w r out h donor k hf (by omega)
      have hrowslen := congrArg List.length b.split
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn, List.length_append, List.length_cons] at hrowslen
      have hmidlen := b.middle_length
      have hafter : b.after = [] := List.length_eq_zero_iff.mp (by omega)
      rw [hafter]
      apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch.terminal
      · simpa only [hlastlen, Nat.add_sub_cancel, hsplit, List.take_append_length] using hpre
      · rw [hlastlen, Nat.add_sub_cancel, hsplit, List.take_length_add_append,
          List.take_succ_cons, List.take_zero]
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true]
  have ht := b.middle_trace.prepend_releaseSearch out[k.val] hno hstop
  simpa only [List.append_nil] using ht

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
