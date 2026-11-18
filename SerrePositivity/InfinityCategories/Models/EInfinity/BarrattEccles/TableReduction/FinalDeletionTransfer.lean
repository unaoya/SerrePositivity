module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TransferPrefixLift
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalDeletionCases
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TerminalTransferBlock

/-!
模型。文献の定義との比較は後で
# 成功 Schedule の最終出現削除の相殺相手の抽出

概要：Berger–Fresse §1.4.4 の最終出現削除から行長を移した相手の成功と削除後出力一致を構成する。
方針：元の出力座標から全てのブロック条件を導き、通常と最終末尾に分けて先行行を連結する。
規約：退化出力も含み、相手の抽出成功を追加仮定しない。
使われ方：残余和の実際の削除項の相殺対を作る。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：二行の実際の証明書から変更後 Schedule の成功出力を構成（BF §1.4.4）。
方針：削除値・中間行の不出現・受け取り行の余裕を導き、二種類のブロック比較を使う。
規約：削除位置の所属範囲と直前出現の行末位置を指定する。
使われ方：最終出現削除の全位置で、相手の Schedule の抽出を完成する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock.final_transfer {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {receiver : Fin d} {donor : Fin (d + 1)} {out : List (Fin n)}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver.castSucc donor out)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) (ho : receiver.castSucc < donor)
    (hd : 1 < (r.val donor).val) (k : Fin out.length)
    (hl : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor ≤ k.val)
    (hh : k.val < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor + (r.val donor).val)
    (hf : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin out.length => out[j.val]) k)
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).Nonempty)
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r receiver =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp).val) :
    ∃ new, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver.castSucc
        (ne_of_gt ho) hd)) [] = some new ∧
      out.eraseIdx k.val =
        new.eraseIdx (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver.castSucc + (r.val receiver.castSucc).val) := by
  let p := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp
  have hm := Finset.max'_mem (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k) hp
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  have hpend : p.val + 1 =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver.castSucc + (r.val receiver.castSucc).val := by
    have hx := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd_add_one r receiver
    rw [he] at hx
    exact hx
  have ha := b.receiver_selected_end p k hpend hm.2
  have hno := b.previousOccurrence_not_mem_middle k hp hpend hl
  have hcapacity := b.receiver_capacity out[k.val] hd ha
  let c := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc))[(r.val receiver.castSucc).val]
  have hc : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc)).take
      ((r.val receiver.castSucc).val + 1) =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc)).take (r.val receiver.castSucc).val ++
          [c] := List.take_succ_eq_append_getElem hcapacity
  obtain ⟨pre, post, hsplit, hprelen, hpre, hpost⟩ := b.donor_split k hl hh
  let s := (r.val donor).val - pre.length - 1
  have hlength : (r.val donor).val = pre.length + (s + 1) := by dsimp only [s]; omega
  have hsbound : s ≤ post.length := by
    have hb := b.donor_bound
    rw [hsplit, List.length_append, List.length_cons] at hb
    omega
  have hkpos : k.val = b.selectedBefore.flatten.length +
      ((r.val receiver.castSucc).val + b.picked.flatten.length + pre.length) := by
    have hstart := b.donor_start
    omega
  by_cases hs : 0 < s
  · have ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows b.after
        (b.finish ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take (pre.length + (s + 1) - 1)) =
          some b.tail := by rw [← hlength]; exact b.tail_success
    obtain ⟨old, changed, hold, hnew, hdel⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transfer_block_deleted_outputs b.removed
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc) (r.val receiver.castSucc).val out[k.val] c
      (r.property.1 _) hcapacity ha hc b.middle b.picked b.finish b.middle_trace hno
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor) pre post s hs hsbound hsplit hpre hpost b.after b.tail ht
    have hold' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc, (r.val receiver.castSucc).val) ::
        (b.middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val) :: b.after)) b.removed = some old := by
      rw [hlength]; exact hold
    have hshort : (r.val donor).val - 1 = pre.length + s := by omega
    have hnew' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc, (r.val receiver.castSucc).val + 1) ::
        (b.middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val - 1) :: b.after)) b.removed =
          some changed := by rw [hshort]; exact hnew
    obtain ⟨new, hsuccess, hwords⟩ := b.lift_transfer h (ne_of_gt ho) hd old changed
      ((r.val receiver.castSucc).val + b.picked.flatten.length + pre.length) hold' hnew' hdel
    exact ⟨new, hsuccess, by simpa only [← hkpos] using hwords⟩
  · have hs0 : s = 0 := by omega
    have hlength' : (r.val donor).val = pre.length + 1 := by omega
    have hp0 : 0 < pre.length := by omega
    have hlast : donor.val = d := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.final_deletion_row_end_last w r out h donor k hf (by omega)
    have hrowslen := congrArg List.length b.split
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn, List.length_append, List.length_cons] at hrowslen
    have hmidlen := b.middle_length
    have hafter : b.after = [] := List.length_eq_zero_iff.mp (by omega)
    obtain ⟨old, changed, hold, hnew, hdel⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.terminal_transfer_block_deleted_outputs b.removed
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc) (r.val receiver.castSucc).val out[k.val] c
      (r.property.1 _) hcapacity ha hc b.middle b.picked b.finish b.middle_trace hno
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor) pre post hp0 hsplit hpre hpost
    have hold' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc, (r.val receiver.castSucc).val) ::
        (b.middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val) :: b.after)) b.removed = some old := by
      rw [hlength', hafter]; exact hold
    have hshort : (r.val donor).val - 1 = pre.length := by omega
    have hnew' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver.castSucc, (r.val receiver.castSucc).val + 1) ::
        (b.middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val - 1) :: b.after)) b.removed =
          some changed := by rw [hshort, hafter]; exact hnew
    obtain ⟨new, hsuccess, hwords⟩ := b.lift_transfer h (ne_of_gt ho) hd old changed
      ((r.val receiver.castSucc).val + b.picked.flatten.length + pre.length) hold' hnew' hdel
    exact ⟨new, hsuccess, by simpa only [← hkpos] using hwords⟩

/-- 概要：全ての残余の最終出現削除で相手の Schedule の成功と削除後出力一致（BF §1.4.4）。
方針：削除行と受け取り行を特定し、実際の抽出証明書を構成して局所比較を適用する。
規約：相手の抽出成功や出力一致は仮定しない。
使われ方：元の削除項と相殺相手の行末削除項を実際に対応させる。 -/
lemma final_deletion_transfer {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (k : Fin out.length) (hx : k ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singletonPositions r out (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h))
    (hf : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin out.length => out[j.val]) k)
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).Nonempty) :
    ∃ (donor : Fin (d + 1)) (receiver : Fin d) (ho : receiver.castSucc < donor)
      (hd : 1 < (r.val donor).val) (new : List (Fin n)),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor ≤ k.val ∧
      k.val < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor + (r.val donor).val ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleEnd r receiver =
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp).val ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin out.length => out[j.val]) k = -((-1 : ℤ) ^ receiver.val) ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r donor receiver.castSucc (ne_of_gt ho) hd))
        [] = some new ∧
      out.eraseIdx k.val =
        new.eraseIdx (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver.castSucc + (r.val receiver.castSucc).val) := by
  obtain ⟨donor, receiver, ho, hd, hl, hh, _, he, hcoeff⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.final_deletion_location w r out h k hx hf hp
  obtain ⟨b⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleBlock_nonempty w r receiver.castSucc donor ho out h
  obtain ⟨new, hnew, hwords⟩ := b.final_transfer h ho hd k hl hh hf hp he
  exact ⟨donor, receiver, ho, hd, new, hl, hh, he, hcoeff, hnew, hwords⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
