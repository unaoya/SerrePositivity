module

public import SerrePositivity.EInfinity.TableReduction.TransferBlock
public import SerrePositivity.EInfinity.TableReduction.TerminalDonorStep

/-!
# 最終末尾削除と先行行末削除のブロック比較

概要：Berger–Fresse §1.4.4 の最後の一文字の最終出現削除を含む行長移動を構成する。
方針：受け取り行の延長と中間行の輸送を、最後の行の短縮へつなぐ。
規約：元の最終行の選択長は 2 以上。
使われ方：最終末尾の削除対にも成功抽出と削除後出力の一致を与える。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：最終行の末尾を削除する相殺対の抽出と削除後出力の一致（BF §1.4.4）。
方針：末尾削除の局所抽出を、中間行と受け取り行の計算へ連結する。
規約：後続行を空とし、削除行後の状態の合流条件を要求しない。
使われ方：全残余位置の相殺で最終位置の分岐を閉じる。 -/
lemma terminal_transfer_block_deleted_outputs (removed receiver : List α) (r : ℕ) (a b : α)
    (hr : 0 < r) (hb : r < (available removed receiver).length)
    (ha : (available removed receiver).take r =
      (available removed receiver).take (r - 1) ++ [a])
    (he : (available removed receiver).take (r + 1) =
      (available removed receiver).take r ++ [b])
    (middle : List (List α × ℕ)) (picked : List (List α)) (finish : List α)
    (hm : ExtractionPrefix middle (removed ++ (available removed receiver).take (r - 1))
      picked finish) (hno : a ∉ picked.flatten)
    (donor pre post : List α) (hp : 0 < pre.length)
    (hd : available finish donor = pre ++ a :: post) (hpre : a ∉ pre) (hpost : a ∉ post) :
    ∃ old new,
      reduceRows ((receiver, r) :: (middle ++ [(donor, pre.length + 1)])) removed = some old ∧
      reduceRows ((receiver, r + 1) :: (middle ++ [(donor, pre.length)])) removed = some new ∧
      old.eraseIdx (r + picked.flatten.length + pre.length) = new.eraseIdx r := by
  obtain ⟨holdDonor, hnewDonor⟩ :=
    reduceRows_terminal_donor_step finish donor pre post a hp hd hpre hpost
  have holdMid := hm.append _ _ holdDonor
  have hold := reduceRows_cons_of_success receiver r _ removed _ hr (by omega) holdMid
  have hnewMid := hm.append_early_exclusion a hno _ _ hnewDonor
  have hnew := reduceRows_receiver_step removed receiver r a b hb ha he _ _ hnewMid
  let left := (available removed receiver).take r
  let mid := picked.flatten ++ pre
  have hleft : left.length = r := by
    simp only [left, List.length_take, Nat.min_eq_left (by omega : r ≤
      (available removed receiver).length)]
  refine ⟨left ++ (mid ++ [a]), left ++ b :: mid, ?_, ?_, ?_⟩
  · simpa only [left, mid, List.append_assoc] using hold
  · simpa only [left, mid, List.append_assoc, List.singleton_append] using hnew
  · have hdel := transferred_words_delete_eq left mid [] a b
    simpa only [List.append_nil, hleft, mid, List.length_append, Nat.add_assoc] using hdel

end SerrePositivity.EInfinity.TableReduction
