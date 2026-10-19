module

public import SerrePositivity.EInfinity.TableReduction.IntermediatePrefix
public import SerrePositivity.EInfinity.TableReduction.ReceiverStep

/-!
# 受け取り行・中間行・削除行を通した行長移動

概要：Berger–Fresse §1.4.4 の二行の行長変更で削除後出力が一致することを構成する。
方針：受け取り行を一文字延ばし、削除値の早い除外を中間行へ通し、短い削除行で合流する。
規約：元の中間行には削除値が現れず、削除行では末尾以外を削除する。
使われ方：実際の Schedule の相殺対へ局所抽出をまとめて適用する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：前の行末の後に一文字を増やし、後の行内部から一文字を減らした抽出（BF §1.4.4）。
方針：既存の三つの局所抽出公式を同じ中間状態で連結する。
規約：行長は自然数であり、Schedule の上界や添字の付け替えは別に渡す。
使われ方：相殺対の二つの語を元の reduceRows で実現する。 -/
lemma transfer_block_extraction (removed receiver : List α) (r : ℕ) (a b : α)
    (hr : 0 < r) (hb : r < (available removed receiver).length)
    (ha : (available removed receiver).take r =
      (available removed receiver).take (r - 1) ++ [a])
    (he : (available removed receiver).take (r + 1) =
      (available removed receiver).take r ++ [b])
    (middle : List (List α × ℕ)) (picked : List (List α)) (finish : List α)
    (hm : ExtractionPrefix middle (removed ++ (available removed receiver).take (r - 1))
      picked finish) (hno : a ∉ picked.flatten)
    (donor pre post : List α) (s : ℕ) (hs : 0 < s) (hbound : s ≤ post.length)
    (hd : available finish donor = pre ++ a :: post) (hpre : a ∉ pre) (hpost : a ∉ post)
    (rest : List (List α × ℕ)) (tail : List α)
    (ht : reduceRows rest
      (finish ++ (available finish donor).take (pre.length + (s + 1) - 1)) = some tail) :
    reduceRows ((receiver, r) :: (middle ++ (donor, pre.length + (s + 1)) :: rest)) removed =
        some ((available removed receiver).take r ++
          (picked.flatten ++ ((pre ++ a :: post.take s) ++ tail))) ∧
      reduceRows ((receiver, r + 1) :: (middle ++ (donor, pre.length + s) :: rest)) removed =
        some (((available removed receiver).take r ++ [b]) ++
          (picked.flatten ++ ((pre ++ post.take s) ++ tail))) := by
  have hdlen : pre.length + (s + 1) ≤ (available finish donor).length := by
    rw [hd, List.length_append, List.length_cons]
    omega
  have hdonor := reduceRows_cons_of_success donor (pre.length + (s + 1)) rest finish tail
    (by omega) hdlen ht
  rw [(donor_selected_split finish donor pre post a s hd hpre hpost).2] at hdonor
  have hmiddle := hm.append _ _ hdonor
  have hbefore := reduceRows_cons_of_success receiver r _ removed _ hr (by omega) hmiddle
  have hshort := reduceRows_donor_step finish donor pre post a s hs hbound hd hpre hpost
    rest tail ht
  have hnewmiddle := hm.append_early_exclusion a hno _ _ hshort
  have hafter := reduceRows_receiver_step removed receiver r a b hb ha he _ _ hnewmiddle
  exact ⟨hbefore, hafter⟩

/-- 概要：離れた一文字を互いに挿入・削除した語の削除後出力は一致（BF §1.4.4）。
方針：前後の連結リストで eraseIdx を指定位置に移す。
規約：二文字の値は等しくても異なっていてもよい。
使われ方：行長移動の二つの抽出結果の削除後の語を同定する。 -/
lemma transferred_words_delete_eq {β : Type*} (left middle right : List β) (a b : β) :
    (left ++ (middle ++ a :: right)).eraseIdx (left.length + middle.length) =
      (left ++ b :: (middle ++ right)).eraseIdx left.length := by
  have hleft : (left ++ (middle ++ a :: right)).eraseIdx (left.length + middle.length) =
      left ++ (middle ++ right) := by
    rw [List.eraseIdx_append, ite_eq_right (by omega), Nat.add_sub_cancel_left]
    rw [List.eraseIdx_append, ite_eq_right (by omega), Nat.sub_self]
    rfl
  have hright : (left ++ b :: (middle ++ right)).eraseIdx left.length =
      left ++ (middle ++ right) := by
    rw [List.eraseIdx_append, ite_eq_right (by omega), Nat.sub_self]
    rfl
  exact hleft.trans hright.symm

/-- 概要：行長を移した二つの成功抽出は指定した一文字の削除後に同じ語となる（BF §1.4.4）。
方針：二つの抽出を前・中・後の標準形へ直して削除公式を適用する。
規約：正規化前のリストの等式であり、退化出力も含む。
使われ方：相殺項の生成元の一致を与える。 -/
lemma transfer_block_deleted_outputs (removed receiver : List α) (r : ℕ) (a b : α)
    (hr : 0 < r) (hb : r < (available removed receiver).length)
    (ha : (available removed receiver).take r =
      (available removed receiver).take (r - 1) ++ [a])
    (he : (available removed receiver).take (r + 1) =
      (available removed receiver).take r ++ [b])
    (middle : List (List α × ℕ)) (picked : List (List α)) (finish : List α)
    (hm : ExtractionPrefix middle (removed ++ (available removed receiver).take (r - 1))
      picked finish) (hno : a ∉ picked.flatten)
    (donor pre post : List α) (s : ℕ) (hs : 0 < s) (hbound : s ≤ post.length)
    (hd : available finish donor = pre ++ a :: post) (hpre : a ∉ pre) (hpost : a ∉ post)
    (rest : List (List α × ℕ)) (tail : List α)
    (ht : reduceRows rest
      (finish ++ (available finish donor).take (pre.length + (s + 1) - 1)) = some tail) :
    ∃ old new, reduceRows
        ((receiver, r) :: (middle ++ (donor, pre.length + (s + 1)) :: rest)) removed = some old ∧
      reduceRows ((receiver, r + 1) :: (middle ++ (donor, pre.length + s) :: rest)) removed =
        some new ∧
      old.eraseIdx (r + picked.flatten.length + pre.length) = new.eraseIdx r := by
  obtain ⟨hold, hnew⟩ := transfer_block_extraction removed receiver r a b hr hb ha he
    middle picked finish hm hno donor pre post s hs hbound hd hpre hpost rest tail ht
  let left := (available removed receiver).take r
  let mid := picked.flatten ++ pre
  let right := post.take s ++ tail
  have hleft : left.length = r := by
    simp only [left, List.length_take, Nat.min_eq_left (by omega : r ≤
      (available removed receiver).length)]
  refine ⟨left ++ (mid ++ a :: right), left ++ b :: (mid ++ right), ?_, ?_, ?_⟩
  · simpa only [left, mid, right, List.append_assoc, List.cons_append] using hold
  · simpa only [left, mid, right, List.append_assoc, List.singleton_append] using hnew
  · have hdel := transferred_words_delete_eq left mid right a b
    simpa only [hleft, mid, List.length_append, Nat.add_assoc] using hdel

end SerrePositivity.EInfinity.TableReduction
