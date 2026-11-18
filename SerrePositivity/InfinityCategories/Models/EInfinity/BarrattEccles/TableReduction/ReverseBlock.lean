module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReceiverRelease
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseExtraction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TransferBlock

/-!
模型。文献の定義との比較は後で
# 行末削除から逆に行長を移す抽出

概要：Berger–Fresse §1.4.4 の長い行末の削除から、後の最終出現削除の相手を構成する。
方針：現在行を短くして直前値を解放し、最初に影響を受ける後続行を延長する。
規約：元の後続列の成功・完全行・除外予算だけを用い、変更後の成功を要求しない。
使われ方：行末側からの逆対応を実際の Schedule の添字へ移すための抽出比較。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：行末側から短縮・最初の後続延長で逆の削除対の成功出力を作る（BF §1.4.4）。
方針：解放状態の初期化・一意な探索・後続への一文字挿入を連結する。
規約：後続の長さ予算は元の Schedule から得る。
使われ方：順方向の削除対と同じ語の逆構成を与える。 -/
lemma reverse_block_extraction {n : ℕ} (removed row : List (Fin n)) (r : ℕ)
    (rest : List (List (Fin n) × ℕ)) (out : List (Fin n))
    (hn : removed.Nodup) (hrow : row.Nodup) (hr : 1 < r)
    (hne : rest ≠ []) (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CompleteRows rest)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r) :: rest) removed = some out)
    (hb : removed.length + (r - 1) + (rest.map (fun p => p.2 - 1)).sum + 1 = n) :
    ∃ a b earlier picked finish chosen later left middle right free,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch a rest free earlier picked finish chosen later ∧
      free = removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take ((r - 1) - 1) ∧
      (∃ head, left = head ++ [a]) ∧
      a ≠ b ∧ a ∉ middle ∧ a ∉ right ∧ left.length = r - 1 ∧
      out = left ++ b :: (middle ++ right) ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((row, r - 1) :: (earlier ++ (chosen.1, chosen.2 + 1) :: later)) removed =
        some (left ++ (middle ++ a :: right)) ∧
      out.eraseIdx (r - 1) =
        (left ++ (middle ++ a :: right)).eraseIdx (r - 1 + middle.length) := by
  obtain ⟨_, hbound, tail, ht, hout⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
  obtain ⟨pre, a, b, free, hprelen, hab, hfull, hshort, hfree, hfn, hfa, hstate, _⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.receiver_release removed row r hn hrow hr hbound
  have htail : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest (free ++ [a]) = some tail := by rw [← hstate]; exact ht
  have hfreeLen : free.length = removed.length + (r - 1) - 1 := by
    rw [hfree, List.length_append]
    omega
  have hbudget : free.length + 1 + (rest.map (fun p => p.2 - 1)).sum + 1 = n := by omega
  obtain ⟨earlier, picked, finish, chosen, later, mid, post, hs, _, _, htailOut,
    haMid, haPost, hnewTail⟩ :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.releaseSearch_constructs_extension rest free a tail hne hc hfn hfa htail hbudget
  have hshortPos : 0 < r - 1 := by omega
  have hshortBound : r - 1 ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).length := by omega
  have hnewState : removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take ((r - 1) - 1) = free := by
    have hl : pre.length = (r - 1) - 1 := by omega
    have he := congrArg (fun xs => xs.take pre.length) hshort
    have hpreBound : pre.length ≤ r - 1 := by omega
    simp only [List.take_take, Nat.min_eq_left hpreBound, List.take_append_length] at he
    rw [hfree, ← hl]
    exact congrArg (List.append removed) he
  have hnext : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (earlier ++ (chosen.1, chosen.2 + 1) :: later)
      (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row).take ((r - 1) - 1)) = some (mid ++ a :: post) := by
    rw [hnewState]
    exact hnewTail
  have hnew := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success row (r - 1) _ removed _ hshortPos hshortBound hnext
  let left := pre ++ [a]
  have hleft : left.length = r - 1 := by
    simp only [left, List.length_append, List.length_singleton]
    omega
  have hold : out = left ++ b :: (mid ++ post) := by
    rw [hout, hfull, htailOut]
    simp only [left, List.append_assoc, List.cons_append, List.nil_append]
  refine ⟨a, b, earlier, picked, finish, chosen, later, left, mid, post, free,
    hs, hnewState.symm, ⟨pre, rfl⟩, hab, haMid, haPost, hleft, hold, ?_, ?_⟩
  · simpa only [hshort, left] using hnew
  · have hdel := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferred_words_delete_eq left mid post a b
    calc
      _ = (left ++ b :: (mid ++ post)).eraseIdx (r - 1) :=
        congrArg (fun xs => xs.eraseIdx (r - 1)) hold
      _ = _ := by simpa only [hleft] using hdel.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
