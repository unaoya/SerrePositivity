module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.NullaryErasure

/-!
模型。文献の定義との比較は後で
# 指定値を一回戻す空語合成の非退化性

概要：Berger–Fresse §1.5.7–9 の nullary 逆構成で、削除後の非退化性を元の語へ戻す。
方針：指定値以外では削除が文字を保ち、戻した一文字は両隣と異なる。
規約：前後には指定値が現れず、空の前半・後半も含む。
使われ方：解放値探索で得た元の成功語を実際の BasisWord に包装する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定値を含まない語では削除後の非退化性から元の非退化性が従う（BF §1.5.7）。
方針：元の隣接二文字を保持する削除写像の some 値を比較する。
規約：空語も含む。
使われ方：空語逆構成の前後の語の隣接非一致を得る。 -/
lemma isChain_of_eraseSlotWord {m : ℕ} (k : Fin (m + 1)) (xs : List (Fin (m + 1)))
    (hk : k ∉ xs) (hc : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k xs).IsChain (· ≠ ·)) : xs.IsChain (· ≠ ·) := by
  induction xs with
  | nil => exact .nil
  | cons a xs ih =>
    cases xs with
    | nil => exact .singleton _
    | cons b ys =>
      have ha : a ≠ k := by intro he; exact hk (by simp [he])
      have hb : b ≠ k := by intro he; exact hk (by simp [he])
      have hc' : (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m 0 k ⟨a, ha⟩ ::
          _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m 0 k ⟨b, hb⟩ :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k ys).IsChain
            (· ≠ ·) := by
        simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord, List.filterMap_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel, dite_eq_right ha,
          dite_eq_right hb] using hc
      apply List.isChain_cons_cons.mpr
      refine ⟨?_, ih (by intro hm; exact hk (List.mem_cons_of_mem a hm)) ?_⟩
      · intro he
        subst b
        exact (List.isChain_cons_cons.mp hc').1 rfl
      · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord, List.filterMap_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel, dite_eq_right hb,
          List.tail_cons] using hc'.tail

/-- 概要：指定値を一回戻す操作は削除後の語を変えない（BF §1.2.4）。
方針：filterMap の連結と指定値での none を評価する。
規約：前後に指定値があっても等式自体は成立する。
使われ方：元の成功基底語の空語合成を目標語へ同定する。 -/
lemma eraseSlotWord_insert {m : ℕ} (k : Fin (m + 1)) (pre post : List (Fin (m + 1))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k (pre ++ k :: post) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k (pre ++ post) := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel, List.filterMap_append]

/-- 概要：削除後が非退化なら、指定値を一度戻した語も非退化（BF §1.5.7–9）。
方針：前後の語の非退化性と指定値の不出現により二つの接続を検証する。
規約：前後は空でもよく、全射性は要求しない。
使われ方：nullary 逆構成の成功語を元の次数の BasisWord にする。 -/
lemma isChain_insert_of_eraseSlotWord {m : ℕ} (k : Fin (m + 1))
    (pre post : List (Fin (m + 1))) (hp : k ∉ pre) (hq : k ∉ post)
    (hc : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k (pre ++ post)).IsChain (· ≠ ·)) :
    (pre ++ k :: post).IsChain (· ≠ ·) := by
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.isChain_of_eraseSlotWord k (pre ++ post) (by simp [hp, hq]) hc
  have hpost : (k :: post).IsChain (· ≠ ·) := ht.right_of_append.cons (by
    intro a ha he
    exact hq (he ▸ List.mem_of_mem_head? ha))
  apply ht.left_of_append.append hpost
  intro a ha b hb he
  have hb' : b = k := by simpa using hb.symm
  apply hp
  rw [← hb', ← he]
  exact List.mem_of_mem_getLast? ha

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
