module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.RemainingWordHead
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositePartitionRecovery
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapseSeparated

/-!
模型。文献の定義との比較は後で
# 任意の非退化合成語の非空挿入部分語への分解

概要：Berger–Fresse §1.5.8–9 の逆構成で、任意の非退化出力を実際の部分語代入へ戻す。
方針：末尾から一文字ずつ戻し、内側先頭は同じ挿入区間へ加え、外側先頭は保持する。
規約：外側語は出力だけからの outerWord。分割添字や元の入力語は仮定しない。
使われ方：splitParts の非空性・個数と全代入一致を供給し、実際の分割復元へ進む。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：挿入先頭の外側復元は指定値の縮約付き先頭付加（BF §1.5.8）。
方針：挿入ラベルの外側射影と縮約の定義を評価する。
規約：先頭区間が既にあれば同じ指定値を一コピーだけ残す。
使われ方：非空挿入区間を合成語の先頭へ一文字ずつ拡張する。 -/
lemma outerWord_inserted_cons {m n : ℕ} (k : Fin (m + 1)) (b : Fin n)
    (out : List (Fin (m + n))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k (insertedPosition m n k b :: out) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord, List.map_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel_inserted, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse]

/-- 概要：任意の非退化出力は復元外側語への非空部分語の代入で表せる（BF §1.5.8）。
方針：出力で帰納し、挿入文字は先頭区間へ加え、外側文字は一意な原像で保持する。
規約：部分語数は復元外側語の指定値の出現回数。共有端点はまだ要求しない。
使われ方：元の splitParts で全合成出力を復元する。 -/
lemma exists_nonempty_parts {m n : ℕ} (k : Fin (m + 1))
    (out : List (Fin (m + n))) (hc : out.IsChain (· ≠ ·)) :
    ∃ parts : List (List (Fin n)), parts.length = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out).count k ∧
      (∀ part ∈ parts, part ≠ []) ∧ out = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) parts := by
  induction out with
  | nil => exact ⟨[], rfl, by simp, rfl⟩
  | cons a out ih =>
    obtain ⟨parts, hlen, hn, hsub⟩ := ih hc.tail
    cases he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k a with
    | inl c =>
      have ha : a = remainingPosition m n k c := by
        apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).injective
        simpa only [remainingPosition, Equiv.apply_symm_apply] using he
      subst a
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord_remaining_cons k c out hc]
      refine ⟨parts, ?_, hn, ?_⟩
      · simpa [c.property] using hlen
      · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right c.property] using
          congrArg (remainingPosition m n k c :: ·) hsub
    | inr b =>
      have ha : a = insertedPosition m n k b := by
        apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).injective
        simpa only [insertedPosition, Equiv.apply_symm_apply] using he
      subst a
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord_inserted_cons]
      cases hx : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out with
      | nil =>
        rw [hx] at hlen hsub
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend]
        refine ⟨[b] :: parts, ?_, ?_, ?_⟩
        · simp only [List.length_cons, List.count_nil, List.count_cons_self] at hlen ⊢
          omega
        · intro word hw
          rcases List.mem_cons.mp hw with rfl | hw
          · exact List.cons_ne_nil _ _
          · exact hn word hw
        · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.headD_cons, List.tail_cons,
            List.map_cons, List.map_nil, List.singleton_append] using
              congrArg (insertedPosition m n k b :: ·) hsub
      | cons c xs =>
        rw [hx] at hlen hsub
        by_cases hck : c = k
        · subst c
          simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend, ite_true]
          cases parts with
          | nil => simp only [List.length_nil, List.count_cons_self] at hlen; omega
          | cons part parts =>
            refine ⟨(b :: part) :: parts, hlen, ?_, ?_⟩
            · intro word hw
              rcases List.mem_cons.mp hw with rfl | hw
              · exact List.cons_ne_nil _ _
              · exact hn word (List.mem_cons_of_mem part hw)
            · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.headD_cons, List.tail_cons,
                List.map_cons, List.cons_append] using
                  congrArg (insertedPosition m n k b :: ·) hsub
        · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend, ite_eq_right (Ne.symm hck)]
          refine ⟨[b] :: parts, ?_, ?_, ?_⟩
          · simpa only [List.length_cons, List.count_cons_self] using congrArg (· + 1) hlen
          · intro word hw
            rcases List.mem_cons.mp hw with rfl | hw
            · exact List.cons_ne_nil _ _
            · exact hn word hw
          · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.headD_cons, List.tail_cons,
              List.map_cons, List.map_nil, List.singleton_append] using
                congrArg (insertedPosition m n k b :: ·) hsub

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
