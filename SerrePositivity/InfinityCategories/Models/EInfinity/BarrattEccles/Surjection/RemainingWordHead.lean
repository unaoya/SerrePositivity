module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeOuterRecovery
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapsePrefixes

/-!
模型。文献の定義との比較は後で
# 非退化な合成語の外側文字を保つ先頭復元

概要：Berger–Fresse §1.5.8–9 の逆構成で、外側文字は外側復元語にそのまま一文字残る。
方針：指定値以外の外側射影の原像は一つだけなので、元の非退化性が先頭縮約を排除する。
規約：内側 arity 零も含む。
使われ方：任意の非退化合成語を外側語と非空な挿入部分語へ逆分解する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：指定値以外の外側ラベルの原像は実際の残りラベルだけ（BF §1.5.8）。
方針：挿入直和分解で場合分けし、内側側の指定値との一致を排除する。
規約：元の外側ラベルは指定値と異なる。
使われ方：外側復元で隣接文字が同じになる場合を元の退化へ戻す。 -/
lemma outerLabel_eq_remaining_iff {m n : ℕ} (k : Fin (m + 1))
    (a : {a : Fin (m + 1) // a ≠ k}) (b : Fin (m + n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k b = a.val ↔ b = remainingPosition m n k a := by
  constructor
  · intro hb
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).injective
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k b =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).symm (Sum.inl a))
    rw [Equiv.apply_symm_apply]
    cases he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k b with
    | inl c =>
      have hc : c = a := Subtype.ext (by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel, he] using hb)
      rw [hc]
    | inr c =>
      have hk : k = a.val := by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel, he] using hb
      exact (a.property hk.symm).elim
  · intro hb
    rw [hb, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel_remaining]

/-- 概要：非退化な合成語の外側先頭は縮約されず復元語の先頭に残る（BF §1.5.8）。
方針：次の射影が同じなら原像一意性で元の隣接重複となるため、不一致縮約を使う。
規約：後続が空の場合も含む。
使われ方：任意の合成語の部分語分解で外側先頭を一文字消費する。 -/
lemma outerWord_remaining_cons {m n : ℕ} (k : Fin (m + 1))
    (a : {a : Fin (m + 1) // a ≠ k}) (out : List (Fin (m + n)))
    (hc : (remainingPosition m n k a :: out).IsChain (· ≠ ·)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k (remainingPosition m n k a :: out) = a.val :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out := by
  cases out with
  | nil => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord, List.map_cons, List.map_nil, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel_remaining,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend]
  | cons b out =>
    have hn : a.val ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k b := by
      intro he
      have hb := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel_eq_remaining_iff k a b).mp he.symm
      exact (List.isChain_cons_cons.mp hc).1 hb.symm
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord
    simp only [List.map_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel_remaining]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_cons_cons_ne a.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k b) _ hn

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
