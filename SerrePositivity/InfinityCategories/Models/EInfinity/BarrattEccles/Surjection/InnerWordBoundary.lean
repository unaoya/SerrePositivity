module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapseSeparated
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeInnerProjection
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.VerticalInnerStep

/-!
模型。文献の定義との比較は後で
# 内側に残る異なる境界文字での復元語の接続

概要：Berger–Fresse §1.5.8 の垂直移動で水平区間ごとの復元内側語を連結する。
方針：残る末尾と先頭を filterMap と縮約が保存し、部分単射性が境界の非一致を保つ。
規約：射影で捨てる文字を各区間の内部に許す。
使われ方：水平区間から元の内側表全体を構成するときの出力一致。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：内側に残る異なる両端の境界では内側復元は連結と交換する（BF §1.5.8）。
方針：両端の保持を射影語に移し、縮約の分離された連結規則を使う。
規約：元の二語の内部の非退化性は要求しない。
使われ方：垂直移動で区切った二つの水平区間の復元語を接続する。 -/
lemma innerWord_append_of_retained {m n : ℕ} (k : Fin (m + 1))
    (pre post : List (Fin (m + n))) (a b : Fin (m + n)) (a' b' : Fin n)
    (ha : pre.getLast? = some a) (hb : post.head? = some b)
    (hfa : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k a = some a') (hfb : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k b = some b') (hne : a ≠ b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k (pre ++ post) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k pre ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k post := by
  have hl : (pre.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)).getLast? = some a' := by
    obtain ⟨left, rfl⟩ := List.getLast?_eq_some_iff.mp ha
    simp only [List.filterMap_append, List.filterMap_cons, hfa, List.filterMap_nil,
      List.getLast?_append, List.getLast?_singleton, Option.some_or]
  have hr : (post.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)).head? = some b' := by
    obtain ⟨right, rfl⟩ := List.head?_eq_some_iff.mp hb
    simp only [List.filterMap_cons, hfb, List.head?_cons]
  have hab : a' ≠ b' := by
    intro he
    rw [he] at hfa
    exact hne (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_partial_injective k a b b' hfa hfb)
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord
  rw [List.filterMap_append]
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_append_of_separated
  intro c hc d hd
  simp only [hl, Option.mem_some_iff] at hc
  simp only [hr, Option.mem_some_iff] at hd
  simpa only [hc, hd] using hab

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
