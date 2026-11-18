module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

/-!
模型。文献の定義との比較は後で
# 共有末尾を一つにした非退化語の連結

概要：Berger–Fresse §1.5.8 の同じ外側行の融合で非退化性を保つ語の接合を扱う。
方針：共有末尾を singleton の重なりとして両語を接続する。
規約：共有文字は両語に実際に存在する末尾と先頭として指定する。
使われ方：外側表の重複行圧縮後の出力の非退化性を証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

variable {α : Type*}

/-- 概要：同じ末尾・先頭を一つにした連結は縮約結果を保つ（BF §1.5.8）。
方針：両語を共有文字で分解し、境界の隣接二コピーを縮める。
規約：内部の非退化性を要求しない。
使われ方：融合出力の縮約不変性を元の選択語へ戻す。 -/
lemma collapse_dropLast_append_shared [DecidableEq α] (left right : List α) (a : α)
    (hl : left.getLast? = some a) (hr : right.head? = some a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (left.dropLast ++ right) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (left ++ right) := by
  obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  obtain ⟨post, rfl⟩ := List.head?_eq_some_iff.mp hr
  simp only [List.dropLast_concat, List.append_assoc, List.singleton_append]
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_duplicate_in_context pre a post).symm

/-- 概要：非退化な両語を共有末尾一つで接合しても非退化（BF §1.5.8）。
方針：singleton の重なりに沿った IsChain の連結を使う。
規約：非退化性は隣接非一致。共有文字以外の重複は許す。
使われ方：重複外側行を融合した出力の非退化性の局所段階。 -/
lemma isChain_dropLast_append_shared (left right : List α) (a : α)
    (hl : left.getLast? = some a) (hr : right.head? = some a)
    (hleft : left.IsChain (· ≠ ·)) (hright : right.IsChain (· ≠ ·)) :
    (left.dropLast ++ right).IsChain (· ≠ ·) := by
  obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  obtain ⟨post, rfl⟩ := List.head?_eq_some_iff.mp hr
  simp only [List.dropLast_concat]
  simpa only [List.append_assoc, List.singleton_append] using
    hleft.append_overlap hright (show [a] ≠ [] by simp)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
