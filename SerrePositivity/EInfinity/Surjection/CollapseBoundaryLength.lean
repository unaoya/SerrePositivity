module

public import SerrePositivity.EInfinity.Surjection.AdjacentCollapseSeparated

/-!
# 非退化な二語の連結の縮約長

概要：Berger–Fresse §1.5.8 の逆構成で、挿入連続区間の境界が失う一文字を数える。
方針：各語の内部は非退化なので、縮約で消えるのは等しい境界の一コピーだけとなる。
規約：連続する二語は非空。離れた同値文字は消さない。
使われ方：復元両語の長さから全分割境界の共有端点を強制する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

/-- 概要：非空非退化な二語の連結は等しい境界でだけ一文字縮む（BF §1.5.8）。
方針：前の語で帰納し、内部の非一致を保ったまま最後の一文字と後続先頭を比較する。
規約：境界の等号は Option の末尾・先頭で表す。
使われ方：区間ごとの縮約損失を正確に零または一と数える。 -/
lemma collapse_append_length (pre post : List α)
    (hpre : pre.IsChain (· ≠ ·)) (hpost : post.IsChain (· ≠ ·))
    (hnpre : pre ≠ []) (hnpost : post ≠ []) :
    (collapse (pre ++ post)).length + (if pre.getLast? = post.head? then 1 else 0) =
      pre.length + post.length := by
  induction pre with
  | nil => exact (hnpre rfl).elim
  | cons a pre ih =>
    cases pre with
    | nil =>
      cases post with
      | nil => exact (hnpost rfl).elim
      | cons b post =>
        change (prepend a (collapse (b :: post))).length +
          (if (some a : Option α) = some b then 1 else 0) = _
        rw [collapse_eq_self _ hpost]
        by_cases he : a = b <;> simp [prepend, he, Nat.add_comm, Nat.add_left_comm]
    | cons b pre =>
      have hn : a ≠ b := (List.isChain_cons_cons.mp hpre).1
      have hi := ih hpre.tail (by simp)
      change (collapse (a :: b :: (pre ++ post))).length + _ = _
      rw [collapse_cons_cons_ne a b _ hn]
      simp only [List.cons_append, List.length_cons, List.getLast?_cons_cons] at hi ⊢
      omega

/-- 概要：非空非退化な前半を任意の非空語へ付けたときの縮約長（BF §1.5.8）。
方針：後半だけを先に縮約し、その先頭保存を二語の損失公式へ渡す。
規約：後半の内部は退化してよい。
使われ方：多数の挿入部分語の境界損失を帰納的に数える。 -/
lemma collapse_prepend_length (pre post : List α) (hpre : pre.IsChain (· ≠ ·))
    (hnpre : pre ≠ []) (hnpost : post ≠ []) :
    (collapse (pre ++ post)).length + (if pre.getLast? = post.head? then 1 else 0) =
      pre.length + (collapse post).length := by
  have hn : collapse post ≠ [] := fun h => hnpost ((collapse_eq_nil_iff _).mp h)
  have he := collapse_append_length pre (collapse post) hpre (collapse_isChain post) hnpre hn
  rw [collapse_head?] at he
  have hc : collapse (pre ++ collapse post) = collapse (pre ++ post) :=
    collapse_append_congr pre _ _ (collapse_eq_self _ (collapse_isChain post))
  rwa [hc] at he

end SerrePositivity.EInfinity.Surjection.AdjacentCollapse
