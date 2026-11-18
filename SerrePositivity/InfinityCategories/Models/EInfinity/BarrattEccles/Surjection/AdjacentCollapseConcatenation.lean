module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

/-!
模型。文献の定義との比較は後で
# 各行の縮約と全出力の縮約の一致

概要：Berger–Fresse §1.5.8 の行ごとに復元した外側語を全出力の外側語へ同定する。
方針：連結前に片側を縮めても最終縮約は変わらないことを帰納的に示す。
規約：異なる行の境界にも同じ値があってよい。
使われ方：圧縮した外側表の出力を元の合成出力の外側復元へ戻す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

/-- 概要：先頭付加で省いた一コピーは連結後の縮約にも影響しない（BF §1.5.8）。
方針：prepend がコピーを省く場合は元の隣接二コピーの縮約を使う。
規約：後続語は任意。
使われ方：左側の語を先に縮約する帰納法の一段。 -/
lemma collapse_prepend_append (a : α) (xs post : List α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend a xs ++ post) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (a :: xs ++ post) := by
  cases xs with
  | nil => rfl
  | cons b xs =>
    by_cases he : a = b
    · subst b
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend, ite_true, List.cons_append] using
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_duplicate a (xs ++ post)).symm
    · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend, ite_eq_right he, List.cons_append]

/-- 概要：左側を先に縮約しても連結語の最終縮約は変わらない（BF §1.5.8）。
方針：左語で帰納し、先頭付加の縮約不変性で後続の帰納法へ戻す。
規約：左語・右語の非退化性を要求しない。
使われ方：行ごとの外側縮約を全語の縮約へまとめる。 -/
lemma collapse_left_append (pre post : List α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse pre ++ post) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (pre ++ post) := by
  induction pre with
  | nil => rfl
  | cons a pre ih =>
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend a (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse pre) ++ post) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (a :: pre ++ post)
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_prepend_append]
    exact congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend a) ih

/-- 概要：各行を縮約して連結した語の縮約は元の全連結語の縮約（BF §1.5.8）。
方針：行リストで帰納し、先頭行と後続全行の縮約をそれぞれ戻す。
規約：空行や同じ境界文字を持つ行を許す。
使われ方：圧縮外側表の出力と合成出力全体の外側復元の一致。 -/
lemma collapse_flatten (words : List (List α)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (words.map _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse).flatten = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse words.flatten := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    simp only [List.map_cons, List.flatten_cons]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_left_append]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_append_congr word _ _ ih

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse
