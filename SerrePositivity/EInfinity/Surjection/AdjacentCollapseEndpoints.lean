module

public import SerrePositivity.EInfinity.Surjection.AdjacentCollapsePrefixes

/-!
# 連続重複縮約が保つ末尾

概要：Berger–Fresse §1.5.8 の外側選択行の境界を、縮約前の実際の境界へ戻す。
方針：prepend で前のコピーを省いても末尾が変わらないことを帰納的に使う。
規約：先頭だけでなく末尾も保存し、空語も同じ none を返す。
使われ方：水平境界の非一致を縮約した外側選択語の連結へ移す。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

/-- 概要：同じ先頭を省く付加は末尾を変えない（BF §1.5.8）。
方針：省く場合は同じ二文字の先頭付加の末尾保存を使う。
規約：後続が空なら追加文字が末尾となる。
使われ方：縮約の末尾保存の帰納段階。 -/
lemma prepend_getLast? (a : α) (xs : List α) :
    (prepend a xs).getLast? = (a :: xs).getLast? := by
  cases xs with
  | nil => rfl
  | cons b xs =>
    by_cases he : a = b
    · subst b
      simp only [prepend, ite_true, List.getLast?_cons_cons]
    · rw [prepend, ite_eq_right he]

/-- 概要：連続重複縮約は語の末尾文字を保つ（BF §1.5.8）。
方針：語で帰納し、非空な後続の縮約から prepend の末尾保存を使う。
規約：空語の末尾も none のまま。
使われ方：縮約した外側選択語の末尾を元の合成行末へ同定する。 -/
lemma collapse_getLast? (xs : List α) : (collapse xs).getLast? = xs.getLast? := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [collapse, prepend_getLast?]
    cases xs with
    | nil => rfl
    | cons b xs =>
      have hn : collapse (b :: xs) ≠ [] := fun h =>
        List.cons_ne_nil _ _ ((collapse_eq_nil_iff _).mp h)
      rw [List.getLast?_cons_of_ne_nil hn, ih, List.getLast?_cons_cons]

end SerrePositivity.EInfinity.Surjection.AdjacentCollapse
