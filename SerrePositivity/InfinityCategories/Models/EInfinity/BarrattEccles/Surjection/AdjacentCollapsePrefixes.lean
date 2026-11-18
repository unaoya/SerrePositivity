module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

/-!
模型。文献の定義との比較は後で
# 連続重複縮約と先頭部分・後続部分

概要：Berger–Fresse §1.5.8 の外側選択行を合成選択行の縮約から復元する。
方針：先頭部分を縮めても先頭部分であり、共有文字からの後続も縮約順位で一致する。
規約：入力語は非退化でなくてよい。後続は選択末尾の文字を残す。
使われ方：復元した外側行長と実際の除外更新を照合する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

/-- 概要：連続重複の縮約は先頭文字を保つ（BF §1.5.8）。
方針：先頭付加の二つの分岐で先頭を計算する。
規約：空語の先頭も none のまま。
使われ方：縮約の非空性と隣接非一致の先頭付加を得る。 -/
lemma collapse_head? (xs : List α) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse xs).head? = xs.head? := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend a (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse xs)).head? = some a
    cases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse xs with
    | nil => rfl
    | cons b ys => by_cases h : a = b <;> simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend, h]

/-- 概要：非空語の縮約は非空（BF §1.5.8）。
方針：先頭の保存から空語との同値を得る。
規約：全ての文字が同じ場合も一文字は残す。
使われ方：縮約した選択行長の正値性を得る。 -/
lemma collapse_eq_nil_iff (xs : List α) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse xs = [] ↔ xs = [] := by
  rw [← List.head?_eq_none_iff, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_head?, List.head?_eq_none_iff]

/-- 概要：異なる先頭二文字の間では縮約が先頭を追加する（BF §1.5.8）。
方針：後続の縮約の先頭を保存し、prepend の非一致分岐を使う。
規約：後続の内部には連続重複を許す。
使われ方：元の添字を縮約後の順位へ移す帰納計算。 -/
lemma collapse_cons_cons_ne (a b : α) (xs : List α) (h : a ≠ b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (a :: b :: xs) = a :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (b :: xs) := by
  have hh : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (b :: xs)).head? = some b := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_head? _
  obtain ⟨tail, ht⟩ := List.head?_eq_some_iff.mp hh
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend a (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (b :: xs)) = a :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (b :: xs)
  rw [ht, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend, ite_eq_right h]

/-- 概要：連続重複を作らない先頭付加は先頭部分関係を保つ（BF §1.5.8）。
方針：先頭部分の共有先頭との一致で prepend の分岐を同期する。
規約：空の先頭部分も許す。
使われ方：縮約が先頭部分を先頭部分へ移すことを帰納的に示す。 -/
lemma prepend_prefix (a : α) (xs ys : List α) (h : xs <+: ys) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend a xs <+: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend a ys := by
  obtain ⟨tail, rfl⟩ := h
  cases xs with
  | nil =>
    cases tail with
    | nil => exact ⟨[], rfl⟩
    | cons b tail =>
      by_cases he : a = b
      · subst b; exact ⟨tail, by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend]⟩
      · exact ⟨b :: tail, by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend, he]⟩
  | cons b xs =>
    by_cases he : a = b <;> simp only [List.cons_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend, he, ite_true, ite_false]
    · exact ⟨tail, rfl⟩
    · exact ⟨tail, rfl⟩

/-- 概要：語の先頭部分の縮約は全体の縮約の先頭部分（BF §1.5.8）。
方針：元の先頭部分で帰納して prepend の先頭部分保存を使う。
規約：境界で同じ文字が重なってもよい。
使われ方：選択語を縮めた長さで復元行を切る。 -/
lemma collapse_append_prefix (pre post : List α) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse pre <+: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (pre ++ post) := by
  induction pre with
  | nil => exact ⟨_, rfl⟩
  | cons a pre ih => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend_prefix a _ _ ih

/-- 概要：縮約した選択先頭部分は縮約後の同じ長さの先頭部分（BF §1.5.8）。
方針：take と drop の分割を縮約の先頭部分保存へ適用する。
規約：r が語長を超える場合も成立する。
使われ方：実際の外側選択語の復元と行長条件を得る。 -/
lemma collapse_take_prefix (xs : List α) (r : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse xs).take (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (xs.take r)).length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (xs.take r) := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_append_prefix (xs.take r) (xs.drop r)
  rw [List.take_append_drop] at h
  obtain ⟨tail, ht⟩ := h
  rw [← ht, List.take_left]

/-- 概要：元の共有文字からの後続は縮約後の同じ選択順位からの後続（BF §1.5.8）。
方針：共有添字で帰納し、等しい隣接値を省く場合と異なる場合の順位を比較する。
規約：i は零始まりで元の語に属する位置。
使われ方：選択末尾を残す元の除外更新を縮約後の外側除外へ戻す。 -/
lemma collapse_drop_rank (xs : List α) (i : ℕ) (hi : i < xs.length) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (xs.drop i) = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse xs).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (xs.take (i + 1))).length - 1) := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => simp only [List.length_nil] at hi; omega
    | cons a xs => simp only [List.drop_zero, List.take_succ_cons, List.take_zero,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend, List.length_singleton, Nat.sub_self]
  | succ i ih =>
    cases xs with
    | nil => simp only [List.length_nil] at hi; omega
    | cons a xs =>
      cases xs with
      | nil => simp only [List.length_cons, List.length_nil] at hi; omega
      | cons b xs =>
        have hi' : i < (b :: xs).length := by
          simp only [List.length_cons] at hi ⊢
          omega
        have ht := ih (b :: xs) hi'
        by_cases he : a = b
        · subst a
          simpa only [List.drop_succ_cons, List.take_succ_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_duplicate] using ht
        · rw [List.drop_succ_cons, List.take_succ_cons, List.take_succ_cons,
            _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_cons_cons_ne a b xs he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_cons_cons_ne a b (xs.take i) he]
          cases hq : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (b :: xs.take i) with
          | nil =>
            have hn := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_nil_iff (b :: xs.take i)).mp hq
            simp only [List.cons_ne_nil] at hn
          | cons c cs =>
            simp only [List.length_cons, Nat.add_sub_cancel, List.drop_succ_cons]
            simpa only [List.take_succ_cons, hq, List.length_cons, Nat.add_sub_cancel] using ht

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse
