module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Renaming

/-!
模型。文献の定義との比較は後で
# 全射語の文字の削除

概要：Berger–Fresse §1.2.3 の微分の各項となる一文字削除を定める。
方針：指定位置を飛ばす Fin.succAbove を語へ前合成する。
規約：削除後の非全射・退化な語は後で自由加群の零元とする。
使われ方：符号付き削除微分と TR の鎖写像性を検証する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定位置の文字を除いた語（BF §1.2.3）。
方針：一つの位置を飛ばす順序単射で制限する。
規約：出力の長さは一つ小さく、値集合は変えない。
使われ方：削除微分の各項を与える。 -/
def erase {n l : ℕ} (u : Fin (l + 1) → Fin n) (i : Fin (l + 1)) : Fin l → Fin n :=
  u ∘ i.succAbove

/-- 概要：削除した語の文字は対応する元の位置の文字（BF §1.2.3）。
方針：削除の定義を評価する。
規約：指定位置自身は像に現れない。
使われ方：削除後の全射性と退化性を判定する。 -/
@[simp]
lemma erase_apply {n l : ℕ} (u : Fin (l + 1) → Fin n) (i : Fin (l + 1)) (j : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i j = u (i.succAbove j) := rfl

/-- 概要：文字の削除と値の置換は可換（BF §1.2.3）。
方針：前合成と後合成の結合則を使う。
規約：削除位置は置換で動かさない。
使われ方：削除微分の同変性を示す。 -/
lemma erase_rename {n l : ℕ} (σ : Equiv.Perm (Fin n))
    (u : Fin (l + 1) → Fin n) (i : Fin (l + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (σ ∘ u) i = σ ∘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i := rfl

/-- 概要：全射語の削除が全射なのは削除した値に別の出現があるとき（BF §1.2.3）。
方針：削除した値の逆像を調べ、飛ばした位置以外の添字を succAbove で戻す。
規約：隣接値の非退化性は要求しない。
使われ方：一度しか現れない値の削除項を零にする。 -/
lemma erase_surjective_iff {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (hu : Function.Surjective u) (i : Fin (l + 1)) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) ↔ ∃ j : Fin (l + 1), j ≠ i ∧ u j = u i := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := h (u i)
    exact ⟨i.succAbove j, Fin.succAbove_ne _ _, hj⟩
  · rintro ⟨j, hji, hj⟩ k
    obtain ⟨a, ha⟩ := hu k
    by_cases hai : a = i
    · subst a
      obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hji
      exact ⟨b, by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_apply, hb] using hj.trans ha⟩
    · obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hai
      exact ⟨b, by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_apply, hb] using ha⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
