module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OccurrenceOrder

/-!
模型。文献の定義との比較は後で
# 指定値の出現で切った外側語の境界

概要：Berger–Fresse §1.2.5 の外側語を指定値の各出現で切る単調列を構成する。
方針：最初は零、続いて各出現位置、最後以降は語の最終位置を取る。
規約：出現そのものは前後両成分の端点になる。
使われ方：外側成分の次数の総和と後続次数を計算する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定値で切る外側成分の境界位置（BF §1.2.5）。
方針：出現位置の昇順列の前後に元の語の両端を付加する。
規約：零始まりで、出現の前にも後にも一成分を置く。
使われ方：右からの代入で通過する外側成分の次数を指定する。 -/
def occurrenceBoundary {n l : ℕ} (v : Fin l → Fin n) (k : Fin n) (i : ℕ) : ℕ :=
  if i = 0 then 0 else if h : i - 1 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k then
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k ⟨i - 1, h⟩).val else l - 1

/-- 概要：最初の外側境界は語の先頭（BF §1.2.5）。
方針：定義の零分岐を評価する。
規約：空語のときも零。
使われ方：外側成分次数の総和の始端を決める。 -/
@[simp] lemma occurrenceBoundary_zero {n l : ℕ} (v : Fin l → Fin n) (k : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary v k 0 = 0 := by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary, ite_true]

/-- 概要：第 i 出現は第 i+1 境界（BF §1.2.5）。
方針：出現番号の一つ後の有限範囲分岐を評価する。
規約：第零境界は出現に数えない。
使われ方：後続外側次数の始点を出現の行番号に同定する。 -/
@[simp] lemma occurrenceBoundary_at {n l : ℕ} (v : Fin l → Fin n) (k : Fin n)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary v k (i.val + 1) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k i).val := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, dite_eq_left i.isLt]

/-- 概要：全出現の後の境界は元の語の最終位置（BF §1.2.5）。
方針：出現列の範囲外の分岐を評価する。
規約：最後以降の境界は一定。
使われ方：外側成分の総次数を元の次数へ戻す。 -/
@[simp] lemma occurrenceBoundary_last {n l : ℕ} (v : Fin l → Fin n) (k : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary v k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k + 1) = l - 1 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, lt_self_iff_false, ↓reduceDIte]

/-- 概要：外側の成分境界は単調（BF §1.2.5）。
方針：零・出現列の内部・末尾の三つに分け、出現の昇順性と位置の上界を使う。
規約：全自然数上の境界列として比較する。
使われ方：外側成分次数の差を望遠鏡和へ移す。 -/
lemma occurrenceBoundary_mono {n l : ℕ} (v : Fin l → Fin n) (k : Fin n) :
    Monotone (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary v k) := by
  intro a b hab
  by_cases ha0 : a = 0
  · simp only [ha0, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary_zero, Nat.zero_le]
  · have hb0 : b ≠ 0 := by omega
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceBoundary, ite_eq_right ha0, ite_eq_right hb0]
    by_cases ha : a - 1 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k
    · by_cases hb : b - 1 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k
      · rw [dite_eq_left ha, dite_eq_left hb]
        exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_strictMono v k).monotone
          (show (⟨a - 1, ha⟩ : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k)) ≤ ⟨b - 1, hb⟩ by
            change a - 1 ≤ b - 1
            omega)
      · rw [dite_eq_left ha, dite_eq_right hb]
        have := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k ⟨a - 1, ha⟩).isLt
        omega
    · have hb : ¬ b - 1 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k := by omega
      rw [dite_eq_right ha, dite_eq_right hb]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
