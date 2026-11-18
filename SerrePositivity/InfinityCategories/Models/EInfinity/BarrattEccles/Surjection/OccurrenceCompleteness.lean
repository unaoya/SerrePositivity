module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OccurrenceOrder

/-!
模型。文献の定義との比較は後で
# 全出現の列挙の完全性と連続出現間の不出現

概要：Berger–Fresse §1.5.7 の水平語の内部に指定値がないことを元の出現列から証明する。
方針：全ての実際の出現に有限出現番号を与え、出現番号の狭義単調性へ戻す。
規約：全射性・非退化性を要求しない。
使われ方：元の外側語を全出現境界で切り、成分語とリスト代入を照合する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定値の全ての実際の出現は列挙された出現の一つ（BF §1.5.7）。
方針：有限位置の filter への所属を有限リスト添字へ戻す。
規約：出現番号は零始まり。
使われ方：境界間の追加出現を出現番号間の不可能な位置へ移す。 -/
lemma occurrenceAt_complete {n l : ℕ} (v : Fin l → Fin n) (k : Fin n)
    (p : Fin l) (hp : v p = k) : ∃ j, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j = p := by
  have hm : p ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrencePositions v k := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrencePositions, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq]
    exact hp
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hm
  refine ⟨⟨j, by rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrencePositions_length]; exact hj⟩, ?_⟩
  exact he

/-- 概要：最初の出現より前には指定値がない（BF §1.5.7）。
方針：仮の出現の番号が第零番号より小さくなることを排除する。
規約：最初の出現番号を明示する。
使われ方：最初の水平語の内部を代入なしに通過する。 -/
lemma occurrenceAt_none_before_first {n l : ℕ} (v : Fin l → Fin n) (k : Fin n)
    (ht : 0 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k) (p : Fin l)
    (hp : p < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k ⟨0, ht⟩) : v p ≠ k := by
  intro he
  obtain ⟨j, hj⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_complete v k p he
  have hb : j < (⟨0, ht⟩ : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k)) :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_strictMono v k).lt_iff_lt.mp (by rw [hj]; exact hp)
  exact (Nat.not_lt_zero j.val) hb

/-- 概要：連続する二出現の間には指定値がない（BF §1.5.7）。
方針：追加出現の番号が隣接する二番号の間に入ることを排除する。
規約：元の語の位置と出現番号を区別する。
使われ方：中間水平語の両端以外を代入なしに通過する。 -/
lemma occurrenceAt_none_between {n l : ℕ} (v : Fin l → Fin n) (k : Fin n)
    (i j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k)) (hij : j.val = i.val + 1) (p : Fin l)
    (hip : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k i < p) (hpj : p < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j) : v p ≠ k := by
  intro he
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_complete v k p he
  have hia : i < a := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_strictMono v k).lt_iff_lt.mp (by rw [ha]; exact hip)
  have haj : a < j := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_strictMono v k).lt_iff_lt.mp (by rw [ha]; exact hpj)
  change i.val < a.val at hia
  change a.val < j.val at haj
  omega

/-- 概要：最後の出現より後には指定値がない（BF §1.5.7）。
方針：追加出現の番号が最後の番号を超えることを排除する。
規約：最後の番号の直後が出現回数。
使われ方：最終水平語の末尾まで代入なしに通過する。 -/
lemma occurrenceAt_none_after_last {n l : ℕ} (v : Fin l → Fin n) (k : Fin n)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k)) (hi : i.val + 1 = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k) (p : Fin l)
    (hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k i < p) : v p ≠ k := by
  intro he
  obtain ⟨j, hj⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_complete v k p he
  have hb : i < j := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_strictMono v k).lt_iff_lt.mp (by rw [hj]; exact hp)
  have := j.isLt
  change i.val < j.val at hb
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
