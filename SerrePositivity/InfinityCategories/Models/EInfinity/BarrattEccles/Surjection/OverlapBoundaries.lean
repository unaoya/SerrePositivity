module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapCoverage

/-!
模型。文献の定義との比較は後で
# 重なる分割の単調な境界列

概要：Berger–Fresse §1.2.4–5 の部分語の端点を一つの単調列へまとめる。
方針：部分長−1 の部分和を使い、最後以降は語の最終位置に固定する。
規約：非空語では各部分語の末尾が次の先頭に一致する。
使われ方：部分語の行次数の和を隣接境界の行番号の差で計算する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition

variable {t l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l)

/-- 概要：部分語の開始位置は分割番号に単調（BF §1.2.4）。
方針：部分長−1 の非負な部分和を比較する。
規約：長さ 1 の部分語が続くとき同じ開始位置を許す。
使われ方：行番号の差の望遠鏡和へ単調性を供給する。 -/
lemma start_mono : Monotone r.start := by
  intro i j hij
  have h := List.sum_take_add_sum_drop
    ((List.ofFn (fun k => (r.val k).val - 1)).take j.val) i.val
  rw [List.take_take, Nat.min_eq_left hij] at h
  change ((List.ofFn (fun k => (r.val k).val - 1)).take i.val).sum ≤
    ((List.ofFn (fun k => (r.val k).val - 1)).take j.val).sum
  omega

/-- 概要：最後以降を最終位置に固定した分割境界の列（BF §1.2.4）。
方針：分割番号 t 未満はその開始位置、それ以降は l−1 とする。
規約：零始まりの自然数位置。
使われ方：有限和を自然数範囲の望遠鏡和へ直す。 -/
def boundary (i : ℕ) : ℕ := if h : i < t then r.start ⟨i, h⟩ else l - 1

/-- 概要：実際の部分語番号で境界はその開始位置（BF §1.2.4）。
方針：有限添字の範囲条件で定義を評価する。
規約：証明項に依存しない。
使われ方：成分次数を隣接境界の行番号の差へ直す。 -/
@[simp] lemma boundary_at (i : Fin t) : r.boundary i.val = r.start i := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.boundary, dite_eq_left i.isLt]

/-- 概要：最後以降の境界は元の語の最終位置（BF §1.2.4）。
方針：範囲外の定義を評価する。
規約：語長が零でも l−1 は零。
使われ方：望遠鏡和の終端を元の語の最後の行番号へ戻す。 -/
@[simp] lemma boundary_last : r.boundary t = l - 1 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.boundary, lt_self_iff_false, ↓reduceDIte]

/-- 概要：次の境界は現在の部分語の最終位置（BF §1.2.4）。
方針：次の部分語がある場合は共有端点、最後なら全語の終了境界を使う。
規約：元の語は非空。
使われ方：各部分語の行次数を隣接境界で評価する。 -/
lemma boundary_next (hl : 0 < l) (i : Fin t) :
    r.boundary (i.val + 1) = r.start i + (r.val i).val - 1 := by
  by_cases hi : i.val + 1 < t
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.boundary, dite_eq_left hi]
    have hs := r.start_next i ⟨i.val + 1, hi⟩ rfl
    have hp := r.positive hl i
    omega
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.boundary, dite_eq_right hi]
    have he := r.last_end hl i (by have := i.isLt; omega)
    omega

/-- 概要：非空語の分割境界は全自然数上で単調（BF §1.2.4）。
方針：二つとも範囲内なら開始位置の単調性、それ以外は最後の位置の上界を使う。
規約：最後以降は一定。
使われ方：成分次数の差を自然数の望遠鏡和で足す。 -/
lemma boundary_mono (hl : 0 < l) : Monotone r.boundary := by
  intro a b hab
  by_cases ha : a < t
  · by_cases hb : b < t
    · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.boundary, dite_eq_left ha, dite_eq_left hb]
      exact r.start_mono (show (⟨a, ha⟩ : Fin t) ≤ ⟨b, hb⟩ from hab)
    · have hs := r.start_add_length_le ⟨a, ha⟩
      have hp := r.positive hl ⟨a, ha⟩
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.boundary, dite_eq_left ha, dite_eq_right hb]
      omega
  · have hb : ¬ b < t := by omega
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.boundary, dite_eq_right ha, dite_eq_right hb, Nat.le_refl]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition
