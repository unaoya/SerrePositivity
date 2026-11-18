module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComponentExtraction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapBoundaries

/-!
模型。文献の定義との比較は後で
# 全ての分割境界の有限位置

概要：Berger–Fresse §1.5.7 の成分列の開始・共有・終了位置を一つの有限位置列にまとめる。
方針：既存の自然数境界を有限位置へ移し、元の成分端点へ照合する。
規約：正の語長で全自然数上に定義し、最後以降は元の最終位置。
使われ方：水平・垂直成分を交互に接続する共通の状態添字。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition

/-- 概要：全ての分割境界の有限位置（BF §1.5.7）。
方針：実際の成分番号は有限開始位置、それ以降は元の語の最終位置。
規約：語長は正。
使われ方：各成分間の同じ共有状態を指定する。 -/
def boundaryPosition {t l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l) (hl : 0 < l) (i : ℕ) : Fin l :=
  ⟨r.boundary i, by
    by_cases hi : i < t
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.boundary, dite_eq_left hi]
      exact (r.startPosition hl ⟨i, hi⟩).isLt
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.boundary, dite_eq_right hi]
      omega⟩

/-- 概要：実際の成分番号の境界はその有限開始位置（BF §1.5.7）。
方針：自然数境界の同じ範囲の式を有限位置へ移す。
規約：証明項に依存しない。
使われ方：水平の固定位置と垂直の開始位置を一致させる。 -/
@[simp] lemma boundaryPosition_at {t l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l) (hl : 0 < l)
    (i : Fin t) : r.boundaryPosition hl i.val = r.startPosition hl i := by
  apply Fin.ext
  exact r.boundary_at i

/-- 概要：次の境界は現在成分の有限終了位置（BF §1.5.7）。
方針：共有端点を表す既存の自然数境界の式を使う。
規約：最終成分も同じ式。
使われ方：垂直の終状態と次の水平の始状態を一致させる。 -/
@[simp] lemma boundaryPosition_next {t l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l) (hl : 0 < l)
    (i : Fin t) : r.boundaryPosition hl (i.val + 1) = r.endPosition hl i := by
  apply Fin.ext
  exact r.boundary_next hl i

/-- 概要：最後の有限分割境界は元の最終位置（BF §1.5.7）。
方針：自然数境界の最終値を読む。
規約：語長は正なので最後の位置が存在する。
使われ方：最終水平成分に内側の最後の位置を渡す。 -/
lemma boundaryPosition_last {t l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l) (hl : 0 < l) :
    (r.boundaryPosition hl t).val + 1 = l := by
  change r.boundary t + 1 = l
  rw [r.boundary_last]
  omega

/-- 概要：成分が一つ以上あると最初の有限境界は零（BF §1.5.7）。
方針：第零成分の開始位置の空の部分和を評価する。
規約：分割数は正。
使われ方：合成表の最初の進行状態の空性を示す。 -/
lemma boundaryPosition_zero {t l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l) (hl : 0 < l) (ht : 0 < t) :
    (r.boundaryPosition hl 0).val = 0 := by
  change r.boundary 0 = 0
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.boundary, dite_eq_left ht, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.start, List.take_zero, List.sum_nil]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition
