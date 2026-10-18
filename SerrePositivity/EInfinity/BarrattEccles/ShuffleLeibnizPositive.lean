module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleBoundaryDecomposition
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleDirectionalTransport
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleEndpointTransport
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalContribution
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleVerticalContribution

/-!
# 正次数の二入力に対する shuffle の Leibniz 則

概要：Berger–Fresse §1.1.3 の shuffle の微分を正次数の二入力について計算する。
方針：全境界を分割し、同方向の面を添字替えし、混合角の和を相殺する。
規約：第一の微分項の出力次数を全境界の出力次数へ明示的に移送する。
使われ方：shuffle の部分合成を鎖写像へまとめるための生成元の計算となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：正次数の shuffle の全微分は水平・垂直の二つの寄与に等しい（Berger–Fresse §1.1.3）。
方針：始端と終端を辺の向きで分け、内部の角の三分割から混合角を消去する。
規約：両入力の次数は p+1 と q+1 である。
使われ方：方向別に証明した微分項を全境界の等式へ代入する。 -/
lemma shuffleValue_d_positive_contributions (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (simplicial (m + 1)) _⦋p + 1⦌) (y : (simplicial n) _⦋q + 1⦌) :
    (normalizedChains A (m + n)).d (p + 1 + (q + 1)) (p + 1 + q)
        (shuffleValue A m n i (p + 1) (q + 1) x y) =
      degreeTransport A (m + n) (by omega : p + (q + 1) = p + 1 + q)
        (horizontalBoundaryContribution A m n i x y) +
      verticalBoundaryContribution A m n i x y := by
  classical
  have hN : 0 < p + 1 + (q + 1) := by omega
  erw [shuffleValue_d_decomposition A m n i (p + 1) (q + 1) hN x y,
    sum_adjacentBoundaryTerm A m n i hN x y]
  let first := fun s : ShufflePath (p + 1) (q + 1) =>
    (s.sign : ℤ) • normalizedGenerator A (m + n) (p + 1 + (q + 1) - 1)
      ((simplicial (m + n)).map (boundaryFaceMap (p + 1 + (q + 1)) hN 0).op
        (shuffleSimplex m n i s x y))
  let last := fun s : ShufflePath (p + 1) (q + 1) =>
    (-1 : ℤ) ^ (p + 1 + (q + 1)) • (s.sign : ℤ) •
      normalizedGenerator A (m + n) (p + 1 + (q + 1) - 1)
        ((simplicial (m + n)).map
          (boundaryFaceMap (p + 1 + (q + 1)) hN (Fin.last (p + 1 + (q + 1)))).op
          (shuffleSimplex m n i s x y))
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun s : ShufflePath (p + 1) (q + 1) => 0 ∈ s.val) first,
    ← Fintype.sum_subtype_add_sum_subtype
      (fun s : ShufflePath (p + 1) (q + 1) => Fin.last (p + 1 + q) ∈ s.val) last]
  dsimp only [first, last]
  rw [sum_horizontalFirstBoundary_transport A m n i hN x y,
    sum_verticalFirstBoundary A m n i hN x y,
    sum_horizontalAdjacentBoundary A m n i hN x y,
    sum_verticalAdjacentBoundary A m n i hN x y,
    sum_horizontalLastBoundary_transport A m n i hN (Fin.last (p + 1 + q))
      (by simp only [Fin.val_last]; omega) x y,
    sum_verticalLastBoundary A m n i hN x y]
  rw [horizontalBoundaryContribution, verticalBoundaryContribution,
    sum_horizontal_first_face A m n i x y, sum_horizontal_last_face A m n i
      ⟨p + (q + 1), by omega⟩ (by dsimp; omega) x y,
    sum_vertical_first_face A m n i x y, sum_vertical_last_face A m n i x y]
  simp only [map_add]
  have regroup (a b c d e f : (normalizedChains A (m + n)).X (p + 1 + q)) :
      (a + b) + (c + d) + (e + f) = ((a + c) + e) + ((b + d) + f) := by abel
  exact regroup _ _ _ _ _ _

/-- 概要：正次数の二入力の生成元について shuffle は Leibniz 則を満たす（Berger–Fresse §1.1.3）。
方針：全微分の二つの寄与を、既存の方向別の微分項の等式で置き換える。
規約：第二の入力の微分に (−1)^(p+1) を付ける。
使われ方：双線形性によって任意の正規化鎖へ微分の両立性を拡張する。 -/
lemma shuffleValue_d_positive (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (simplicial (m + 1)) _⦋p + 1⦌) (y : (simplicial n) _⦋q + 1⦌) :
    (normalizedChains A (m + n)).d (p + 1 + (q + 1)) (p + 1 + q)
        (shuffleValue A m n i (p + 1) (q + 1) x y) =
      degreeTransport A (m + n) (by omega : p + (q + 1) = p + 1 + q)
        (shuffleBilinear A m n i p (q + 1)
          ((normalizedChains A (m + 1)).d (p + 1) p
            (normalizedGenerator A (m + 1) (p + 1) x))
          (normalizedGenerator A n (q + 1) y)) +
      (-1 : ℤ) ^ (p + 1) • shuffleBilinear A m n i (p + 1) q
        (normalizedGenerator A (m + 1) (p + 1) x)
        ((normalizedChains A n).d (q + 1) q (normalizedGenerator A n (q + 1) y)) := by
  rw [shuffleValue_d_positive_contributions A m n i p q x y,
    horizontalBoundaryContribution_eq A m n i x y, verticalBoundaryContribution_eq A m n i x y]

end SerrePositivity.EInfinity.BarrattEccles
