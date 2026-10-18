module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleBoundaryFaces

/-!
# shuffle の全境界の始端・内部・終端への分割

概要：Berger–Fresse §1.1.3 の正次数の shuffle の微分を端点と隣接する角の和へ分割する。
方針：頂点の有限和を最初・内部・最後へ分け、内部の頂点を隣接角で添字替えする。
規約：全ての出力を次数 p+q−1 に統一して扱う。
使われ方：全微分を水平・垂直の寄与と混合角の相殺へ接続する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：正次数の頂点上の有限和を最初・内部・最後に分ける（Berger–Fresse §1.1.3）。
方針：最初の頂点の分離と最後の頂点の分離を順に適用する。
規約：内部の番号 a は Fin(N−1) で、その頂点番号は a+1 である。
使われ方：shuffle の境界面の和を端点と角の和へ分ける。 -/
lemma sum_fin_first_interior_last {M : Type*} [AddCommMonoid M]
    (N : ℕ) (hN : 0 < N) (f : Fin (N + 1) → M) :
    ∑ b, f b = f 0 + (∑ a : Fin (N - 1), f ⟨a.val + 1, by have h := a.isLt; omega⟩) +
      f (Fin.last N) := by
  cases N with
  | zero => omega
  | succ r =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [add_assoc]
    rfl

variable (A : Type u) [CommRing A]

/-- 概要：隣接角の境界和は小さい辺番号による内部面の二重和に等しい（Berger–Fresse §1.1.3）。
方針：角と経路・小さい辺番号の全単射を有限和に適用する。
規約：面の番号は小さい辺番号 a に一つ加えた値である。
使われ方：全境界の内部面と三種類の角の寄与を同定する。 -/
lemma sum_adjacentBoundaryTerm_enumeration (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (hN : 0 < p + q) (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌) :
    ∑ c : AdjacentCorner p q, adjacentBoundaryTerm A m n i hN x y c =
      ∑ s : ShufflePath p q, ∑ a : Fin (p + q - 1),
        (-1 : ℤ) ^ (a.val + 1) • (s.sign : ℤ) •
          normalizedGenerator A (m + n) (p + q - 1)
            ((simplicial (m + n)).map
              (boundaryFaceMap (p + q) hN ⟨a.val + 1, by have h := a.isLt; omega⟩).op
              (shuffleSimplex m n i s x y)) := by
  classical
  rw [← (adjacentCornerEquiv p q hN).sum_comp (adjacentBoundaryTerm A m n i hN x y),
    Fintype.sum_prod_type]
  rfl

/-- 概要：shuffle の全微分は始端・内部の角・終端の符号つき境界和に等しい（Berger–Fresse §1.1.3）。
方針：全ての面の交代和を端点と内部へ分け、内部の頂点を角で添字づける。
規約：全境界の出力次数は p+q−1 である。
使われ方：各方向の寄与と混合角の相殺を全微分の等式へまとめる。 -/
lemma shuffleValue_d_decomposition (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (hN : 0 < p + q) (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌) :
    (normalizedChains A (m + n)).d (p + q) (p + q - 1) (shuffleValue A m n i p q x y) =
      (∑ s : ShufflePath p q, (s.sign : ℤ) • normalizedGenerator A (m + n) (p + q - 1)
        ((simplicial (m + n)).map (boundaryFaceMap (p + q) hN 0).op
          (shuffleSimplex m n i s x y))) +
      (∑ c : AdjacentCorner p q, adjacentBoundaryTerm A m n i hN x y c) +
      (∑ s : ShufflePath p q, (-1 : ℤ) ^ (p + q) • (s.sign : ℤ) •
        normalizedGenerator A (m + n) (p + q - 1)
          ((simplicial (m + n)).map (boundaryFaceMap (p + q) hN (Fin.last (p + q))).op
            (shuffleSimplex m n i s x y))) := by
  classical
  rw [shuffleValue_d A m n i p q hN x y, sum_adjacentBoundaryTerm_enumeration A m n i hN x y]
  simp_rw [sum_fin_first_interior_last (p + q) hN]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_last, Finset.sum_add_distrib]

end SerrePositivity.EInfinity.BarrattEccles
