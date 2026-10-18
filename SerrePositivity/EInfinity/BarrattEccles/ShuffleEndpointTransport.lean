module

public import SerrePositivity.EInfinity.BarrattEccles.NormalizedDegreeTransport
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleBoundaryFaces
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalEndpointSum
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleVerticalEndpointSum

/-!
# 始端・終端の境界項の次数移送

概要：Berger–Fresse §1.1.3 の全境界の端点を方向別の端点の公式へ接続する。
方針：同じ頂点を飛ばす二つの面写像を比較し、正規化生成元の次数移送を使う。
規約：全境界の出力次数 N−1 と小さい shuffle の次数 p+q を同定する。
使われ方：水平・垂直の寄与をまとめた微分の計算で端点の項を処理する。
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

/-- 概要：水平始端の生成元の移送は全境界の最初の面である（Berger–Fresse §1.1.3）。
方針：最初の頂点を飛ばす面写像を次数の等式の前後で比較する。
規約：この等式は shuffle の符号を掛ける前の生成元について述べる。
使われ方：水平始端の境界和の次数を全境界に合わせる。 -/
lemma degreeTransport_horizontal_first (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (hN : 0 < p + 1 + q) (s : ShufflePath (p + 1) q)
    (x : (simplicial (m + 1)) _⦋p + 1⦌) (y : (simplicial n) _⦋q⦌) :
    degreeTransport A (m + n) (by omega : p + q = p + 1 + q - 1)
        (normalizedGenerator A (m + n) (p + q)
          ((simplicial (m + n)).map (horizontalFirstFaceMap p q).op
            (shuffleSimplex m n i (p := p + 1) (q := q) s x y))) =
      normalizedGenerator A (m + n) (p + 1 + q - 1)
        ((simplicial (m + n)).map (boundaryFaceMap (p + 1 + q) hN 0).op
          (shuffleSimplex m n i (p := p + 1) (q := q) s x y)) := by
  apply degreeTransport_generator_map
  intro k
  dsimp [horizontalFirstFaceMap, boundaryFaceMap]

/-- 概要：水平終端の生成元の移送は全境界の最後の面である（Berger–Fresse §1.1.3）。
方針：最後の辺 a の直後が最後の頂点であることから面写像を比較する。
規約：a は最後の辺を指定する。
使われ方：水平終端の境界和の次数を全境界に合わせる。 -/
lemma degreeTransport_horizontal_last (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (hN : 0 < p + 1 + q) (s : ShufflePath (p + 1) q)
    (a : Fin (p + 1 + q)) (hlast : a.val + 1 = p + 1 + q)
    (x : (simplicial (m + 1)) _⦋p + 1⦌) (y : (simplicial n) _⦋q⦌) :
    degreeTransport A (m + n) (by omega : p + q = p + 1 + q - 1)
        (normalizedGenerator A (m + n) (p + q)
          ((simplicial (m + n)).map (horizontalFaceMap p q a).op
            (shuffleSimplex m n i (p := p + 1) (q := q) s x y))) =
      normalizedGenerator A (m + n) (p + 1 + q - 1)
        ((simplicial (m + n)).map (boundaryFaceMap (p + 1 + q) hN (Fin.last (p + 1 + q))).op
          (shuffleSimplex m n i (p := p + 1) (q := q) s x y)) := by
  apply degreeTransport_generator_map
  intro k
  have ha : a.succ = Fin.last (p + 1 + q) := Fin.ext hlast
  dsimp [horizontalFaceMap, boundaryFaceMap]
  rw [ha]

/-- 概要：全境界の水平始端の和は方向別の始端の和の移送である（Berger–Fresse §1.1.3）。
方針：生成元の始端の移送を shuffle の符号と有限和へ拡張する。
規約：水平始端の経路は 0 が水平辺集合に属することで指定する。
使われ方：水平始端の計算を全境界へ代入する。 -/
lemma sum_horizontalFirstBoundary_transport (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (hN : 0 < p + 1 + q)
    (x : (simplicial (m + 1)) _⦋p + 1⦌) (y : (simplicial n) _⦋q⦌) :
    (∑ s : {s : ShufflePath (p + 1) q // 0 ∈ s.val},
      (s.val.sign : ℤ) • normalizedGenerator A (m + n) (p + 1 + q - 1)
        ((simplicial (m + n)).map (boundaryFaceMap (p + 1 + q) hN 0).op
          (shuffleSimplex m n i (p := p + 1) (q := q) s.val x y))) =
      degreeTransport A (m + n) (by omega : p + q = p + 1 + q - 1)
        (shuffleValue A m n i p q ((simplicial (m + 1)).δ 0 x) y) := by
  classical
  rw [← sum_horizontal_first_face A m n i x y, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_zsmul, degreeTransport_horizontal_first A m n i hN s.val x y]

/-- 概要：全境界の水平終端の和は方向別の終端の和の移送である（Berger–Fresse §1.1.3）。
方針：終端の生成元の移送を二つの符号と有限和へ拡張する。
規約：第一の入力の最後の境界符号 (−1)^(p+1) を含む。
使われ方：水平終端の計算を全境界へ代入する。 -/
lemma sum_horizontalLastBoundary_transport (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (hN : 0 < p + 1 + q) (a : Fin (p + 1 + q)) (hlast : a.val + 1 = p + 1 + q)
    (x : (simplicial (m + 1)) _⦋p + 1⦌) (y : (simplicial n) _⦋q⦌) :
    (∑ s : {s : ShufflePath (p + 1) q // a ∈ s.val},
      (-1 : ℤ) ^ (p + 1 + q) • (s.val.sign : ℤ) •
        normalizedGenerator A (m + n) (p + 1 + q - 1)
          ((simplicial (m + n)).map (boundaryFaceMap (p + 1 + q) hN (Fin.last (p + 1 + q))).op
            (shuffleSimplex m n i (p := p + 1) (q := q) s.val x y))) =
      degreeTransport A (m + n) (by omega : p + q = p + 1 + q - 1)
        ((-1 : ℤ) ^ (p + 1) •
          shuffleValue A m n i p q ((simplicial (m + 1)).δ (Fin.last (p + 1)) x) y) := by
  classical
  rw [← sum_horizontal_last_face A m n i a hlast x y, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_zsmul, map_zsmul, degreeTransport_horizontal_last A m n i hN s.val a hlast x y]

/-- 概要：全境界の垂直始端の和は第二の入力の最初の面の shuffle である（Berger–Fresse §1.1.3）。
方針：垂直次数を後続次数とすると最初の面写像が定義上通常の δ 0 に一致する。
規約：Koszul 符号 (−1)^p を含む。
使われ方：垂直始端の計算を全境界へ代入する。 -/
lemma sum_verticalFirstBoundary (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (hN : 0 < p + (q + 1))
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q + 1⦌) :
    (∑ s : {s : ShufflePath p (q + 1) // 0 ∉ s.val},
      (s.val.sign : ℤ) • normalizedGenerator A (m + n) (p + (q + 1) - 1)
        ((simplicial (m + n)).map (boundaryFaceMap (p + (q + 1)) hN 0).op
          (shuffleSimplex m n i (p := p) (q := q + 1) s.val x y))) =
      (-1 : ℤ) ^ p • shuffleValue A m n i p q x ((simplicial n).δ 0 y) :=
  sum_vertical_first_face A m n i x y

/-- 概要：全境界の垂直終端の和は第二の入力の最後の面の shuffle である（Berger–Fresse §1.1.3）。
方針：最後の辺の直後が最後の頂点であることと方向別の終端の和の公式を使う。
規約：入力の境界符号と Koszul 符号の両方を含む。
使われ方：垂直終端の計算を全境界へ代入する。 -/
lemma sum_verticalLastBoundary (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (hN : 0 < p + (q + 1))
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q + 1⦌) :
    (∑ s : {s : ShufflePath p (q + 1) // Fin.last (p + q) ∉ s.val},
      (-1 : ℤ) ^ (p + (q + 1)) • (s.val.sign : ℤ) •
        normalizedGenerator A (m + n) (p + (q + 1) - 1)
          ((simplicial (m + n)).map
            (boundaryFaceMap (p + (q + 1)) hN (Fin.last (p + (q + 1)))).op
            (shuffleSimplex m n i (p := p) (q := q + 1) s.val x y))) =
      (-1 : ℤ) ^ p • (-1 : ℤ) ^ (q + 1) •
        shuffleValue A m n i p q x ((simplicial n).δ (Fin.last (q + 1)) y) :=
  sum_vertical_last_face A m n i x y

end SerrePositivity.EInfinity.BarrattEccles
