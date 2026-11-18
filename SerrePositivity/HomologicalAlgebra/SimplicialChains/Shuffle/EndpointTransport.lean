module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.DegreeTransport
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.BoundaryFaces
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.HorizontalEndpointSum
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.VerticalEndpointSum
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleEndpointTransport

/-!
# 一般の単体集合の始端・終端の境界項の次数移送

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

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：水平始端の生成元の移送は全境界の最初の面である（Berger–Fresse §1.1.3）。
方針：最初の頂点を飛ばす面写像を次数の等式の前後で比較する。
規約：この等式は shuffle の符号を掛ける前の生成元について述べる。
使われ方：水平始端の境界和の次数を全境界に合わせる。 -/
lemma degreeTransport_horizontal_first (X Y : SSet.{0}) {p q : ℕ}
    (hN : 0 < p + 1 + q) (s : ShufflePath (p + 1) q)
    (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.degreeTransport A (X ⊗ Y) (by omega : p + q = p + 1 + q - 1)
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
          ((X ⊗ Y).map (horizontalFirstFaceMap p q).op
            (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p + 1) (q := q) s x y))) =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + 1 + q - 1)
        ((X ⊗ Y).map (boundaryFaceMap (p + 1 + q) hN 0).op
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p + 1) (q := q) s x y)) := by
  apply _root_.SerrePositivity.SimplicialChains.Shuffle.degreeTransport_generator_map
  intro k
  dsimp [horizontalFirstFaceMap, boundaryFaceMap]

/-- 概要：水平終端の生成元の移送は全境界の最後の面である（Berger–Fresse §1.1.3）。
方針：最後の辺 a の直後が最後の頂点であることから面写像を比較する。
規約：a は最後の辺を指定する。
使われ方：水平終端の境界和の次数を全境界に合わせる。 -/
lemma degreeTransport_horizontal_last (X Y : SSet.{0}) {p q : ℕ}
    (hN : 0 < p + 1 + q) (s : ShufflePath (p + 1) q)
    (a : Fin (p + 1 + q)) (hlast : a.val + 1 = p + 1 + q)
    (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.degreeTransport A (X ⊗ Y) (by omega : p + q = p + 1 + q - 1)
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
          ((X ⊗ Y).map (horizontalFaceMap p q a).op
            (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p + 1) (q := q) s x y))) =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + 1 + q - 1)
        ((X ⊗ Y).map (boundaryFaceMap (p + 1 + q) hN (Fin.last (p + 1 + q))).op
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p + 1) (q := q) s x y)) := by
  apply _root_.SerrePositivity.SimplicialChains.Shuffle.degreeTransport_generator_map
  intro k
  have ha : a.succ = Fin.last (p + 1 + q) := Fin.ext hlast
  dsimp [horizontalFaceMap, boundaryFaceMap]
  rw [ha]

/-- 概要：全境界の水平始端の和は方向別の始端の和の移送である（Berger–Fresse §1.1.3）。
方針：生成元の始端の移送を shuffle の符号と有限和へ拡張する。
規約：水平始端の経路は 0 が水平辺集合に属することで指定する。
使われ方：水平始端の計算を全境界へ代入する。 -/
lemma sum_horizontalFirstBoundary_transport (X Y : SSet.{0}) {p q : ℕ}
    (hN : 0 < p + 1 + q)
    (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    (∑ s : {s : ShufflePath (p + 1) q // 0 ∈ s.val},
      (s.val.sign : ℤ) • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + 1 + q - 1)
        ((X ⊗ Y).map (boundaryFaceMap (p + 1 + q) hN 0).op
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p + 1) (q := q) s.val x y))) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.degreeTransport A (X ⊗ Y) (by omega : p + q = p + 1 + q - 1)
        (_root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q (X.δ 0 x) y) := by
  classical
  rw [← _root_.SerrePositivity.SimplicialChains.Shuffle.sum_horizontal_first_face A X Y x y, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_zsmul, _root_.SerrePositivity.SimplicialChains.Shuffle.degreeTransport_horizontal_first A X Y hN s.val x y]

/-- 概要：全境界の水平終端の和は方向別の終端の和の移送である（Berger–Fresse §1.1.3）。
方針：終端の生成元の移送を二つの符号と有限和へ拡張する。
規約：第一の入力の最後の境界符号 (−1)^(p+1) を含む。
使われ方：水平終端の計算を全境界へ代入する。 -/
lemma sum_horizontalLastBoundary_transport (X Y : SSet.{0}) {p q : ℕ}
    (hN : 0 < p + 1 + q) (a : Fin (p + 1 + q)) (hlast : a.val + 1 = p + 1 + q)
    (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    (∑ s : {s : ShufflePath (p + 1) q // a ∈ s.val},
      (-1 : ℤ) ^ (p + 1 + q) • (s.val.sign : ℤ) •
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + 1 + q - 1)
          ((X ⊗ Y).map (boundaryFaceMap (p + 1 + q) hN (Fin.last (p + 1 + q))).op
            (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p + 1) (q := q) s.val x y))) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.degreeTransport A (X ⊗ Y) (by omega : p + q = p + 1 + q - 1)
        ((-1 : ℤ) ^ (p + 1) •
          _root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q (X.δ (Fin.last (p + 1)) x) y) := by
  classical
  rw [← _root_.SerrePositivity.SimplicialChains.Shuffle.sum_horizontal_last_face A X Y a hlast x y, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_zsmul, map_zsmul, _root_.SerrePositivity.SimplicialChains.Shuffle.degreeTransport_horizontal_last A X Y hN s.val a hlast x y]

/-- 概要：全境界の垂直始端の和は第二の入力の最初の面の shuffle である（Berger–Fresse §1.1.3）。
方針：垂直次数を後続次数とすると最初の面写像が定義上通常の δ 0 に一致する。
規約：Koszul 符号 (−1)^p を含む。
使われ方：垂直始端の計算を全境界へ代入する。 -/
lemma sum_verticalFirstBoundary (X Y : SSet.{0}) {p q : ℕ}
    (hN : 0 < p + (q + 1))
    (x : X _⦋p⦌) (y : Y _⦋q + 1⦌) :
    (∑ s : {s : ShufflePath p (q + 1) // 0 ∉ s.val},
      (s.val.sign : ℤ) • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + (q + 1) - 1)
        ((X ⊗ Y).map (boundaryFaceMap (p + (q + 1)) hN 0).op
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q + 1) s.val x y))) =
      (-1 : ℤ) ^ p • _root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q x (Y.δ 0 y) :=
  _root_.SerrePositivity.SimplicialChains.Shuffle.sum_vertical_first_face A X Y x y

/-- 概要：全境界の垂直終端の和は第二の入力の最後の面の shuffle である（Berger–Fresse §1.1.3）。
方針：最後の辺の直後が最後の頂点であることと方向別の終端の和の公式を使う。
規約：入力の境界符号と Koszul 符号の両方を含む。
使われ方：垂直終端の計算を全境界へ代入する。 -/
lemma sum_verticalLastBoundary (X Y : SSet.{0}) {p q : ℕ}
    (hN : 0 < p + (q + 1))
    (x : X _⦋p⦌) (y : Y _⦋q + 1⦌) :
    (∑ s : {s : ShufflePath p (q + 1) // Fin.last (p + q) ∉ s.val},
      (-1 : ℤ) ^ (p + (q + 1)) • (s.val.sign : ℤ) •
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + (q + 1) - 1)
          ((X ⊗ Y).map
            (boundaryFaceMap (p + (q + 1)) hN (Fin.last (p + (q + 1)))).op
            (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p) (q := q + 1) s.val x y))) =
      (-1 : ℤ) ^ p • (-1 : ℤ) ^ (q + 1) •
        _root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q x (Y.δ (Fin.last (q + 1)) y) :=
  _root_.SerrePositivity.SimplicialChains.Shuffle.sum_vertical_last_face A X Y x y

end SerrePositivity.SimplicialChains.Shuffle
