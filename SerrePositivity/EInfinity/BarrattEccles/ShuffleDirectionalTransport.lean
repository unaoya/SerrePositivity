module

public import SerrePositivity.EInfinity.BarrattEccles.NormalizedDegreeTransport
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleBoundaryFaces
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCornerCoordinates
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalSum
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleVerticalSum

/-!
# 内部境界の方向別の和と次数の移送

概要：Berger–Fresse §1.1.3 の全内部境界の分割を、方向別に計算した内部面の和へ接続する。
方針：隣接角の添字の全単射と、正規化生成元の次数移送の両立性を使う。
規約：全境界の次数 N−1 と方向別の p+q 次数を等式で同定する。
使われ方：水平・垂直の微分項の計算を全境界の分割へ代入する。
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

/-- 概要：全内部境界の垂直部分は辺の削除で計算した垂直角の和である（Berger–Fresse §1.1.3）。
方針：二種類の角の全単射を有限和に適用して、同じ頂点を飛ばす面写像を同定する。
規約：垂直次数を q+1 と書くと出力次数は p+q に簡約される。
使われ方：第二の入力の内部微分の計算を全境界へ接続する。 -/
lemma sum_verticalAdjacentBoundary (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (hN : 0 < p + (q + 1))
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q + 1⦌) :
    (∑ c : VerticalAdjacentCorner p (q + 1),
      adjacentBoundaryTerm A m n i hN x y ⟨c.val, c.property.1⟩) =
      ∑ c : VerticalCorner p q, verticalCornerTerm A m n i x y c := by
  classical
  rw [← (verticalAdjacentCornerEquiv p q).sum_comp]
  rfl

/-- 概要：全内部境界の水平部分は水平角の和の次数移送である（Berger–Fresse §1.1.3）。
方針：角の添字を移し、面写像の各頂点の一致を生成元の次数移送の補題へ渡す。
規約：p+q と (p+1+q)−1 の同定を線形写像で明示する。
使われ方：第一の入力の内部微分の計算を全境界へ接続する。 -/
lemma sum_horizontalAdjacentBoundary (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (hN : 0 < p + 1 + q)
    (x : (simplicial (m + 1)) _⦋p + 1⦌) (y : (simplicial n) _⦋q⦌) :
    (∑ c : HorizontalAdjacentCorner (p + 1) q,
      adjacentBoundaryTerm A m n i hN x y ⟨c.val, c.property.1⟩) =
      degreeTransport A (m + n) (by omega : p + q = p + 1 + q - 1)
        (∑ c : HorizontalCorner p q, horizontalCornerTerm A m n i x y c) := by
  classical
  rw [← (horizontalAdjacentCornerEquiv p q).sum_comp, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  let a := Fin.cast (by omega : p + q + 1 = p + 1 + q) c.val.2.castSucc
  let b := Fin.cast (by omega : p + q + 1 = p + 1 + q) c.val.2.succ
  have hgen := degreeTransport_generator_map A (m + n) (p + 1 + q)
    (by omega : p + q = p + 1 + q - 1) (horizontalFaceMap p q a)
    (middleFaceMap (p + 1 + q) hN b) (by intro k; apply Fin.ext; rfl)
    (shuffleSimplex m n i (p := p + 1) (q := q) c.val.1 x y)
  change (-1 : ℤ) ^ (c.val.2.val + 1) • (c.val.1.sign : ℤ) • _ =
    degreeTransport A (m + n) (by omega)
      ((-1 : ℤ) ^ (c.val.2.val + 1) • (c.val.1.sign : ℤ) • _)
  rw [map_zsmul, map_zsmul, hgen]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
