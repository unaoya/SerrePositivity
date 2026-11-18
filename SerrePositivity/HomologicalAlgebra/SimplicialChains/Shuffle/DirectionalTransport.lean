module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.DegreeTransport
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.BoundaryFaces
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCornerCoordinates
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.HorizontalSum
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.VerticalSum
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleDirectionalTransport

/-!
# 一般の単体集合の内部境界の方向別の和と次数の移送

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

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：全内部境界の垂直部分は辺の削除で計算した垂直角の和である（Berger–Fresse §1.1.3）。
方針：二種類の角の全単射を有限和に適用して、同じ頂点を飛ばす面写像を同定する。
規約：垂直次数を q+1 と書くと出力次数は p+q に簡約される。
使われ方：第二の入力の内部微分の計算を全境界へ接続する。 -/
lemma sum_verticalAdjacentBoundary (X Y : SSet.{0}) {p q : ℕ}
    (hN : 0 < p + (q + 1))
    (x : X _⦋p⦌) (y : Y _⦋q + 1⦌) :
    (∑ c : VerticalAdjacentCorner p (q + 1),
      _root_.SerrePositivity.SimplicialChains.Shuffle.adjacentBoundaryTerm A X Y hN x y ⟨c.val, c.property.1⟩) =
      ∑ c : VerticalCorner p q, _root_.SerrePositivity.SimplicialChains.Shuffle.verticalCornerTerm A X Y x y c := by
  classical
  rw [← (verticalAdjacentCornerEquiv p q).sum_comp]
  rfl

/-- 概要：全内部境界の水平部分は水平角の和の次数移送である（Berger–Fresse §1.1.3）。
方針：角の添字を移し、面写像の各頂点の一致を生成元の次数移送の補題へ渡す。
規約：p+q と (p+1+q)−1 の同定を線形写像で明示する。
使われ方：第一の入力の内部微分の計算を全境界へ接続する。 -/
lemma sum_horizontalAdjacentBoundary (X Y : SSet.{0}) {p q : ℕ}
    (hN : 0 < p + 1 + q)
    (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    (∑ c : HorizontalAdjacentCorner (p + 1) q,
      _root_.SerrePositivity.SimplicialChains.Shuffle.adjacentBoundaryTerm A X Y hN x y ⟨c.val, c.property.1⟩) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.degreeTransport A (X ⊗ Y) (by omega : p + q = p + 1 + q - 1)
        (∑ c : HorizontalCorner p q, _root_.SerrePositivity.SimplicialChains.Shuffle.horizontalCornerTerm A X Y x y c) := by
  classical
  rw [← (horizontalAdjacentCornerEquiv p q).sum_comp, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  let a := Fin.cast (by omega : p + q + 1 = p + 1 + q) c.val.2.castSucc
  let b := Fin.cast (by omega : p + q + 1 = p + 1 + q) c.val.2.succ
  have hgen := _root_.SerrePositivity.SimplicialChains.Shuffle.degreeTransport_generator_map A (X ⊗ Y) (p + 1 + q)
    (by omega : p + q = p + 1 + q - 1) (horizontalFaceMap p q a)
    (middleFaceMap (p + 1 + q) hN b) (by intro k; apply Fin.ext; rfl)
    (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p + 1) (q := q) c.val.1 x y)
  change (-1 : ℤ) ^ (c.val.2.val + 1) • (c.val.1.sign : ℤ) • _ =
    _root_.SerrePositivity.SimplicialChains.Shuffle.degreeTransport A (X ⊗ Y) (by omega)
      ((-1 : ℤ) ^ (c.val.2.val + 1) • (c.val.1.sign : ℤ) • _)
  rw [map_zsmul, map_zsmul, hgen]
  rfl

end SerrePositivity.SimplicialChains.Shuffle
