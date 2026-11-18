module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.BoundaryDecomposition
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.DirectionalTransport
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.EndpointTransport
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.HorizontalContribution
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.VerticalContribution
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLeibnizPositive

/-!
# 一般の単体集合の正次数の二入力に対する shuffle の Leibniz 則

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

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：正次数の shuffle の全微分は水平・垂直の二つの寄与に等しい（Berger–Fresse §1.1.3）。
方針：始端と終端を辺の向きで分け、内部の角の三分割から混合角を消去する。
規約：両入力の次数は p+1 と q+1 である。
使われ方：方向別に証明した微分項を全境界の等式へ代入する。 -/
lemma shuffleValue_d_positive_contributions (X Y : SSet.{0}) (p q : ℕ)
    (x : X _⦋p + 1⦌) (y : Y _⦋q + 1⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (p + 1 + (q + 1)) (p + 1 + q)
        (_root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y (p + 1) (q + 1) x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.degreeTransport A (X ⊗ Y) (by omega : p + (q + 1) = p + 1 + q)
        (_root_.SerrePositivity.SimplicialChains.Shuffle.horizontalBoundaryContribution A X Y x y) +
      _root_.SerrePositivity.SimplicialChains.Shuffle.verticalBoundaryContribution A X Y x y := by
  classical
  have hN : 0 < p + 1 + (q + 1) := by omega
  erw [_root_.SerrePositivity.SimplicialChains.Shuffle.shuffleValue_d_decomposition A X Y (p + 1) (q + 1) hN x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_adjacentBoundaryTerm A X Y hN x y]
  let first := fun s : ShufflePath (p + 1) (q + 1) =>
    (s.sign : ℤ) • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + 1 + (q + 1) - 1)
      ((X ⊗ Y).map (boundaryFaceMap (p + 1 + (q + 1)) hN 0).op
        (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y))
  let last := fun s : ShufflePath (p + 1) (q + 1) =>
    (-1 : ℤ) ^ (p + 1 + (q + 1)) • (s.sign : ℤ) •
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + 1 + (q + 1) - 1)
        ((X ⊗ Y).map
          (boundaryFaceMap (p + 1 + (q + 1)) hN (Fin.last (p + 1 + (q + 1)))).op
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y))
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun s : ShufflePath (p + 1) (q + 1) => 0 ∈ s.val) first,
    ← Fintype.sum_subtype_add_sum_subtype
      (fun s : ShufflePath (p + 1) (q + 1) => Fin.last (p + 1 + q) ∈ s.val) last]
  dsimp only [first, last]
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.sum_horizontalFirstBoundary_transport A X Y hN x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_verticalFirstBoundary A X Y hN x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_horizontalAdjacentBoundary A X Y hN x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_verticalAdjacentBoundary A X Y hN x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_horizontalLastBoundary_transport A X Y hN (Fin.last (p + 1 + q))
      (by simp only [Fin.val_last]; omega) x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_verticalLastBoundary A X Y hN x y]
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.horizontalBoundaryContribution, _root_.SerrePositivity.SimplicialChains.Shuffle.verticalBoundaryContribution,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_horizontal_first_face A X Y x y, _root_.SerrePositivity.SimplicialChains.Shuffle.sum_horizontal_last_face A X Y
      ⟨p + (q + 1), by omega⟩ (by dsimp; omega) x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_vertical_first_face A X Y x y, _root_.SerrePositivity.SimplicialChains.Shuffle.sum_vertical_last_face A X Y x y]
  simp only [map_add]
  have regroup (a b c d e f : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X (p + 1 + q)) :
      (a + b) + (c + d) + (e + f) = ((a + c) + e) + ((b + d) + f) := by abel
  exact regroup _ _ _ _ _ _

/-- 概要：正次数の二入力の生成元について shuffle は Leibniz 則を満たす（Berger–Fresse §1.1.3）。
方針：全微分の二つの寄与を、既存の方向別の微分項の等式で置き換える。
規約：第二の入力の微分に (−1)^(p+1) を付ける。
使われ方：双線形性によって任意の正規化鎖へ微分の両立性を拡張する。 -/
lemma shuffleValue_d_positive (X Y : SSet.{0}) (p q : ℕ)
    (x : X _⦋p + 1⦌) (y : Y _⦋q + 1⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (p + 1 + (q + 1)) (p + 1 + q)
        (_root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y (p + 1) (q + 1) x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.degreeTransport A (X ⊗ Y) (by omega : p + (q + 1) = p + 1 + q)
        (_root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y p (q + 1)
          ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + 1) p
            (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X (p + 1) x))
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Y (q + 1) y)) +
      (-1 : ℤ) ^ (p + 1) • _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y (p + 1) q
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X (p + 1) x)
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).d (q + 1) q (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Y (q + 1) y)) := by
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.shuffleValue_d_positive_contributions A X Y p q x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.horizontalBoundaryContribution_eq A X Y x y, _root_.SerrePositivity.SimplicialChains.Shuffle.verticalBoundaryContribution_eq A X Y x y]

end SerrePositivity.SimplicialChains.Shuffle
