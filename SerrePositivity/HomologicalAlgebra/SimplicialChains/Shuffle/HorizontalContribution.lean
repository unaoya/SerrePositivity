module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.HorizontalSum
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.HorizontalEndpointSum
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleDegenerate
public import Mathlib.Algebra.BigOperators.Fin
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalContribution
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.Components
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.BoundaryFaces

/-!
# 一般の単体集合のshuffle 境界の水平方向の全寄与

概要：Berger–Fresse §1.1.3 の水平な内部面と水平始端・終端の和を第一の入力の微分へまとめる。
方針：各有限和の添字替えを合成し、交代面和としての正規化鎖の微分を使う。
規約：第一の入力の微分には追加の Koszul 符号を付けない。
使われ方：shuffle の Leibniz 則の第一の項を与える。
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

/-- 概要：内部の水平面の和を入力の内部面の shuffle の和で表す（Berger–Fresse §1.1.3）。
方針：小さい経路と面番号の二重和の順序を交換して value にまとめる。
規約：内部面の番号は j+1 であり、始端・終端を含まない。
使われ方：第一の入力の全境界和との比較を行う。 -/
lemma sum_horizontalCornerTerm_shuffleValue (X Y : SSet.{0}) {p q : ℕ}
    (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    ∑ c : HorizontalCorner p q, _root_.SerrePositivity.SimplicialChains.Shuffle.horizontalCornerTerm A X Y x y c =
      ∑ j : Fin p, (-1 : ℤ) ^ (j.val + 1) •
        _root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q (X.δ j.succ.castSucc x) y := by
  classical
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.sum_horizontalCornerTerm A X Y x y, Finset.sum_comm]
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.value, Finset.smul_sum]

/-- 概要：第一の生成元の微分へ shuffle 双線形写像を適用した交代面和（Berger–Fresse §1.1.3）。
方針：正規化生成元の微分の公式に線形性と生成元上の shuffle 公式を使う。
規約：第一の入力の微分の各面に通常の交代符号を付ける。
使われ方：水平面の和を第一の入力の微分の項に直す。 -/
lemma shuffleBilinear_d_left_generators (X Y : SSet.{0}) {p q : ℕ}
    (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y p q
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + 1) p (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X (p + 1) x))
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Y q y) =
      ∑ k : Fin (p + 2), (-1 : ℤ) ^ k.val •
        _root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q (X.δ k x) y := by
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_d A X p x]
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear_generators]

/-- 概要：shuffle 境界の水平な内部面と水平始端・終端の合計（Berger–Fresse §1.1.3）。
方針：大きい経路の各面を角・始端・終端で添字づけて符号つきで加える。
規約：全ての項は (p+q) 次の正規化鎖に属する。
使われ方：Leibniz 則の第一の入力の微分に対応する寄与を定義する。 -/
def horizontalBoundaryContribution (X Y : SSet.{0}) {p q : ℕ}
    (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X (p + q) :=
  (∑ s : {s : ShufflePath (p + 1) q // 0 ∈ s.val},
    (s.val.sign : ℤ) • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
      ((X ⊗ Y).map (horizontalFirstFaceMap p q).op
        (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p + 1) (q := q) s.val x y))) +
  (∑ c : HorizontalCorner p q, _root_.SerrePositivity.SimplicialChains.Shuffle.horizontalCornerTerm A X Y x y c) +
  (∑ s : {s : ShufflePath (p + 1) q // (⟨p + q, by omega⟩ : Fin (p + 1 + q)) ∈ s.val},
    (-1 : ℤ) ^ (p + 1 + q) • (s.val.sign : ℤ) •
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q)
        ((X ⊗ Y).map (horizontalFaceMap p q ⟨p + q, by omega⟩).op
          (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y (p := p + 1) (q := q) s.val x y)))

/-- 概要：水平境界の全寄与は第一の入力の微分である（Berger–Fresse §1.1.3）。
方針：始端・内部・終端の和を添字替えして、入力の交代面和を復元する。
規約：微分は正規化鎖のホモロジー次数を一つ下げる。
使われ方：shuffle の Leibniz 則の第一の項の計算を完了する。 -/
lemma horizontalBoundaryContribution_eq (X Y : SSet.{0}) {p q : ℕ}
    (x : X _⦋p + 1⦌) (y : Y _⦋q⦌) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.horizontalBoundaryContribution A X Y x y =
      _root_.SerrePositivity.SimplicialChains.Shuffle.bilinear A X Y p q
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + 1) p (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X (p + 1) x))
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A Y q y) := by
  classical
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.horizontalBoundaryContribution, _root_.SerrePositivity.SimplicialChains.Shuffle.sum_horizontal_first_face A X Y x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_horizontalCornerTerm_shuffleValue A X Y x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_horizontal_last_face A X Y ⟨p + q, by omega⟩ (by dsimp; omega) x y,
    _root_.SerrePositivity.SimplicialChains.Shuffle.shuffleBilinear_d_left_generators A X Y x y]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, Fin.val_castSucc,
    Fin.val_last, Fin.succ_castSucc, Fin.succ_last, add_assoc]

end SerrePositivity.SimplicialChains.Shuffle
