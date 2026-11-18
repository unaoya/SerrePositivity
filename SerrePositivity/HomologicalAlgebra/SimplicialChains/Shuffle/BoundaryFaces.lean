module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.MixedBoundary
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.BoundaryCuts
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCornerPartition
public import Mathlib.Algebra.BigOperators.Fin
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleBoundaryFaces

/-!
# 一般の単体集合のshuffle の全境界と隣接する角

概要：Berger–Fresse §1.1.3 の shuffle の境界を正次数で一様に記述する。
方針：次数 N−1 の面写像を構成し、内部の頂点を隣接する辺の角で添字づける。
規約：始端・終端は全境界の一部であり、内部の面の番号は辺の番号に一つ加えた値。
使われ方：全境界を水平・垂直の寄与および相殺する混合角へ分割する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial

/-- 概要：正次数の生成元の微分を全ての面写像の交代和で表す（Berger–Fresse §1.1.2）。
方針：正次数を後続次数として既存の生成元の微分の公式を使う。
規約：出力の次数は N−1 である。
使われ方：shuffle の全境界の有限和を得る。 -/
lemma normalizedGenerator_d_pos (A : Type u) [CommRing A] (X : SSet.{0}) (N : ℕ) (hN : 0 < N)
    (x : X _⦋N⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d N (N - 1) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X N x) =
      ∑ b : Fin (N + 1), (-1 : ℤ) ^ b.val • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X (N - 1)
        (X.map (boundaryFaceMap N hN b).op x) := by
  cases N with
  | zero => omega
  | succ r => exact _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_d A X r x

variable (A : Type u) [CommRing A]

/-- 概要：任意の隣接角の符号つき境界項（Berger–Fresse §1.1.3）。
方針：二辺の間の頂点を削除し、shuffle と境界の符号を掛ける。
規約：出力の次数は p+q−1 で統一する。
使われ方：内部の全境界の和を三種類の角へ分ける。 -/
def adjacentBoundaryTerm (X Y : SSet.{0}) {p q : ℕ}
    (hN : 0 < p + q) (x : X _⦋p⦌) (y : Y _⦋q⦌)
    (c : AdjacentCorner p q) : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).X (p + q - 1) :=
  (-1 : ℤ) ^ c.val.2.2.val • (c.val.1.sign : ℤ) •
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q - 1)
      ((X ⊗ Y).map (middleFaceMap (p + q) hN c.val.2.2).op
        (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y c.val.1 x y))

/-- 概要：内部境界の全角の和で混合角の寄与を消去する（Berger–Fresse §1.1.3）。
方針：三種類の角の全単射と既存の混合角の和の相殺を使う。
規約：同方向の角の二つの和だけが残る。
使われ方：全境界の内部部分を二つの入力の微分に帰着する。 -/
lemma sum_adjacentBoundaryTerm (X Y : SSet.{0}) {p q : ℕ}
    (hN : 0 < p + q) (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    ∑ c : AdjacentCorner p q, _root_.SerrePositivity.SimplicialChains.Shuffle.adjacentBoundaryTerm A X Y hN x y c =
      (∑ c : HorizontalAdjacentCorner p q,
        _root_.SerrePositivity.SimplicialChains.Shuffle.adjacentBoundaryTerm A X Y hN x y ⟨c.val, c.property.1⟩) +
      (∑ c : VerticalAdjacentCorner p q,
        _root_.SerrePositivity.SimplicialChains.Shuffle.adjacentBoundaryTerm A X Y hN x y ⟨c.val, c.property.1⟩) := by
  rw [sum_adjacentCorner_partition]
  have hm : (∑ c : MixedCorner p q,
      _root_.SerrePositivity.SimplicialChains.Shuffle.adjacentBoundaryTerm A X Y hN x y ⟨c.val, c.property.1⟩) = 0 :=
    _root_.SerrePositivity.SimplicialChains.Shuffle.sum_mixedBoundary_eq_zero A X Y p q hN x y
  rw [hm, add_zero]

/-- 概要：shuffle の微分は全ての経路・面の符号つき和である（Berger–Fresse §1.1.3）。
方針：shuffle の有限和を微分の線形性で展開し、生成元の微分の交代面和を使う。
規約：正次数 p+q の境界を p+q−1 次で計算する。
使われ方：全境界を始端・内部・終端に分ける出発点となる。 -/
lemma shuffleValue_d (X Y : SSet.{0}) (p q : ℕ) (hN : 0 < p + q)
    (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)).d (p + q) (p + q - 1) (_root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q x y) =
      ∑ s : ShufflePath p q, ∑ b : Fin (p + q + 1),
        (-1 : ℤ) ^ b.val • (s.sign : ℤ) • _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q - 1)
          ((X ⊗ Y).map (boundaryFaceMap (p + q) hN b).op
            (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y)) := by
  classical
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.value, map_sum, map_zsmul, _root_.SerrePositivity.SimplicialChains.Shuffle.normalizedGenerator_d_pos A (X ⊗ Y) (p + q) hN,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro b _
  exact smul_comm _ _ _

end SerrePositivity.SimplicialChains.Shuffle
