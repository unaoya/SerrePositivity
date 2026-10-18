module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleVerticalSum
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleVerticalEndpointSum
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleDegenerate
public import Mathlib.Algebra.BigOperators.Fin

/-!
# shuffle 境界の垂直方向の全寄与

概要：Berger–Fresse §1.1.3 の垂直な内部面と垂直始端・終端の和を第二の入力の微分へまとめる。
方針：各有限和の添字替えを合成し、交代面和としての正規化鎖の微分を使う。
規約：第二の入力の微分に水平次数 p による Koszul 符号を付ける。
使われ方：shuffle の Leibniz 則の第二の項を与える。
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

/-- 概要：内部の垂直面の和を入力の内部面の shuffle の和で表す（Berger–Fresse §1.1.3）。
方針：小さい経路と面番号の二重和の順序を交換して shuffleValue にまとめる。
規約：内部面の番号は j+1 であり、始端・終端を含まない。
使われ方：第二の入力の全境界和との比較を行う。 -/
lemma sum_verticalCornerTerm_shuffleValue (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q + 1⦌) :
    ∑ c : VerticalCorner p q, verticalCornerTerm A m n i x y c =
      (-1 : ℤ) ^ p • ∑ j : Fin q, (-1 : ℤ) ^ (j.val + 1) •
        shuffleValue A m n i p q x ((simplicial n).δ j.succ.castSucc y) := by
  classical
  rw [sum_verticalCornerTerm A m n i x y, Finset.sum_comm]
  simp only [shuffleValue, Finset.smul_sum]

/-- 概要：第二の生成元の微分へ shuffle 双線形写像を適用した交代面和（Berger–Fresse §1.1.3）。
方針：正規化生成元の微分の公式に線形性と生成元上の shuffle 公式を使う。
規約：この等式には外側の Koszul 符号をまだ掛けない。
使われ方：垂直面の和を第二の入力の微分の項に直す。 -/
lemma shuffleBilinear_d_right_generators (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q + 1⦌) :
    shuffleBilinear A m n i p q (normalizedGenerator A (m + 1) p x)
        ((normalizedChains A n).d (q + 1) q (normalizedGenerator A n (q + 1) y)) =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
        shuffleValue A m n i p q x ((simplicial n).δ k y) := by
  rw [normalizedGenerator_d A n q y]
  simp only [map_sum, map_zsmul, shuffleBilinear_generators]

/-- 概要：shuffle 境界の垂直な内部面と垂直始端・終端の合計（Berger–Fresse §1.1.3）。
方針：大きい経路の各面を角・始端・終端で添字づけて符号つきで加える。
規約：全ての項は (p+q) 次の正規化鎖に属する。
使われ方：Leibniz 則の第二の入力の微分に対応する寄与を定義する。 -/
def verticalBoundaryContribution (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q + 1⦌) :
    (normalizedChains A (m + n)).X (p + q) :=
  (∑ s : {s : ShufflePath p (q + 1) // 0 ∉ s.val},
    (s.val.sign : ℤ) • normalizedGenerator A (m + n) (p + q)
      ((simplicial (m + n)).δ 0
        (shuffleSimplex m n i (p := p) (q := q + 1) s.val x y))) +
  (∑ c : VerticalCorner p q, verticalCornerTerm A m n i x y c) +
  (∑ s : {s : ShufflePath p (q + 1) // Fin.last (p + q) ∉ s.val},
    (-1 : ℤ) ^ (p + (q + 1)) • (s.val.sign : ℤ) •
      normalizedGenerator A (m + n) (p + q)
        ((simplicial (m + n)).δ (Fin.last (p + q)).succ
          (shuffleSimplex m n i (p := p) (q := q + 1) s.val x y)))

/-- 概要：垂直境界の全寄与は Koszul 符号を掛けた第二の入力の微分である（Berger–Fresse §1.1.3）。
方針：始端・内部・終端の和を添字替えして、入力の交代面和を復元する。
規約：微分は正規化鎖のホモロジー次数を一つ下げる。
使われ方：shuffle の Leibniz 則の第二の項の計算を完了する。 -/
lemma verticalBoundaryContribution_eq (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q + 1⦌) :
    verticalBoundaryContribution A m n i x y =
      (-1 : ℤ) ^ p • shuffleBilinear A m n i p q (normalizedGenerator A (m + 1) p x)
        ((normalizedChains A n).d (q + 1) q (normalizedGenerator A n (q + 1) y)) := by
  classical
  rw [verticalBoundaryContribution, sum_vertical_first_face A m n i x y,
    sum_verticalCornerTerm_shuffleValue A m n i x y, sum_vertical_last_face A m n i x y,
    ← smul_add, ← smul_add, shuffleBilinear_d_right_generators A m n i x y]
  congr 1
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, Fin.val_castSucc,
    Fin.val_last, Fin.succ_castSucc, Fin.succ_last, add_assoc]

end SerrePositivity.EInfinity.BarrattEccles
