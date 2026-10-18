module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCornerPartition
public import Mathlib.Algebra.BigOperators.Fin

/-!
# shuffle の全境界と隣接する角

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

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：正次数の単体から一頂点を除く面写像（Berger–Fresse §1.1.2）。
方針：次数 N−1+1 を N と同定して succAbove を使う。
規約：最後の頂点の削除も含む Fin(N+1) の全頂点で添字づける。
使われ方：正次数を後続次数に書き直さずに境界の交代面和を表す。 -/
def boundaryFaceMap (N : ℕ) (hN : 0 < N) (b : Fin (N + 1)) : ⦋N - 1⦌ ⟶ ⦋N⦌ :=
  SimplexCategory.mkHom {
    toFun j := b.succAbove (Fin.cast (Nat.sub_add_cancel (by omega : 1 ≤ N)) j)
    monotone' := fun _ _ h => (Fin.strictMono_succAbove b).monotone h }

/-- 概要：内部の面写像は全ての面写像の族の制限である（Berger–Fresse §1.1.3）。
方針：両方の写像の定義が同じ succAbove を使うことを確認する。
規約：内部の頂点は b.castSucc として指定する。
使われ方：混合角の相殺を全境界の一部に適用する。 -/
lemma boundaryFaceMap_castSucc (N : ℕ) (hN : 0 < N) (b : Fin N) :
    boundaryFaceMap N hN b.castSucc = middleFaceMap N hN b := rfl

/-- 概要：正次数の生成元の微分を全ての面写像の交代和で表す（Berger–Fresse §1.1.2）。
方針：正次数を後続次数として既存の生成元の微分の公式を使う。
規約：出力の次数は N−1 である。
使われ方：shuffle の全境界の有限和を得る。 -/
lemma normalizedGenerator_d_pos (A : Type u) [CommRing A] (n N : ℕ) (hN : 0 < N)
    (x : (simplicial n) _⦋N⦌) :
    (normalizedChains A n).d N (N - 1) (normalizedGenerator A n N x) =
      ∑ b : Fin (N + 1), (-1 : ℤ) ^ b.val • normalizedGenerator A n (N - 1)
        ((simplicial n).map (boundaryFaceMap N hN b).op x) := by
  cases N with
  | zero => omega
  | succ r => exact normalizedGenerator_d A n r x

/-- 概要：小さい辺番号と隣接する二辺の角の全単射（Berger–Fresse §1.1.3）。
方針：辺番号 a に対して二辺 a と a+1 を取り、逆向きには最初の辺を読む。
規約：正次数 p+q の内部角は Fin(p+q−1) で添字づける。
使われ方：内部の境界面の二重和を角全体の和に直す。 -/
def adjacentCornerEquiv (p q : ℕ) (hN : 0 < p + q) :
    ShufflePath p q × Fin (p + q - 1) ≃ AdjacentCorner p q where
  toFun v := ⟨(v.1, (⟨v.2.val, by have h := v.2.isLt; omega⟩,
    ⟨v.2.val + 1, by have h := v.2.isLt; omega⟩)), rfl⟩
  invFun c := (c.val.1, ⟨c.val.2.1.val, by
    have h := c.val.2.2.isLt
    have hnext := c.property
    omega⟩)
  left_inv v := by
    apply Prod.ext
    · rfl
    · apply Fin.ext; rfl
  right_inv c := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Fin.ext; rfl
      · apply Fin.ext; exact c.property.symm

variable (A : Type u) [CommRing A]

/-- 概要：任意の隣接角の符号つき境界項（Berger–Fresse §1.1.3）。
方針：二辺の間の頂点を削除し、shuffle と境界の符号を掛ける。
規約：出力の次数は p+q−1 で統一する。
使われ方：内部の全境界の和を三種類の角へ分ける。 -/
def adjacentBoundaryTerm (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (hN : 0 < p + q) (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌)
    (c : AdjacentCorner p q) : (normalizedChains A (m + n)).X (p + q - 1) :=
  (-1 : ℤ) ^ c.val.2.2.val • (c.val.1.sign : ℤ) •
    normalizedGenerator A (m + n) (p + q - 1)
      ((simplicial (m + n)).map (middleFaceMap (p + q) hN c.val.2.2).op
        (shuffleSimplex m n i c.val.1 x y))

/-- 概要：内部境界の全角の和で混合角の寄与を消去する（Berger–Fresse §1.1.3）。
方針：三種類の角の全単射と既存の混合角の和の相殺を使う。
規約：同方向の角の二つの和だけが残る。
使われ方：全境界の内部部分を二つの入力の微分に帰着する。 -/
lemma sum_adjacentBoundaryTerm (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (hN : 0 < p + q) (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌) :
    ∑ c : AdjacentCorner p q, adjacentBoundaryTerm A m n i hN x y c =
      (∑ c : HorizontalAdjacentCorner p q,
        adjacentBoundaryTerm A m n i hN x y ⟨c.val, c.property.1⟩) +
      (∑ c : VerticalAdjacentCorner p q,
        adjacentBoundaryTerm A m n i hN x y ⟨c.val, c.property.1⟩) := by
  rw [sum_adjacentCorner_partition]
  have hm : (∑ c : MixedCorner p q,
      adjacentBoundaryTerm A m n i hN x y ⟨c.val, c.property.1⟩) = 0 :=
    sum_mixedBoundary_eq_zero A m n i p q hN x y
  rw [hm, add_zero]

/-- 概要：shuffle の微分は全ての経路・面の符号つき和である（Berger–Fresse §1.1.3）。
方針：shuffle の有限和を微分の線形性で展開し、生成元の微分の交代面和を使う。
規約：正次数 p+q の境界を p+q−1 次で計算する。
使われ方：全境界を始端・内部・終端に分ける出発点となる。 -/
lemma shuffleValue_d (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ) (hN : 0 < p + q)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌) :
    (normalizedChains A (m + n)).d (p + q) (p + q - 1) (shuffleValue A m n i p q x y) =
      ∑ s : ShufflePath p q, ∑ b : Fin (p + q + 1),
        (-1 : ℤ) ^ b.val • (s.sign : ℤ) • normalizedGenerator A (m + n) (p + q - 1)
          ((simplicial (m + n)).map (boundaryFaceMap (p + q) hN b).op
            (shuffleSimplex m n i s x y)) := by
  classical
  simp only [shuffleValue, map_sum, map_zsmul, normalizedGenerator_d_pos A (m + n) (p + q) hN,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro b _
  exact smul_comm _ _ _

end SerrePositivity.EInfinity.BarrattEccles
