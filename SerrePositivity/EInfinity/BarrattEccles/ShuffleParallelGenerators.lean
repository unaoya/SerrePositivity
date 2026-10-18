module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleParallelSimplex
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleDegenerate

/-!
# 正規化生成元上の shuffle の並列結合則

概要：Berger–Fresse §1.1.3 の異なる入力への二段の shuffle 和を生成元上で比較する。
方針：並列の添字の全単射と符号および合成単体の一致を使う。
規約：交換する入力の次数 q,r に Koszul 符号 (−1)^(qr) を付ける。
使われ方：任意の正規化鎖と複体の射の並列結合則へ拡張する。
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

/-- 概要：並列合成の対応する正規化生成元は移送後に一致する（Berger–Fresse §1.1.3）。
方針：shuffle 単体の並列結合則と正規化の自然性を使う。
規約：中間の arity の移送も単体に含める。
使われ方：並列結合則の二重有限和の各項を比較する。 -/
lemma shuffleParallel_generator (m n k : ℕ) (i j : Fin (m + 2)) (hji : j ≠ i)
    (p q r : ℕ) (v : ShufflePath (p + q) r × ShufflePath p q)
    (x : (simplicial (m + 2)) _⦋p⦌) (y : (simplicial n) _⦋q⦌)
    (z : (simplicial k) _⦋r⦌) :
    degreeTransport A (m + k + n) (by omega : p + q + r = p + r + q)
        ((normalizedChainMap A (simplicialArityMap (by omega : m + n + k = m + k + n))).f
          (p + q + r) (normalizedGenerator A (m + n + k) (p + q + r)
            (shuffleSimplex (m + n) k (parallelSlot m n i j hji) v.1
              ((simplicialArityMap (by omega : m + 1 + n = m + n + 1)).app _
                (shuffleSimplex (m + 1) n i v.2 x y)) z))) =
      normalizedGenerator A (m + k + n) (p + r + q)
        (shuffleSimplex (m + k) n (parallelSlot m k j i hji.symm)
          (parallelShuffleEquiv p q r v).1
          ((simplicialArityMap (by omega : m + 1 + k = m + k + 1)).app _
            (shuffleSimplex (m + 1) k j (parallelShuffleEquiv p q r v).2 x z)) y) := by
  rw [normalizedChainMap_generator, shuffleSimplex_parallel_assoc,
    degreeTransport_generator_degreeCast]

/-- 概要：正規化生成元上の並列 shuffle は Koszul 符号を伴って一致する（Berger–Fresse §1.1.3）。
方針：二重和を並列 shuffle の全単射で添字替えし、符号と生成元を比較する。
規約：出力次数は p+r+q とする。
使われ方：並列結合則を任意の正規化鎖へ延長する。 -/
lemma shuffleBilinear_parallel_generators (m n k : ℕ) (i j : Fin (m + 2)) (hji : j ≠ i)
    (p q r : ℕ) (x : (simplicial (m + 2)) _⦋p⦌)
    (y : (simplicial n) _⦋q⦌) (z : (simplicial k) _⦋r⦌) :
    degreeTransport A (m + k + n) (by omega : p + q + r = p + r + q)
        ((normalizedChainMap A (simplicialArityMap (by omega : m + n + k = m + k + n))).f
          (p + q + r)
          (shuffleBilinear A (m + n) k (parallelSlot m n i j hji) (p + q) r
            ((normalizedChainMap A (simplicialArityMap
              (by omega : m + 1 + n = m + n + 1))).f (p + q)
              (shuffleValue A (m + 1) n i p q x y)) (normalizedGenerator A k r z))) =
      (-1 : ℤ) ^ (q * r) •
        shuffleBilinear A (m + k) n (parallelSlot m k j i hji.symm) (p + r) q
          ((normalizedChainMap A (simplicialArityMap
            (by omega : m + 1 + k = m + k + 1))).f (p + r)
            (shuffleValue A (m + 1) k j p r x z)) (normalizedGenerator A n q y) := by
  classical
  simp only [shuffleValue, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    normalizedChainMap_generator, shuffleBilinear_generators, shuffleValue,
    map_sum, map_zsmul, Finset.smul_sum, smul_smul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  let f (v : ShufflePath (p + q) r × ShufflePath p q) :=
    ((v.2.sign : ℤ) * (v.1.sign : ℤ)) •
      degreeTransport A (m + k + n) (by omega : p + q + r = p + r + q)
        (normalizedGenerator A (m + k + n) (p + q + r)
          ((simplicialArityMap (by omega : m + n + k = m + k + n)).app _
            (shuffleSimplex (m + n) k (parallelSlot m n i j hji) v.1
              ((simplicialArityMap (by omega : m + 1 + n = m + n + 1)).app _
                (shuffleSimplex (m + 1) n i v.2 x y)) z)))
  let g (w : ShufflePath (p + r) q × ShufflePath p r) :=
    ((-1 : ℤ) ^ (q * r) * ((w.2.sign : ℤ) * (w.1.sign : ℤ))) •
      normalizedGenerator A (m + k + n) (p + r + q)
        (shuffleSimplex (m + k) n (parallelSlot m k j i hji.symm) w.1
          ((simplicialArityMap (by omega : m + 1 + k = m + k + 1)).app _
            (shuffleSimplex (m + 1) k j w.2 x z)) y)
  change (∑ s, ∑ t, f (s, t)) = ∑ s, ∑ t, g (s, t)
  rw [← Fintype.sum_prod_type (f := f), ← Fintype.sum_prod_type (f := g)]
  apply Fintype.sum_equiv (parallelShuffleEquiv p q r)
  intro v
  dsimp only [f, g]
  have ht := shuffleParallel_generator A m n k i j hji p q r v x y z
  rw [normalizedChainMap_generator] at ht
  rw [ht]
  congr 1
  have he : (-1 : ℤˣ) ^ (q * r) * (-1 : ℤˣ) ^ (q * r) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  have hs := congrArg (fun s : ℤˣ => (-1 : ℤˣ) ^ (q * r) * s) (parallelShuffle_sign p q r v)
  conv_rhs at hs => rw [← mul_assoc, he, one_mul]
  have hz := congrArg (fun s : ℤˣ => (s : ℤ)) hs.symm
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    mul_comm] using hz

end SerrePositivity.EInfinity.BarrattEccles
