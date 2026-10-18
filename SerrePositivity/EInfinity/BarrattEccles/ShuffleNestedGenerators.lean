module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleNestedSimplex
public import SerrePositivity.EInfinity.BarrattEccles.TripleShufflePermutation
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleDegenerate

/-!
# 正規化生成元上の shuffle の入れ子結合則

概要：Berger–Fresse §1.1.3 の反復 shuffle 和を正規化生成元上で比較する。
方針：三入力の添字の全単射、符号の積と合成単体の一致を使う。
規約：出力の arity を移送してから正規化鎖の次数を移送する。
使われ方：任意の正規化鎖上の入れ子結合則の生成元の場合となる。
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

/-- 概要：入れ子の shuffle の対応する各生成元は移送後に一致する（Berger–Fresse §1.1.3）。
方針：単体の入れ子結合則と正規化生成元の自然性を使う。
規約：符号を掛ける前の一項について述べる。
使われ方：二重 shuffle 和の添字替えにおける項の等式を与える。 -/
lemma shuffleNested_generator (m n k : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (p q r : ℕ) (v : ShufflePath (p + q) r × ShufflePath p q)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial (n + 1)) _⦋q⦌)
    (z : (simplicial k) _⦋r⦌) :
    degreeTransport A (m + (n + k)) (Nat.add_assoc p q r)
        ((normalizedChainMap A (simplicialArityMap (Nat.add_assoc m n k))).f (p + q + r)
          (normalizedGenerator A (m + n + k) (p + q + r)
            (shuffleSimplex (m + n) k (nestedSlot m n i j) v.1
              (shuffleSimplex m (n + 1) i v.2 x y) z))) =
      normalizedGenerator A (m + (n + k)) (p + (q + r))
        (shuffleSimplex m (n + k) i (tripleShuffleEquiv p q r v).1 x
          (shuffleSimplex n k j (tripleShuffleEquiv p q r v).2 y z)) := by
  rw [normalizedChainMap_generator, shuffleSimplex_nested_assoc,
    degreeTransport_generator_degreeCast]

/-- 概要：正規化生成元の反復 shuffle は入れ子の結合則を満たす（Berger–Fresse §1.1.3）。
方針：二つの有限和を三入力の添字の全単射で対応させる。
規約：外側と内側の符号の積を保ち、arity と次数を移送する。
使われ方：三つの入力に関する線形性で結合則を任意の鎖へ拡張する。 -/
lemma shuffleBilinear_nested_generators (m n k : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (p q r : ℕ) (x : (simplicial (m + 1)) _⦋p⦌)
    (y : (simplicial (n + 1)) _⦋q⦌) (z : (simplicial k) _⦋r⦌) :
    degreeTransport A (m + (n + k)) (Nat.add_assoc p q r)
        ((normalizedChainMap A (simplicialArityMap (Nat.add_assoc m n k))).f (p + q + r)
          (shuffleBilinear A (m + n) k (nestedSlot m n i j) (p + q) r
            (shuffleValue A m (n + 1) i p q x y) (normalizedGenerator A k r z))) =
      shuffleBilinear A m (n + k) i p (q + r) (normalizedGenerator A (m + 1) p x)
        (shuffleValue A n k j q r y z) := by
  classical
  have hgen (t : ShufflePath p q) :
      shuffleBilinear A (m + n) k (nestedSlot m n i j) (p + q) r
        (normalizedGenerator A (m + (n + 1)) (p + q) (shuffleSimplex m (n + 1) i t x y))
        (normalizedGenerator A k r z) =
      shuffleValue A (m + n) k (nestedSlot m n i j) (p + q) r
        (shuffleSimplex m (n + 1) i t x y) z :=
    shuffleBilinear_generators A (m + n) k (nestedSlot m n i j) (p + q) r _ z
  simp only [shuffleValue, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    shuffleBilinear_generators, hgen, shuffleValue, map_sum, map_zsmul, Finset.smul_sum, smul_smul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  let f (v : ShufflePath (p + q) r × ShufflePath p q) :=
    ((v.2.sign : ℤ) * (v.1.sign : ℤ)) •
      degreeTransport A (m + (n + k)) (Nat.add_assoc p q r)
        ((normalizedChainMap A (simplicialArityMap (Nat.add_assoc m n k))).f (p + q + r)
          (normalizedGenerator A (m + n + k) (p + q + r)
            (shuffleSimplex (m + n) k (nestedSlot m n i j) v.1
              (shuffleSimplex m (n + 1) i v.2 x y) z)))
  let g (w : ShufflePath p (q + r) × ShufflePath q r) :=
    ((w.2.sign : ℤ) * (w.1.sign : ℤ)) •
      normalizedGenerator A (m + (n + k)) (p + (q + r))
        (shuffleSimplex m (n + k) i w.1 x (shuffleSimplex n k j w.2 y z))
  change (∑ s, ∑ t, f (s, t)) = ∑ s, ∑ t, g (s, t)
  rw [← Fintype.sum_prod_type (f := f), ← Fintype.sum_prod_type (f := g)]
  apply Fintype.sum_equiv (tripleShuffleEquiv p q r)
  intro v
  dsimp only [f, g]
  rw [shuffleNested_generator]
  have h := congrArg (fun s : ℤˣ => (s : ℤ)) (tripleShuffle_sign p q r v)
  simp only [Units.val_mul] at h
  congr 1
  simpa only [mul_comm] using h

end SerrePositivity.EInfinity.BarrattEccles
