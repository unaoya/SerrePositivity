module

public import SerrePositivity.EInfinity.TableReduction.TransportCompatibility
public import SerrePositivity.EInfinity.TableReduction.Surjectivity
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleNestedChains
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleParallelChains

/-!
# 全射語の部分合成の二つの結合則

概要：Berger–Fresse §1.2.4–5 の入れ子と並列の部分合成の結合則を証明する。
方針：三入力を全射 TR で持ち上げ、BE の結合則に合成と移送の保存を適用する。
規約：零 arity・零次数を含み、並列の交換には Koszul 符号を付ける。
使われ方：χ の対称 dg オペラッドの結合則の成分計算。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Surjection

open TableReduction

variable (A : Type u) [CommRing A]

/-- 概要：全射語の部分合成は全次数の入れ子結合則を満たす（BF §1.2.4–5）。
方針：三入力を BE の逆像に取り、実際の正規化 TR の合成と移送の保存を使う。
規約：入れ子位置は既存の BE の挿入ラベルで指定する。
使われ方：χ の nested_assoc の成分公式。 -/
lemma partialComposition_nested_assoc (m n k : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (p q r : ℕ) (x : degreeModule A (m + 1) p)
    (y : degreeModule A (n + 1) q) (z : degreeModule A k r) :
    degreeTransport A (m + (n + k)) (Nat.add_assoc p q r)
        (arityTransport A (Nat.add_assoc m n k) (p + q + r)
          (partialComposition A (m + n) k (p + q) r (BarrattEccles.nestedSlot m n i j)
            (partialComposition A m (n + 1) p q i x y) z)) =
      partialComposition A m (n + k) p (q + r) i x
        (partialComposition A n k q r j y z) := by
  obtain ⟨x, rfl⟩ := normalizedMap_surjective A (m + 1) p x
  obtain ⟨y, rfl⟩ := normalizedMap_surjective A (n + 1) q y
  obtain ⟨z, rfl⟩ := normalizedMap_surjective A k r z
  have h := congrArg (normalizedMap A (m + (n + k)) (p + (q + r)))
    (BarrattEccles.shuffleBilinear_nested_assoc A m n k i j p q r x y z)
  simp only [normalizedMap_degreeTransport, normalizedMap_arityTransport,
    normalizedMap_shuffleBilinear] at h
  erw [normalizedMap_shuffleBilinear A (n := n + 1) i x y] at h
  exact h

/-- 概要：全射語の並列部分合成は Koszul 符号付き結合則を満たす（BF §1.2.4–5）。
方針：全射 TR の三つの逆像で BE の並列法則を評価する。
規約：二つの挿入位置は異なり、交換符号は (−1)^(q*r)。
使われ方：χ の parallel_assoc の成分公式。 -/
lemma partialComposition_parallel_assoc (m n k : ℕ) (i j : Fin (m + 2)) (hji : j ≠ i)
    (p q r : ℕ) (x : degreeModule A (m + 2) p)
    (y : degreeModule A n q) (z : degreeModule A k r) :
    degreeTransport A (m + k + n) (by omega : p + q + r = p + r + q)
        (arityTransport A (by omega : m + n + k = m + k + n) (p + q + r)
          (partialComposition A (m + n) k (p + q) r
            (BarrattEccles.parallelSlot m n i j hji)
            (arityTransport A (by omega : m + 1 + n = m + n + 1) (p + q)
              (partialComposition A (m + 1) n p q i x y)) z)) =
      (-1 : ℤ) ^ (q * r) •
        partialComposition A (m + k) n (p + r) q
          (BarrattEccles.parallelSlot m k j i hji.symm)
          (arityTransport A (by omega : m + 1 + k = m + k + 1) (p + r)
            (partialComposition A (m + 1) k p r j x z)) y := by
  obtain ⟨x, rfl⟩ := normalizedMap_surjective A (m + 2) p x
  obtain ⟨y, rfl⟩ := normalizedMap_surjective A n q y
  obtain ⟨z, rfl⟩ := normalizedMap_surjective A k r z
  have h := congrArg (normalizedMap A (m + k + n) (p + r + q))
    (BarrattEccles.shuffleBilinear_parallel_assoc A m n k i j hji p q r x y z)
  simpa only [normalizedMap_degreeTransport, normalizedMap_arityTransport, map_zsmul,
    normalizedMap_shuffleBilinear] using h

end SerrePositivity.EInfinity.Surjection
