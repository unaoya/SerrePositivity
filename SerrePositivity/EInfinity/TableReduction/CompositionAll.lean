module

public import SerrePositivity.EInfinity.TableReduction.CompositionNullaryZero
public import SerrePositivity.EInfinity.TableReduction.CompositionNullaryPositiveDegree

/-!
# 全 arity・全次数の実際の正規化 TR 合成保存

概要：Berger–Fresse §1.3・§1.5.7–9 の TR 部分合成保存を nullary を含めて証明する。
方針：正の内側 arity と零 arity の二次数分岐をまとめ、正規化生成元から双線形に延長する。
規約：任意の可換環・全 arity・全次数。元の単体の非退化性は要求しない。
使われ方：全射 TR から χ の微分との両立とオペラッド公理を移す主定理。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.TableReduction

open Surjection BarrattEccles
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：全実際の shuffle の TR 和は全 arity の部分合成を保つ（BF §1.5.7–9）。
方針：正の内側 arity、空語、零 arity の正次数を既存の全和の定理へ分ける。
規約：出力 arity 零と任意の入力置換列を含む。
使われ方：正規化生成元上の部分合成保存の有限和の公式。 -/
lemma onSequence_partialComposition {m n d e : ℕ} (k : Fin (m + 1))
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) :
    (∑ s : ShufflePath d e, (s.sign : ℤ) • onSequence A (fun j =>
      permutationComposition m n k (outer (s.horizontal j)) (inner (s.vertical j)))) =
      Surjection.partialComposition A m n d e k (onSequence A outer) (onSequence A inner) := by
  cases n with
  | zero =>
    cases e with
    | zero => exact onSequence_partialComposition_nullary_zero A k outer inner
    | succ e => exact onSequence_partialComposition_nullary_succ A k outer inner
  | succ n => exact onSequence_partialComposition_of_pos A (Nat.zero_lt_succ n) outer inner k

/-- 概要：全 arity の正規化生成元の実際の shuffle 合成で TR は部分合成を保つ（BF §1.5.7–9）。
方針：生成元上の全 shuffle 公式に一般の onSequence 合成保存を適用する。
規約：元の単体が退化していてもよい。
使われ方：任意の鎖に対する双線形外延性の入力。 -/
lemma normalizedMap_shuffle_generators {m n d e : ℕ} (k : Fin (m + 1))
    (x : (simplicial (m + 1)) _⦋d⦌) (y : (simplicial n) _⦋e⦌) :
    normalizedMap A (m + n) (d + e)
      (shuffleBilinear A m n k d e (normalizedGenerator A (m + 1) d x)
        (normalizedGenerator A n e y)) =
      Surjection.partialComposition A m n d e k
        (normalizedMap A (m + 1) d (normalizedGenerator A (m + 1) d x))
        (normalizedMap A n e (normalizedGenerator A n e y)) := by
  simp only [shuffleBilinear_generators, shuffleValue, map_sum, map_zsmul,
    normalizedMap_generator]
  rw [← onSequence_partialComposition A k (simplexEquiv (m + 1) d x)
    (simplexEquiv n e y)]
  apply Finset.sum_congr rfl
  intro s _
  congr 1

/-- 概要：実際の正規化 TR は全 arity・全次数の双線形 shuffle 合成を保つ（BF §1.3・§1.5.7–9）。
方針：二つの双線形写像を正規化生成元で比較し、一般の合成保存を使う。
規約：nullary、出力 arity 零、任意の可換環を含む。
使われ方：全射 TR を用いて χ の微分・単位・同変性・結合則を構成する主経路。 -/
lemma normalizedMap_shuffleBilinear {m n d e : ℕ} (k : Fin (m + 1))
    (x : (BarrattEccles.normalizedChains A (m + 1)).X d)
    (y : (BarrattEccles.normalizedChains A n).X e) :
    normalizedMap A (m + n) (d + e) (shuffleBilinear A m n k d e x y) =
      Surjection.partialComposition A m n d e k
        (normalizedMap A (m + 1) d x) (normalizedMap A n e y) := by
  let L := (shuffleBilinear A m n k d e).compr₂ (normalizedMap A (m + n) (d + e))
  let R := ((Surjection.partialComposition A m n d e k).compl₂
    (normalizedMap A n e)).comp (normalizedMap A (m + 1) d)
  have he : L = R := by
    apply normalizedGenerator_bilinear_ext A (m + 1) n d e
    intro sx sy
    change normalizedMap A (m + n) (d + e)
      (shuffleBilinear A m n k d e (normalizedGenerator A (m + 1) d sx)
        (normalizedGenerator A n e sy)) = _
    exact normalizedMap_shuffle_generators A k sx sy
  exact congrArg (fun f => f x y) he

end SerrePositivity.EInfinity.TableReduction
