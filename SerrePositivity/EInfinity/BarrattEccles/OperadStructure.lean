module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic
public import SerrePositivity.EInfinity.BarrattEccles.Sequence
public import SerrePositivity.EInfinity.BarrattEccles.InverseSlotPermutations
public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionEquivariance
public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionParallel
public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionRightUnit

/-!
# Barratt–Eccles の対称 dg オペラッド

概要：Berger–Fresse §1.1 の正規化 Barratt–Eccles 複体を対称 dg オペラッドにまとめる。
方針：shuffle の部分合成、単位、等変性と二つの結合則の証明を用いる。
規約：対称列の共変な作用には右作用の逆置換を使う。
使われ方：Barratt–Eccles 代数とその転送モデル構造の入力となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory

variable (A : Type u) [CommRing A]

set_option maxHeartbeats 800000 in
-- 対称列の評価と複体の型の照合を全ての法則に対して同時に行うため、精緻化の上限を増やす。
/-- 概要：正規化 EΣₙ と shuffle 合成による Barratt–Eccles オペラッド（Berger–Fresse §1.1）。
方針：構成済みの複体、単位と部分合成に、各法則の証明を組み合わせる。
規約：arity 0 を含み、全ての合成は非有界整数コチェイン複体の射である。
使われ方：E∞ dg 代数の圏と忘却関手を定義する。 -/
def operad : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A where
  sequence := sequence A
  unit := unit A
  comp := partialComposition A
  unit_comp := partialComposition_left_unit A
  comp_unit := partialComposition_right_unit A
  inner_equivariance m n i σ := by
    simp only [sequence_map_permutation A n σ,
      sequence_map_permutation A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i σ)]
    rw [← innerPermutation_inv m n i σ]
    exact partialComposition_inner_rightAction A m n i σ⁻¹
  outer_equivariance m n i σ := by
    simp only [sequence_map_permutation A (m + 1) σ,
      sequence_map_permutation A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ)]
    rw [← outerPermutation_inv m n i σ]
    have h := partialComposition_outer_rightAction A m n (σ i) σ⁻¹
    have hs : σ⁻¹ (σ i) = i := σ.symm_apply_apply i
    rw [hs] at h
    exact h
  nested_assoc := partialComposition_nested_assoc A
  parallel_assoc := partialComposition_parallel_assoc A

end SerrePositivity.EInfinity.BarrattEccles
