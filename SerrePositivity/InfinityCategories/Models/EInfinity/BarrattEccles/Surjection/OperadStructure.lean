module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Sequence
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComplexNested
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComplexParallel
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComplexEquivariance
public import SerrePositivity.EInfinity.BarrattEccles.InverseSlotPermutations

/-!
模型。文献の定義との比較は後で
# 全射語の対称 dg オペラッド

概要：Berger–Fresse §1.2 の χ を実際の非有界整数複体の対称 dg オペラッドにまとめる。
方針：構成した対称列・単位・部分合成の複体射と、全射 TR から得た全ての法則を使う。
規約：arity 零を含み、共変な対称群作用は値の左置換。
使われ方：一般の TR オペラッド射と区間切断作用の受け口。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable (A : Type u) [CommRing A]

set_option maxHeartbeats 800000 in
-- 対称列の評価と全ての複体射の法則を同時に照合するため精緻化の上限を増やす。
/-- 概要：全射語と符号付き部分合成による対称 dg オペラッド χ（BF §1.2）。
方針：整数複体の対称列と構成した単位・部分合成に全法則の証明を付ける。
規約：任意の可換環、零 arity、非有界整数コチェイン複体。
使われ方：TR のオペラッド射性と Δ¹ の区間切断作用を構成する。 -/
def operad : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A where
  sequence := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sequence A
  unit := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexUnit A
  comp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A
  unit_comp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition_left_unit A
  comp_unit := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition_right_unit A
  inner_equivariance m n i σ := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sequence_map_permutation A n σ,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sequence_map_permutation A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i σ)]
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A n σ) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m n i =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m n i ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i σ)
    simpa only [_root_.SerrePositivity.EInfinity.BarrattEccles.innerPermutation_inv, inv_inv] using
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition_inner_rightAction A m n i σ⁻¹
  outer_equivariance m n i σ := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sequence_map_permutation A (m + 1) σ,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sequence_map_permutation A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ)]
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A (m + 1) σ ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m n (σ i) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m n i ≫
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ)
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition_outer_rightAction A m n (σ i) σ⁻¹
    have hs : σ⁻¹ (σ i) = i := σ.symm_apply_apply i
    simpa only [_root_.SerrePositivity.EInfinity.BarrattEccles.outerPermutation_inv, inv_inv, hs] using h
  nested_assoc := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition_nested_assoc A
  parallel_assoc := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition_parallel_assoc A

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
