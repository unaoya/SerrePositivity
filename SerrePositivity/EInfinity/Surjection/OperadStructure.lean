module

public import SerrePositivity.EInfinity.Operad.Basic
public import SerrePositivity.EInfinity.Surjection.Sequence
public import SerrePositivity.EInfinity.Surjection.ComplexNested
public import SerrePositivity.EInfinity.Surjection.ComplexParallel
public import SerrePositivity.EInfinity.Surjection.ComplexEquivariance
public import SerrePositivity.EInfinity.BarrattEccles.InverseSlotPermutations

/-!
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

namespace SerrePositivity.EInfinity.Surjection

open CategoryTheory MonoidalCategory

variable (A : Type u) [CommRing A]

set_option maxHeartbeats 800000 in
-- 対称列の評価と全ての複体射の法則を同時に照合するため精緻化の上限を増やす。
/-- 概要：全射語と符号付き部分合成による対称 dg オペラッド χ（BF §1.2）。
方針：整数複体の対称列と構成した単位・部分合成に全法則の証明を付ける。
規約：任意の可換環、零 arity、非有界整数コチェイン複体。
使われ方：TR のオペラッド射性と Δ¹ の区間切断作用を構成する。 -/
def operad : Operad A where
  sequence := sequence A
  unit := complexUnit A
  comp := complexPartialComposition A
  unit_comp := complexPartialComposition_left_unit A
  comp_unit := complexPartialComposition_right_unit A
  inner_equivariance m n i σ := by
    simp only [sequence_map_permutation A n σ,
      sequence_map_permutation A (m + n) (operadInnerPermutation m n i σ)]
    change (complex A (m + 1) ◁ complexRename A n σ) ≫ complexPartialComposition A m n i =
      complexPartialComposition A m n i ≫ complexRename A (m + n) (operadInnerPermutation m n i σ)
    simpa only [BarrattEccles.innerPermutation_inv, inv_inv] using
      complexPartialComposition_inner_rightAction A m n i σ⁻¹
  outer_equivariance m n i σ := by
    simp only [sequence_map_permutation A (m + 1) σ,
      sequence_map_permutation A (m + n) (operadOuterPermutation m n i σ)]
    change (complexRename A (m + 1) σ ▷ complex A n) ≫
      complexPartialComposition A m n (σ i) =
        complexPartialComposition A m n i ≫
          complexRename A (m + n) (operadOuterPermutation m n i σ)
    have h := complexPartialComposition_outer_rightAction A m n (σ i) σ⁻¹
    have hs : σ⁻¹ (σ i) = i := σ.symm_apply_apply i
    simpa only [BarrattEccles.outerPermutation_inv, inv_inv, hs] using h
  nested_assoc := complexPartialComposition_nested_assoc A
  parallel_assoc := complexPartialComposition_parallel_assoc A

end SerrePositivity.EInfinity.Surjection
