module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CoInsertion

/-!
模型。文献の定義との比較は後で
# 余演算の代入の自然性

概要：Berger–Fresse §3.1 の余演算の代入を係数射と複体射に沿って比較する。
方針：分割と連結の自然性により、指定位置の余演算の可換性へ帰着する。
規約：出力 arity 0 を含む。
使われ方：余代数の制限・同型移送と convolution の関手性を証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：余演算の代入は係数射に関して自然（Berger–Fresse §3.1）。
方針：係数射を分割・交換・結合子の後ろへ移す。
規約：底の複体と出力数は同じとする。
使われ方：オペラッド射に沿う余代数構造の制限を定義する。 -/
@[reassoc]
lemma tensorCoInsertionAction_coeff {K C D : Complex A} (f : C ⟶ D)
    (m n : ℕ) (i : Fin (m + 1)) (θ : D ⊗ K ⟶ power K n) :
    (f ▷ power K (m + 1)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction K D m n i θ =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction K C m n i ((f ▷ K) ≫ θ) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction, power]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_left]
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_middle_assoc]
  simp only [← whiskerLeft_comp_assoc]
  rw [associator_inv_naturality_left_assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
