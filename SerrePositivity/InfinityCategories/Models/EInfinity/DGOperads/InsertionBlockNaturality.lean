module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorNaturality

/-!
模型。文献の定義との比較は後で
# 三ブロックへの代入の自然性

概要：Berger–Moerdijk §1 の代数・余代数の代入を一般の三ブロックで比較する。
方針：係数と先行ブロックの交換を、全ブロックの射へ自然に通す。
規約：一般の対称モノイダル圏で、空ブロックは単位対象で表す。
使われ方：テンソル冪への代入の自然性と単位余代数の計算に用いる。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

/-- 概要：三つの入力ブロックの中央へ係数付き演算を適用する（BM §1）。
方針：係数を先行ブロックの後へ交換し、中央のブロックへ適用する。
規約：ブロックは一般の対称モノイダル圏の任意の対象でよい。
使われ方：代入・余代入の底の射についての自然性を共通に扱う。 -/
def tensorInsertionBlock {K : Type u} [Category.{v} K] [MonoidalCategory K]
    [SymmetricCategory K] (C L M X Y : K) (θ : C ⊗ X ⟶ Y) :
    C ⊗ (L ⊗ (X ⊗ M)) ⟶ L ⊗ (Y ⊗ M) :=
  (α_ C L (X ⊗ M)).inv ≫ ((β_ C L).hom ▷ (X ⊗ M)) ≫
    (α_ L C (X ⊗ M)).hom ≫ (L ◁ (α_ C X M).inv) ≫ (L ◁ (θ ▷ M))

/-- 概要：三ブロックの代入は各ブロックと演算の比較について自然（BM §1）。
方針：結合子と交換の自然性で全ての射を演算の後へ通す。
規約：中央の比較図式は与えた係数を固定する。
使われ方：複体のテンソル冪への代入の自然性を証明する。 -/
@[reassoc]
lemma tensorInsertionBlock_naturality {K : Type u} [Category.{v} K] [MonoidalCategory K]
    [SymmetricCategory K] {C L M X Y L' M' X' Y' : K}
    (l : L ⟶ L') (m : M ⟶ M') (x : X ⟶ X') (y : Y ⟶ Y')
    (θ : C ⊗ X ⟶ Y) (θ' : C ⊗ X' ⟶ Y') (hθ : (C ◁ x) ≫ θ' = θ ≫ y) :
    (C ◁ (l ⊗ₘ (x ⊗ₘ m))) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionBlock C L' M' X' Y' θ' =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionBlock C L M X Y θ ≫ (l ⊗ₘ (y ⊗ₘ m)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionBlock
  rw [← id_tensorHom, associator_inv_naturality_assoc]
  rw [tensorHom_comp_whiskerRight_assoc, BraidedCategory.braiding_naturality]
  rw [← whiskerRight_comp_tensorHom_assoc, associator_naturality_assoc]
  simp only [id_tensorHom]
  rw [tensorHom_comp_whiskerLeft_assoc]
  rw [← id_tensorHom C (x ⊗ₘ m), associator_inv_naturality]
  simp only [Category.assoc, ← id_tensorHom, ← tensorHom_id,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  simp only [← id_tensorHom] at hθ
  rw [hθ]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
