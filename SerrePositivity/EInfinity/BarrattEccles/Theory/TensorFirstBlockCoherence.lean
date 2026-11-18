module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorPowerSeparationAppend

/-!
# テンソル演算の先頭ブロックの分離

## 概要
Berger–Fresse §1.1.4 のテンソル作用で、先頭の入力ブロックへの演算を二列へ分ける。

## 方針
四因子の分離の自然性と結合子の整合性を使い、二列の作用を独立に適用する。

## 規約
全ての係数射とブロックの分離射は指定された射のまま保持する。

## 使われ方
HA 3.2.4.7 の比較先のテンソル代数の部分合成則。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- BF §1.1.4 の二列分離と先頭の二つの作用の比較。 -/
lemma tensorFirstBlockAssembly {O N M O₁ O₂ N₁ N₂ M₁ M₂ V W : C}
    (d : O ⟶ O₁ ⊗ O₂) (s : N ⟶ N₁ ⊗ N₂) (t : M ⟶ M₁ ⊗ M₂)
    (a : O₁ ⊗ N₁ ⟶ V) (b : O₂ ⊗ N₂ ⟶ W) :
    (α_ O N M).inv ≫
      (((d ⊗ₘ s) ≫ tensorμ O₁ O₂ N₁ N₂ ≫ (a ⊗ₘ b)) ⊗ₘ t) ≫
        tensorμ V W M₁ M₂ =
      (d ⊗ₘ ((s ⊗ₘ t) ≫ tensorμ N₁ N₂ M₁ M₂)) ≫
        tensorμ O₁ O₂ (N₁ ⊗ M₁) (N₂ ⊗ M₂) ≫
          (((α_ O₁ N₁ M₁).inv ≫ (a ▷ M₁)) ⊗ₘ
            ((α_ O₂ N₂ M₂).inv ≫ (b ▷ M₂))) := by
  rw [← tensorHom_comp_whiskerRight_assoc]
  simp only [comp_whiskerRight, Category.assoc]
  rw [tensorμ_natural_left, ← associator_inv_naturality_assoc,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorμ_associativity_inv_assoc]
  simp only [tensorHom_comp_tensorHom, tensorHom_comp_whiskerLeft_assoc]

end SerrePositivity.EInfinity
