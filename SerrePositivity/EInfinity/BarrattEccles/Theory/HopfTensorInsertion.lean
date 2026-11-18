module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorFirstBlock
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionZero

/-!
# テンソル演算の先頭代入との比較

## 概要
BF §1.1.4 のテンソル演算と、オペラッド代数の指定された先頭代入射を比較する。

## 方針
先頭ブロックの比較に入力数の交換の移送を合成する。

## 規約
代入する演算の入力数零を含み、移送の射は二列で同じ等式から作る。

## 使われ方
HA 3.2.4.7 の比較先のテンソル代数の合成公理。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open DifferentialGraded TensorPowers
variable {A : Type u} [CommRing A]
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power

/-- BF §1.1.4 の二列分離は、指定された先頭代入射と可換。 -/
lemma tensorInsertionAction_separation_zero (V W C C₁ C₂ : Complex A) (m n : ℕ)
    (d : C ⟶ C₁ ⊗ C₂) (a : C₁ ⊗ power V n ⟶ V) (b : C₂ ⊗ power W n ⟶ W) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction (V ⊗ W) C m n 0
      ((d ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W n).hom) ≫ tensorμ _ _ _ _ ≫ (a ⊗ₘ b)) ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W (m + 1)).hom =
      (d ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W (m + n)).hom) ≫ tensorμ _ _ _ _ ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction V C₁ m n 0 a ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction W C₂ m n 0 b) := by
  have h := tensorFirstAction_separation V W C C₁ C₂ n m d a b
  simp only [tensorFirstAction, Category.assoc] at h
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_zero, Category.assoc]
  rw [h, whiskerLeft_comp_tensorHom_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation_index V W (Nat.add_comm m n),
    ← tensorHom_comp_whiskerLeft_assoc, tensorμ_natural_right_assoc,
    tensorHom_comp_tensorHom]

end SerrePositivity.EInfinity
