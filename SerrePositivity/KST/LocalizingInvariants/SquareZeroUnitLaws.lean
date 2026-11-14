module
public import SerrePositivity.KST.LocalizingInvariants.TensorBiproductExt

public import SerrePositivity.InfinityCategories.HA.Section7_3_4.SquareZeroMultiplication

/-!
概要：分裂平方零拡大の積に対して、左右の単位則を証明する。
方針：直和二成分へ制限し、元の代数と双加群の単位則へ戻す。
規約：非可換双加群の二つの作用を保持。使われ方：実平方零 dg 代数の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalPreadditive Preadditive
open scoped MonObj
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] (A : Mon C) (M : Bimod A A) [HasBinaryBiproduct A.X M.X]

lemma one_mul : (_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.one A M ▷ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M = (λ_ (_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M)).hom := by
  apply biprodTensorRight_hom_ext
  · calc
      (𝟙_ C ◁ biprod.inl) ≫ ((_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.one A M ▷ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M) =
          (η[A.X] ▷ A.X) ≫ (biprod.inl ⊗ₘ biprod.inl) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M := by
        simp only [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.one, ← id_tensorHom, ← tensorHom_id,
          tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
      _ = (λ_ A.X).hom ≫ biprod.inl := by rw [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_ll, ← Category.assoc, MonObj.one_mul]
      _ = (𝟙_ C ◁ biprod.inl) ≫ (λ_ (_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M)).hom := by rw [leftUnitor_naturality]
  · calc
      (𝟙_ C ◁ biprod.inr) ≫ ((_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.one A M ▷ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M) =
          (η[A.X] ▷ M.X) ≫ (biprod.inl ⊗ₘ biprod.inr) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M := by
        simp only [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.one, ← id_tensorHom, ← tensorHom_id,
          tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
      _ = (λ_ M.X).hom ≫ biprod.inr := by rw [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_lr, ← Category.assoc, M.one_actLeft]
      _ = (𝟙_ C ◁ biprod.inr) ≫ (λ_ (_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M)).hom := by rw [leftUnitor_naturality]

lemma mul_one : (_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M ◁ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.one A M) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M = (ρ_ (_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M)).hom := by
  apply biprodTensorLeft_hom_ext
  · calc
      (biprod.inl ▷ 𝟙_ C) ≫ ((_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M ◁ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.one A M) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M) =
          (A.X ◁ η[A.X]) ≫ (biprod.inl ⊗ₘ biprod.inl) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M := by
        simp only [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.one, ← id_tensorHom, ← tensorHom_id,
          tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
      _ = (ρ_ A.X).hom ≫ biprod.inl := by rw [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_ll, ← Category.assoc, MonObj.mul_one]
      _ = (biprod.inl ▷ 𝟙_ C) ≫ (ρ_ (_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M)).hom := by rw [rightUnitor_naturality]
  · calc
      (biprod.inr ▷ 𝟙_ C) ≫ ((_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M ◁ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.one A M) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M) =
          (M.X ◁ η[A.X]) ≫ (biprod.inr ⊗ₘ biprod.inl) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M := by
        simp only [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.one, ← id_tensorHom, ← tensorHom_id,
          tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
      _ = (ρ_ M.X).hom ≫ biprod.inr := by rw [_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rl, ← Category.assoc, M.actRight_one]
      _ = (biprod.inr ▷ 𝟙_ C) ≫ (ρ_ (_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M)).hom := by rw [rightUnitor_naturality]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
