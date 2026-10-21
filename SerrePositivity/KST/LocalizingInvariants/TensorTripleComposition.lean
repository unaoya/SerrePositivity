module

public import SerrePositivity.KST.LocalizingInvariants.TensorBiproductExt

/-!
概要：三重 tensor 上の二通りの積の制限を、三つの指定射の合成で計算する。
方針：tensor の関手性と associator の自然性を使う。
規約：元の associator を保持。使われ方：平方零代数の結合則。
-/

@[expose] public section
universe u v
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.LocalizingInvariants
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {X Y Z S : C}

lemma tensorTriple_mul_left (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (m : S ⊗ S ⟶ S) :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ ((m ▷ S) ≫ m) = (((f ⊗ₘ g) ≫ m) ⊗ₘ h) ≫ m := by
  simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.comp_id]

lemma tensorTriple_mul_right (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (m : S ⊗ S ⟶ S) :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ ((α_ S S S).hom ≫ (S ◁ m) ≫ m) =
      (α_ X Y Z).hom ≫ (f ⊗ₘ ((g ⊗ₘ h) ≫ m)) ≫ m := by
  rw [← Category.assoc, associator_naturality, Category.assoc]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants
