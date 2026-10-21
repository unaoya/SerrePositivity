module

public import SerrePositivity.KST.LocalizingInvariants.TensorTripleComposition

/-!
概要：異なる代数・加群因子を持つ三重 tensor の二つの合成を計算する。
方針：tensor の関手性と associator の自然性を使う。
規約：三つの因子を同一視しない。使われ方：全射に沿う双加群作用の降下。
-/

@[expose] public section
universe u v
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.LocalizingInvariants
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {X Y Z A B P D T : C}

lemma tensorTriple_action_left (f : X ⟶ A) (g : Y ⟶ B) (h : Z ⟶ P)
    (m : A ⊗ B ⟶ D) (n : D ⊗ P ⟶ T) :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ ((m ▷ P) ≫ n) = (((f ⊗ₘ g) ≫ m) ⊗ₘ h) ≫ n := by
  simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.comp_id]

lemma tensorTriple_action_right (f : X ⟶ A) (g : Y ⟶ B) (h : Z ⟶ P)
    (m : B ⊗ P ⟶ D) (n : A ⊗ D ⟶ T) :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ ((α_ A B P).hom ≫ (A ◁ m) ≫ n) =
      (α_ X Y Z).hom ≫ (f ⊗ₘ ((g ⊗ₘ h) ≫ m)) ≫ n := by
  rw [← Category.assoc, associator_naturality, Category.assoc]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants
