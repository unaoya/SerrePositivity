module

public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
概要：全射に沿って降下した単位と積から、商対象の非可換代数構造を構成する。
方針：単位則と結合則を tensor 全射で消去して、元の代数則に戻す。
規約：tensor 全射性は適用時に検証する。使われ方：有限 dg Postnikov 切断。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory
open scoped MonObj
namespace SerrePositivity.KST.LocalizingInvariants

@[instance_reducible]
def monoidObjectAlongEpi {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (B : Mon C) {A : C} (p : B.X ⟶ A)
    [Epi (𝟙_ C ◁ p)] [Epi (p ▷ 𝟙_ C)] [Epi ((p ⊗ₘ p) ⊗ₘ p)]
    (mul : A ⊗ A ⟶ A) (hμ : (p ⊗ₘ p) ≫ mul = μ[B.X] ≫ p) : MonObj A where
  one := η[B.X] ≫ p
  mul := mul
  one_mul := by
    apply (cancel_epi (𝟙_ C ◁ p)).1
    calc
      (𝟙_ C ◁ p) ≫ (((η[B.X] ≫ p) ▷ A) ≫ mul) =
          (η[B.X] ▷ B.X) ≫ (p ⊗ₘ p) ≫ mul := by
        simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, Category.comp_id]
      _ = (𝟙_ C ◁ p) ≫ (λ_ A).hom := by
        rw [hμ, ← Category.assoc, MonObj.one_mul, leftUnitor_naturality]
  mul_one := by
    apply (cancel_epi (p ▷ 𝟙_ C)).1
    calc
      (p ▷ 𝟙_ C) ≫ ((A ◁ (η[B.X] ≫ p)) ≫ mul) =
          (B.X ◁ η[B.X]) ≫ (p ⊗ₘ p) ≫ mul := by
        simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, Category.comp_id]
      _ = (p ▷ 𝟙_ C) ≫ (ρ_ A).hom := by
        rw [hμ, ← Category.assoc, MonObj.mul_one, rightUnitor_naturality]
  mul_assoc := by
    apply (cancel_epi ((p ⊗ₘ p) ⊗ₘ p)).1
    calc
      ((p ⊗ₘ p) ⊗ₘ p) ≫ ((mul ▷ A) ≫ mul) =
          ((μ[B.X] ≫ p) ⊗ₘ p) ≫ mul := by
        rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.comp_id, hμ]
      _ = (μ[B.X] ▷ B.X) ≫ (p ⊗ₘ p) ≫ mul := by
        rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp]
      _ = (μ[B.X] ▷ B.X) ≫ μ[B.X] ≫ p := by rw [hμ]
      _ = (α_ B.X B.X B.X).hom ≫ (B.X ◁ μ[B.X]) ≫ μ[B.X] ≫ p := by
        rw [← Category.assoc, MonObj.mul_assoc, Category.assoc, Category.assoc]
      _ = (α_ B.X B.X B.X).hom ≫ (B.X ◁ μ[B.X]) ≫ (p ⊗ₘ p) ≫ mul := by
        rw [hμ]
      _ = (α_ B.X B.X B.X).hom ≫ (p ⊗ₘ ((p ⊗ₘ p) ≫ mul)) ≫ mul := by
        rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, ← hμ]
      _ = (α_ B.X B.X B.X).hom ≫ (p ⊗ₘ (p ⊗ₘ p)) ≫ (A ◁ mul) ≫ mul := by
        rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id]
      _ = ((p ⊗ₘ p) ⊗ₘ p) ≫ ((α_ A A A).hom ≫ (A ◁ mul) ≫ mul) := by
        rw [← Category.assoc, ← associator_naturality, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants
