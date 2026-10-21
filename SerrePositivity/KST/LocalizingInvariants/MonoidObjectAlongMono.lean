module

public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
概要：元の代数への単射と指定された単位・積の閉性から、部分対象の代数構造を作る。
方針：各モノイド則を元の単射で消去し、tensor の関手性と元の三つの代数則を使う。
規約：積の可換性は要求しない。使われ方：smart connective cover の実 dg 代数構造。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory
open scoped MonObj
namespace SerrePositivity.KST.LocalizingInvariants

@[instance_reducible]
def monoidObjectAlongMono {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (B : Mon C) {A : C} (i : A ⟶ B.X) [Mono i]
    (one : 𝟙_ C ⟶ A) (mul : A ⊗ A ⟶ A)
    (hη : one ≫ i = η[B.X]) (hμ : mul ≫ i = (i ⊗ₘ i) ≫ μ[B.X]) : MonObj A where
  one := one
  mul := mul
  one_mul := by
    apply (cancel_mono i).1
    calc
      ((one ▷ A) ≫ mul) ≫ i = ((one ≫ i) ⊗ₘ i) ≫ μ[B.X] := by
        rw [Category.assoc, hμ, ← tensorHom_id one A, ← Category.assoc,
          tensorHom_comp_tensorHom, Category.id_comp]
      _ = (𝟙_ C ◁ i) ≫ (η[B.X] ▷ B.X) ≫ μ[B.X] := by
        rw [hη, ← id_tensorHom, ← tensorHom_id, ← Category.assoc,
          tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      _ = (λ_ A).hom ≫ i := by rw [MonObj.one_mul, leftUnitor_naturality]
  mul_one := by
    apply (cancel_mono i).1
    calc
      ((A ◁ one) ≫ mul) ≫ i = (i ⊗ₘ (one ≫ i)) ≫ μ[B.X] := by
        rw [Category.assoc, hμ, ← id_tensorHom A one, ← Category.assoc,
          tensorHom_comp_tensorHom, Category.id_comp]
      _ = (i ▷ 𝟙_ C) ≫ (B.X ◁ η[B.X]) ≫ μ[B.X] := by
        rw [hη, ← tensorHom_id, ← id_tensorHom, ← Category.assoc,
          tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      _ = (ρ_ A).hom ≫ i := by rw [MonObj.mul_one, rightUnitor_naturality]
  mul_assoc := by
    apply (cancel_mono i).1
    calc
      ((mul ▷ A) ≫ mul) ≫ i = ((mul ≫ i) ⊗ₘ i) ≫ μ[B.X] := by
        rw [Category.assoc, hμ, ← tensorHom_id mul A, ← Category.assoc,
          tensorHom_comp_tensorHom, Category.id_comp]
        rw [hμ]
      _ = ((i ⊗ₘ i) ⊗ₘ i) ≫ (μ[B.X] ▷ B.X) ≫ μ[B.X] := by
        rw [hμ, ← tensorHom_id, ← Category.assoc, tensorHom_comp_tensorHom,
          Category.comp_id]
      _ = ((i ⊗ₘ i) ⊗ₘ i) ≫ (α_ B.X B.X B.X).hom ≫
          (B.X ◁ μ[B.X]) ≫ μ[B.X] := by rw [MonObj.mul_assoc]
      _ = (α_ A A A).hom ≫ (i ⊗ₘ (i ⊗ₘ i)) ≫ (B.X ◁ μ[B.X]) ≫ μ[B.X] := by
        rw [← Category.assoc, associator_naturality, Category.assoc]
      _ = (α_ A A A).hom ≫ (i ⊗ₘ ((i ⊗ₘ i) ≫ μ[B.X])) ≫ μ[B.X] := by
        rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id]
      _ = (α_ A A A).hom ≫ (i ⊗ₘ (mul ≫ i)) ≫ μ[B.X] := by rw [← hμ]
      _ = (α_ A A A).hom ≫ (A ◁ mul) ≫ (i ⊗ₘ i) ≫ μ[B.X] := by
        rw [← id_tensorHom A mul, tensorHom_comp_tensorHom_assoc, Category.id_comp]
      _ = ((α_ A A A).hom ≫ (A ◁ mul) ≫ mul) ≫ i := by simp only [Category.assoc, hμ]

end SerrePositivity.KST.LocalizingInvariants
