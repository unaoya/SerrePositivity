module

public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
概要：単位と積を保つ共同単射族から、源の実モノイド対象を構成する。
方針：各モノイド則を全射影へ送り、元の単位則と結合則へ帰着する。
規約：tensor による極限保存は要求しない。使われ方：実 dg 代数 pullback。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory MonoidalCategory
open scoped MonObj
namespace SerrePositivity.KST.LocalizingInvariants

@[instance_reducible]
def monoidObjectAlongFamily {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {I : Type w} (Bs : I → Mon C) {A : C} (p : ∀ j, A ⟶ (Bs j).X)
    (hj : ∀ {T : C} {f g : T ⟶ A}, (∀ j, f ≫ p j = g ≫ p j) → f = g)
    (one : 𝟙_ C ⟶ A) (mul : A ⊗ A ⟶ A)
    (hOne : ∀ j, one ≫ p j = η[(Bs j).X])
    (hMul : ∀ j, mul ≫ p j = (p j ⊗ₘ p j) ≫ μ[(Bs j).X]) : MonObj A where
  one := one
  mul := mul
  one_mul := by
    apply hj
    intro j
    let B := Bs j
    let i := p j
    have hη : one ≫ i = η[B.X] := hOne j
    have hμ : mul ≫ i = (i ⊗ₘ i) ≫ μ[B.X] := hMul j
    calc
      ((one ▷ A) ≫ mul) ≫ i = ((one ≫ i) ⊗ₘ i) ≫ μ[B.X] := by
        rw [Category.assoc, hμ, ← tensorHom_id one A, ← Category.assoc,
          tensorHom_comp_tensorHom, Category.id_comp]
      _ = (𝟙_ C ◁ i) ≫ (η[B.X] ▷ B.X) ≫ μ[B.X] := by
        rw [hη, ← id_tensorHom, ← tensorHom_id, ← Category.assoc,
          tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      _ = (λ_ A).hom ≫ i := by rw [MonObj.one_mul, leftUnitor_naturality]
  mul_one := by
    apply hj
    intro j
    let B := Bs j
    let i := p j
    have hη : one ≫ i = η[B.X] := hOne j
    have hμ : mul ≫ i = (i ⊗ₘ i) ≫ μ[B.X] := hMul j
    calc
      ((A ◁ one) ≫ mul) ≫ i = (i ⊗ₘ (one ≫ i)) ≫ μ[B.X] := by
        rw [Category.assoc, hμ, ← id_tensorHom A one, ← Category.assoc,
          tensorHom_comp_tensorHom, Category.id_comp]
      _ = (i ▷ 𝟙_ C) ≫ (B.X ◁ η[B.X]) ≫ μ[B.X] := by
        rw [hη, ← tensorHom_id, ← id_tensorHom, ← Category.assoc,
          tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      _ = (ρ_ A).hom ≫ i := by rw [MonObj.mul_one, rightUnitor_naturality]
  mul_assoc := by
    apply hj
    intro j
    let B := Bs j
    let i := p j
    have hη : one ≫ i = η[B.X] := hOne j
    have hμ : mul ≫ i = (i ⊗ₘ i) ≫ μ[B.X] := hMul j
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
