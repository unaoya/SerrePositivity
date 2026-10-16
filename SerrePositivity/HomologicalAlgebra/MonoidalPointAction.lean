module
public import SerrePositivity.HomologicalAlgebra.MonoidalUnitHomRing

/-! # Multiplication by an actual unit-section of a commutative algebra object -/
@[expose] public noncomputable section
universe v u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Multiplication by a unit-section is an endomorphism of the original algebra object. -/
def commMonPointAction (A : CommMon C) (p : 𝟙_ C ⟶ A.X) : A.X ⟶ A.X :=
  (λ_ A.X).inv ≫ (p ⊗ₘ 𝟙 A.X) ≫ A.mon.mul

/-- Algebra morphisms intertwine multiplication by a section and by its image. -/
@[reassoc] lemma commMonPointAction_naturality
    {A B : CommMon C} (f : A ⟶ B) (p : 𝟙_ C ⟶ A.X) :
    commMonPointAction A p ≫ f.hom.hom =
      f.hom.hom ≫ commMonPointAction B (p ≫ f.hom.hom) := by
  let := A.mon
  let := B.mon
  let := f.hom.isMonHom_hom
  simp only [commMonPointAction, Category.assoc, IsMonHom.mul_hom,
    tensorHom_comp_tensorHom_assoc, Category.id_comp]
  erw [leftUnitor_inv_naturality_assoc]
  rw [← id_tensorHom]
  simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp]
  erw [Category.comp_id]
  rfl

/-- On the actual unit sections this endomorphism is precisely multiplication. -/
lemma commMonPointAction_sections (A : CommMon C) (p q : 𝟙_ C ⟶ A.X) :
    letI := commMonUnitHomCommMonoid C A
    q ≫ commMonPointAction A p = p * q := by
  let := commMonUnitHomCommMonoid C A
  rw [commMonUnitHom_mul]
  simp only [commMonPointAction, leftUnitor_inv_naturality_assoc, ← id_tensorHom,
    tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]

end SerrePositivity
