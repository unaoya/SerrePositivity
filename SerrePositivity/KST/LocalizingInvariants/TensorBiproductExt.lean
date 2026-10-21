module

public import SerrePositivity.KST.LocalizingInvariants.CochainHomSupport
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
概要：加法的 tensor における直和始域の射を、二つまたは四つの成分で判定する。
方針：直和の恒等射の分解を tensor へ写し、各包含での一致を合成する。
規約：射の厳密な等式。使われ方：dg 平方零拡大の代数則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalPreadditive Preadditive
namespace SerrePositivity.KST.LocalizingInvariants

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] {A B P T : C} [HasBinaryBiproduct A B]

lemma biprodTensorLeft_hom_ext {f g : (A ⊞ B) ⊗ P ⟶ T}
    (hl : (biprod.inl ▷ P) ≫ f = (biprod.inl ▷ P) ≫ g)
    (hr : (biprod.inr ▷ P) ≫ f = (biprod.inr ▷ P) ≫ g) : f = g := by
  calc
    f = (biprod.fst ▷ P) ≫ ((biprod.inl ▷ P) ≫ f) +
        (biprod.snd ▷ P) ≫ ((biprod.inr ▷ P) ≫ f) := by
      rw [← Category.assoc, ← Category.assoc, ← comp_whiskerRight, ← comp_whiskerRight,
        ← add_comp, ← add_whiskerRight, biprod.total, id_whiskerRight, Category.id_comp]
    _ = (biprod.fst ▷ P) ≫ ((biprod.inl ▷ P) ≫ g) +
        (biprod.snd ▷ P) ≫ ((biprod.inr ▷ P) ≫ g) := by rw [hl, hr]
    _ = g := by
      rw [← Category.assoc, ← Category.assoc, ← comp_whiskerRight, ← comp_whiskerRight,
        ← add_comp, ← add_whiskerRight, biprod.total, id_whiskerRight, Category.id_comp]

lemma biprodTensorRight_hom_ext {f g : P ⊗ (A ⊞ B) ⟶ T}
    (hl : (P ◁ biprod.inl) ≫ f = (P ◁ biprod.inl) ≫ g)
    (hr : (P ◁ biprod.inr) ≫ f = (P ◁ biprod.inr) ≫ g) : f = g := by
  calc
    f = (P ◁ biprod.fst) ≫ ((P ◁ biprod.inl) ≫ f) +
        (P ◁ biprod.snd) ≫ ((P ◁ biprod.inr) ≫ f) := by
      rw [← Category.assoc, ← Category.assoc, ← whiskerLeft_comp, ← whiskerLeft_comp,
        ← add_comp, ← whiskerLeft_add, biprod.total, whiskerLeft_id, Category.id_comp]
    _ = (P ◁ biprod.fst) ≫ ((P ◁ biprod.inl) ≫ g) +
        (P ◁ biprod.snd) ≫ ((P ◁ biprod.inr) ≫ g) := by rw [hl, hr]
    _ = g := by
      rw [← Category.assoc, ← Category.assoc, ← whiskerLeft_comp, ← whiskerLeft_comp,
        ← add_comp, ← whiskerLeft_add, biprod.total, whiskerLeft_id, Category.id_comp]

lemma biprodTensor_hom_ext {f g : (A ⊞ B) ⊗ (A ⊞ B) ⟶ T}
    (hll : (biprod.inl ⊗ₘ biprod.inl) ≫ f = (biprod.inl ⊗ₘ biprod.inl) ≫ g)
    (hlr : (biprod.inl ⊗ₘ biprod.inr) ≫ f = (biprod.inl ⊗ₘ biprod.inr) ≫ g)
    (hrl : (biprod.inr ⊗ₘ biprod.inl) ≫ f = (biprod.inr ⊗ₘ biprod.inl) ≫ g)
    (hrr : (biprod.inr ⊗ₘ biprod.inr) ≫ f = (biprod.inr ⊗ₘ biprod.inr) ≫ g) : f = g := by
  apply biprodTensorLeft_hom_ext
  · apply biprodTensorRight_hom_ext
    · simpa only [← Category.assoc, ← tensorHom_def'] using hll
    · simpa only [← Category.assoc, ← tensorHom_def'] using hlr
  · apply biprodTensorRight_hom_ext
    · simpa only [← Category.assoc, ← tensorHom_def'] using hrl
    · simpa only [← Category.assoc, ← tensorHom_def'] using hrr

end SerrePositivity.KST.LocalizingInvariants
