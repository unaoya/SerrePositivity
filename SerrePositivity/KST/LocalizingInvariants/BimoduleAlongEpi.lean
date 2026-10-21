module

public import SerrePositivity.KST.LocalizingInvariants.TensorTripleActionComposition
public import Mathlib.CategoryTheory.Monoidal.Bimod

/-!
概要：全射代数射を通って降下した左右作用に、実双加群の三則を供給する。
方針：tensor 全射で作用則を消去し、元の双加群の各作用則へ戻す。
規約：tensor 全射性は適用時に検証。使われ方：Postnikov 層の底への作用の降下。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory
open scoped MonObj
namespace SerrePositivity.KST.LocalizingInvariants
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

def bimoduleAlongEpi {A D : Mon C} (q : A ⟶ D) (M : Bimod A A)
    (l : D.X ⊗ M.X ⟶ M.X) (r : M.X ⊗ D.X ⟶ M.X)
    (hl : (q.hom ▷ M.X) ≫ l = M.actLeft) (hr : (M.X ◁ q.hom) ≫ r = M.actRight)
    [Epi ((q.hom ⊗ₘ q.hom) ⊗ₘ 𝟙 M.X)]
    [Epi ((𝟙 M.X ⊗ₘ q.hom) ⊗ₘ q.hom)]
    [Epi ((q.hom ⊗ₘ 𝟙 M.X) ⊗ₘ q.hom)] : Bimod D D where
  X := M.X
  actLeft := l
  actRight := r
  one_actLeft := by
    rw [← IsMonHom.one_hom q.hom, comp_whiskerRight, Category.assoc, hl, M.one_actLeft]
  actRight_one := by
    rw [← IsMonHom.one_hom q.hom, whiskerLeft_comp, Category.assoc, hr, M.actRight_one]
  left_assoc := by
    apply (cancel_epi ((q.hom ⊗ₘ q.hom) ⊗ₘ 𝟙 M.X)).1
    rw [tensorTriple_action_left, tensorTriple_action_right, ← IsMonHom.mul_hom q.hom]
    simp only [tensorHom_id, comp_whiskerRight_assoc, hl]
    rw [tensorHom_def', Category.assoc, hl]
    exact M.left_assoc
  right_assoc := by
    apply (cancel_epi (α_ M.X D.X D.X).hom).1
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    apply (cancel_epi ((𝟙 M.X ⊗ₘ q.hom) ⊗ₘ q.hom)).1
    rw [tensorTriple_action_right, tensorTriple_action_left, ← IsMonHom.mul_hom q.hom]
    simp only [id_tensorHom, whiskerLeft_comp_assoc, hr]
    rw [tensorHom_def, Category.assoc, hr]
    rw [M.right_assoc, Iso.hom_inv_id_assoc]
  middle_assoc := by
    apply (cancel_epi ((q.hom ⊗ₘ 𝟙 M.X) ⊗ₘ q.hom)).1
    rw [tensorTriple_action_left, tensorTriple_action_right]
    simp only [tensorHom_id, id_tensorHom, hl, hr]
    rw [tensorHom_def, Category.assoc, hr, tensorHom_def', Category.assoc, hl]
    exact M.middle_assoc

end SerrePositivity.KST.LocalizingInvariants
