module

public import SerrePositivity.KST.LocalizingInvariants.BimoduleAlongEpi

/-!
概要：実代数射に沿う双加群の左右同時の制限を構成する。
方針：作用を代数射と合成し、三つの作用則を tensor の自然性で制限する。
規約：代数射の単位・積保存を使う。使われ方：Postnikov 層を元の代数上で扱う。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory
open scoped MonObj
namespace SerrePositivity.KST.LocalizingInvariants
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

def bimoduleRestrict {A D : Mon C} (q : A ⟶ D) (M : Bimod D D) : Bimod A A where
  X := M.X
  actLeft := (q.hom ▷ M.X) ≫ M.actLeft
  actRight := (M.X ◁ q.hom) ≫ M.actRight
  one_actLeft := by
    rw [← Category.assoc, ← comp_whiskerRight, IsMonHom.one_hom, M.one_actLeft]
  actRight_one := by
    rw [← Category.assoc, ← whiskerLeft_comp, IsMonHom.one_hom, M.actRight_one]
  left_assoc := by
    have h := congrArg (fun f ↦ ((q.hom ⊗ₘ q.hom) ⊗ₘ 𝟙 M.X) ≫ f) M.left_assoc
    rw [tensorTriple_action_left, tensorTriple_action_right] at h
    simpa only [Category.assoc, ← id_tensorHom, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc, ← IsMonHom.mul_hom,
      Category.id_comp, Category.comp_id] using h
  right_assoc := by
    apply (cancel_epi (α_ M.X A.X A.X).hom).1
    have h₀ : (M.actRight ▷ D.X) ≫ M.actRight =
        (α_ M.X D.X D.X).hom ≫ (M.X ◁ μ[D.X]) ≫ M.actRight := by
      rw [M.right_assoc, Iso.hom_inv_id_assoc]
    have h := congrArg (fun f ↦ ((𝟙 M.X ⊗ₘ q.hom) ⊗ₘ q.hom) ≫ f) h₀
    rw [tensorTriple_action_left, tensorTriple_action_right] at h
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, ← id_tensorHom, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc, ← IsMonHom.mul_hom,
      Category.id_comp, Category.comp_id] using h.symm
  middle_assoc := by
    have h := congrArg (fun f ↦ ((q.hom ⊗ₘ 𝟙 M.X) ⊗ₘ q.hom) ≫ f) M.middle_assoc
    rw [tensorTriple_action_left, tensorTriple_action_right] at h
    simpa only [Category.assoc, ← id_tensorHom, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id] using h

end SerrePositivity.KST.LocalizingInvariants
