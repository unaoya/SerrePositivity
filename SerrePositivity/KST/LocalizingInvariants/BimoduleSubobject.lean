module

public import SerrePositivity.KST.LocalizingInvariants.TensorTripleActionComposition
public import Mathlib.CategoryTheory.Monoidal.Bimod

/-!
概要：実双加群への単射と作用の因子分解から、元の部分対象に双加群構造を与える。
方針：単射で各作用則を消去し、元の双加群の単位・結合則を三重 tensor に移す。
規約：可換性を要求しない。使われ方：実双加群射の像と derivation の係数制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory
open scoped MonObj
namespace SerrePositivity.KST.LocalizingInvariants
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

def bimoduleSubobject (A : Mon C) (M : Bimod A A) {P : C} (i : P ⟶ M.X) [Mono i]
    (l : A.X ⊗ P ⟶ P) (r : P ⊗ A.X ⟶ P)
    (hl : l ≫ i = (A.X ◁ i) ≫ M.actLeft)
    (hr : r ≫ i = (i ▷ A.X) ≫ M.actRight) : Bimod A A where
  X := P
  actLeft := l
  actRight := r
  one_actLeft := by
    apply (cancel_mono i).1
    calc
      ((η[A.X] ▷ P) ≫ l) ≫ i = (η[A.X] ⊗ₘ i) ≫ M.actLeft := by
        simp only [Category.assoc, hl, ← id_tensorHom, ← tensorHom_id,
          tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
      _ = (𝟙_ C ◁ i) ≫ (η[A.X] ▷ M.X) ≫ M.actLeft := by
        simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, Category.comp_id]
      _ = (λ_ P).hom ≫ i := by rw [M.one_actLeft, leftUnitor_naturality]
  actRight_one := by
    apply (cancel_mono i).1
    calc
      ((P ◁ η[A.X]) ≫ r) ≫ i = (i ⊗ₘ η[A.X]) ≫ M.actRight := by
        simp only [Category.assoc, hr, ← id_tensorHom, ← tensorHom_id,
          tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
      _ = (i ▷ 𝟙_ C) ≫ (M.X ◁ η[A.X]) ≫ M.actRight := by
        simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, Category.comp_id]
      _ = (ρ_ P).hom ≫ i := by rw [M.actRight_one, rightUnitor_naturality]
  left_assoc := by
    apply (cancel_mono i).1
    have h := congrArg (fun f ↦ ((𝟙 A.X ⊗ₘ 𝟙 A.X) ⊗ₘ i) ≫ f) M.left_assoc
    rw [tensorTriple_action_left, tensorTriple_action_right] at h
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp] at h
    simpa only [Category.assoc, hl, ← id_tensorHom, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id] using h
  right_assoc := by
    apply (cancel_epi (α_ P A.X A.X).hom).1
    apply (cancel_mono i).1
    have h₀ : (M.actRight ▷ A.X) ≫ M.actRight =
        (α_ M.X A.X A.X).hom ≫ (M.X ◁ μ[A.X]) ≫ M.actRight := by
      rw [M.right_assoc, Iso.hom_inv_id_assoc]
    have h := congrArg (fun f ↦ ((i ⊗ₘ 𝟙 A.X) ⊗ₘ 𝟙 A.X) ≫ f) h₀
    rw [tensorTriple_action_left, tensorTriple_action_right] at h
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp] at h
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, hr, ← id_tensorHom,
      ← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp,
      Category.comp_id] using h.symm
  middle_assoc := by
    apply (cancel_mono i).1
    have h := congrArg (fun f ↦ ((𝟙 A.X ⊗ₘ i) ⊗ₘ 𝟙 A.X) ≫ f) M.middle_assoc
    rw [tensorTriple_action_left, tensorTriple_action_right] at h
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp] at h
    simpa only [Category.assoc, hl, hr, ← id_tensorHom, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id] using h

end SerrePositivity.KST.LocalizingInvariants
