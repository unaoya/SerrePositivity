module

public import SerrePositivity.KST.LocalizingInvariants.TensorTripleActionComposition
public import SerrePositivity.KST.LocalizingInvariants.CochainTensorTruncationDesc
public import Mathlib.CategoryTheory.Monoidal.Bimod

/-!
概要：実 dg 双加群の全射商に、降下した左右作用から実双加群構造を与える。
方針：tensor の全射性で各作用則を消去し、元の双加群の三則へ戻す。
規約：商複体と元の射を保持。使われ方：係数射の実 cokernel。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] (A : Mon (Complex R)) (M : Bimod A A)
  {P : Complex R} (e : M.X ⟶ P) [Epi e] (l : A.X ⊗ P ⟶ P) (r : P ⊗ A.X ⟶ P)
  (hl : (A.X ◁ e) ≫ l = M.actLeft ≫ e) (hr : (e ▷ A.X) ≫ r = M.actRight ≫ e)

include e hl in
lemma quotient_one_left : (η[A.X] ▷ P) ≫ l = (λ_ P).hom := by
  have : Epi (𝟙 (𝟙_ (Complex R)) ⊗ₘ e) := TruncationDesc.tensor_epi _ _
  apply (cancel_epi (𝟙 (𝟙_ (Complex R)) ⊗ₘ e)).1
  calc
    _ = (η[A.X] ▷ M.X) ≫ (A.X ◁ e) ≫ l := by
      simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
        Category.id_comp, Category.comp_id]
    _ = (η[A.X] ▷ M.X) ≫ M.actLeft ≫ e := by rw [hl]
    _ = (𝟙 (𝟙_ (Complex R)) ⊗ₘ e) ≫ (λ_ P).hom := by
      rw [← Category.assoc, M.one_actLeft, id_tensorHom, leftUnitor_naturality]

include e hr in
lemma quotient_one_right : (P ◁ η[A.X]) ≫ r = (ρ_ P).hom := by
  have : Epi (e ⊗ₘ 𝟙 (𝟙_ (Complex R))) := TruncationDesc.tensor_epi _ _
  apply (cancel_epi (e ⊗ₘ 𝟙 (𝟙_ (Complex R)))).1
  calc
    _ = (M.X ◁ η[A.X]) ≫ (e ▷ A.X) ≫ r := by
      simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
        Category.id_comp, Category.comp_id]
    _ = (M.X ◁ η[A.X]) ≫ M.actRight ≫ e := by rw [hr]
    _ = (e ⊗ₘ 𝟙 (𝟙_ (Complex R))) ≫ (ρ_ P).hom := by
      rw [← Category.assoc, M.actRight_one, tensorHom_id, rightUnitor_naturality]

include e hl in
lemma quotient_left_assoc : (μ[A.X] ▷ P) ≫ l =
    (α_ A.X A.X P).hom ≫ (A.X ◁ l) ≫ l := by
  have : Epi ((𝟙 A.X ⊗ₘ 𝟙 A.X) ⊗ₘ e) :=
    TruncationDesc.tensor_epi (𝟙 A.X ⊗ₘ 𝟙 A.X) e
  apply (cancel_epi ((𝟙 A.X ⊗ₘ 𝟙 A.X) ⊗ₘ e)).1
  rw [tensorTriple_action_left, tensorTriple_action_right]
  simp only [tensorHom_id, id_tensorHom, id_whiskerRight, Category.id_comp, hl]
  simp only [tensorHom_def', Category.assoc, hl, whiskerLeft_comp]
  rw [whisker_exchange_assoc, hl, ← Category.assoc, M.left_assoc]
  simp only [Category.assoc]

include e hr in
lemma quotient_right_assoc : (P ◁ μ[A.X]) ≫ r =
    (α_ P A.X A.X).inv ≫ (r ▷ A.X) ≫ r := by
  apply (cancel_epi (α_ P A.X A.X).hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have : Epi (e ⊗ₘ 𝟙 A.X) := TruncationDesc.tensor_epi _ _
  have : Epi ((e ⊗ₘ 𝟙 A.X) ⊗ₘ 𝟙 A.X) :=
    TruncationDesc.tensor_epi (e ⊗ₘ 𝟙 A.X) (𝟙 A.X)
  apply (cancel_epi ((e ⊗ₘ 𝟙 A.X) ⊗ₘ 𝟙 A.X)).1
  rw [tensorTriple_action_right, tensorTriple_action_left]
  simp only [tensorHom_id, id_tensorHom, Category.id_comp, hr]
  simp only [tensorHom_def, Category.assoc, hr, comp_whiskerRight]
  simp only [id_whiskerRight, Category.id_comp]
  rw [← whisker_exchange_assoc, hr, ← Category.assoc (M.X ◁ μ[A.X]),
    M.right_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

include e hl hr in
lemma quotient_middle_assoc : (l ▷ A.X) ≫ r =
    (α_ A.X P A.X).hom ≫ (A.X ◁ r) ≫ l := by
  have : Epi (𝟙 A.X ⊗ₘ e) := TruncationDesc.tensor_epi _ _
  have : Epi ((𝟙 A.X ⊗ₘ e) ⊗ₘ 𝟙 A.X) := TruncationDesc.tensor_epi _ _
  apply (cancel_epi ((𝟙 A.X ⊗ₘ e) ⊗ₘ 𝟙 A.X)).1
  rw [tensorTriple_action_left, tensorTriple_action_right]
  simp only [id_tensorHom, tensorHom_id, hl, hr, comp_whiskerRight, whiskerLeft_comp,
    tensorHom_def, tensorHom_def', Category.assoc]
  simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp]
  rw [hr, ← whiskerLeft_comp_assoc, hr, whiskerLeft_comp_assoc, hl,
    ← Category.assoc, M.middle_assoc]
  simp only [Category.assoc]

def dgBimoduleQuotient : Bimod A A where
  X := P
  actLeft := l
  actRight := r
  one_actLeft := quotient_one_left A M e l hl
  actRight_one := quotient_one_right A M e r hr
  left_assoc := quotient_left_assoc A M e l hl
  right_assoc := quotient_right_assoc A M e r hr
  middle_assoc := quotient_middle_assoc A M e l r hl hr

end SerrePositivity.KST.LocalizingInvariants
