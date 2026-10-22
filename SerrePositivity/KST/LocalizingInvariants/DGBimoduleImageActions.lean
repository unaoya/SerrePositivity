module

public import SerrePositivity.KST.LocalizingInvariants.BimoduleSubobject
public import SerrePositivity.KST.LocalizingInvariants.CochainTensorTruncationDesc
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
概要：実 dg 双加群射の複体圏の像へ、左右の作用を降ろす。
方針：像の全射・単射分解と tensor の全射性で、可換正方形の一意な lift を取る。
規約：像の包含へ合成して元の作用を回収。使われ方：LT の係数の像への制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGBimoduleImage
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} {M N : Bimod A A} (f : M ⟶ N)

lemma leftEpi : Epi (A.X ◁ factorThruImage f.hom) := by
  simpa only [id_tensorHom] using TruncationDesc.tensor_epi (𝟙 A.X) (factorThruImage f.hom)

lemma rightEpi : Epi (factorThruImage f.hom ▷ A.X) := by
  simpa only [tensorHom_id] using TruncationDesc.tensor_epi (factorThruImage f.hom) (𝟙 A.X)

def leftSquare : CommSq (M.actLeft ≫ factorThruImage f.hom)
    (A.X ◁ factorThruImage f.hom) (image.ι f.hom) ((A.X ◁ image.ι f.hom) ≫ N.actLeft) := by
  constructor
  rw [Category.assoc, image.fac, ← Category.assoc, ← whiskerLeft_comp,
    image.fac, f.left_act_hom]

def rightSquare : CommSq (M.actRight ≫ factorThruImage f.hom)
    (factorThruImage f.hom ▷ A.X) (image.ι f.hom) ((image.ι f.hom ▷ A.X) ≫ N.actRight) := by
  constructor
  rw [Category.assoc, image.fac, ← Category.assoc, ← comp_whiskerRight,
    image.fac, f.right_act_hom]

def left : A.X ⊗ image f.hom ⟶ image f.hom := by
  have := leftEpi f
  have : StrongEpi (A.X ◁ factorThruImage f.hom) := strongEpi_of_epi _
  exact (leftSquare f).lift

def right : image f.hom ⊗ A.X ⟶ image f.hom := by
  have := rightEpi f
  have : StrongEpi (factorThruImage f.hom ▷ A.X) := strongEpi_of_epi _
  exact (rightSquare f).lift

lemma left_inclusion : left f ≫ image.ι f.hom = (A.X ◁ image.ι f.hom) ≫ N.actLeft := by
  have := leftEpi f
  have : StrongEpi (A.X ◁ factorThruImage f.hom) := strongEpi_of_epi _
  exact (leftSquare f).fac_right

lemma right_inclusion : right f ≫ image.ι f.hom = (image.ι f.hom ▷ A.X) ≫ N.actRight := by
  have := rightEpi f
  have : StrongEpi (factorThruImage f.hom ▷ A.X) := strongEpi_of_epi _
  exact (rightSquare f).fac_right

lemma projection_left : (A.X ◁ factorThruImage f.hom) ≫ left f =
    M.actLeft ≫ factorThruImage f.hom := by
  have := leftEpi f
  have : StrongEpi (A.X ◁ factorThruImage f.hom) := strongEpi_of_epi _
  exact (leftSquare f).fac_left

lemma projection_right : (factorThruImage f.hom ▷ A.X) ≫ right f =
    M.actRight ≫ factorThruImage f.hom := by
  have := rightEpi f
  have : StrongEpi (factorThruImage f.hom ▷ A.X) := strongEpi_of_epi _
  exact (rightSquare f).fac_left

end SerrePositivity.KST.LocalizingInvariants.DGBimoduleImage
