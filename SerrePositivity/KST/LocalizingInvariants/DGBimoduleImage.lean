module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleImageActions

/-!
概要：実 dg 双加群射の像と、その実双加群の全射・単射分解を構成する。
方針：複体圏の像上の左右作用を、包含の単射性で双加群の三則へ移す。
規約：underlying の元の像分解を保持。使われ方：Postnikov の係数の像。
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

def obj : Bimod A A :=
  bimoduleSubobject A N (image.ι f.hom) (left f) (right f)
    (left_inclusion f) (right_inclusion f)

def inclusion : obj f ⟶ N where
  hom := image.ι f.hom
  left_act_hom := left_inclusion f
  right_act_hom := right_inclusion f

def projection : M ⟶ obj f where
  hom := factorThruImage f.hom
  left_act_hom := (projection_left f).symm
  right_act_hom := (projection_right f).symm

lemma projection_inclusion : projection f ≫ inclusion f = f := by
  apply Bimod.Hom.ext
  exact image.fac f.hom

lemma inclusion_mono : Mono (inclusion f).hom := by
  change Mono (image.ι f.hom)
  infer_instance
lemma projection_epi : Epi (projection f).hom := by
  change Epi (factorThruImage f.hom)
  infer_instance

end SerrePositivity.KST.LocalizingInvariants.DGBimoduleImage
