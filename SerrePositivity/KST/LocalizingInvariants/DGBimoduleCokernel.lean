module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleCokernelActions

/-!
概要：実 dg 双加群射の cokernel と、元の次数全射な商射を実双加群で構成する。
方針：複体の cokernel 上の作用に検証した全射商の作用則を適用する。
規約：underlying の元の cokernel 射を保持。使われ方：平方零係数の商。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGBimoduleCokernel
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} {M N : Bimod A A} (f : M ⟶ N)

def obj : Bimod A A := dgBimoduleQuotient A N (cokernel.π f.hom)
  (left f) (right f) (projection_left f) (projection_right f)

def projection : N ⟶ obj f where
  hom := cokernel.π f.hom
  left_act_hom := (projection_left f).symm
  right_act_hom := (projection_right f).symm

lemma projection_epi : Epi (projection f).hom := by
  change Epi (cokernel.π f.hom)
  infer_instance

lemma condition : f.hom ≫ (projection f).hom = 0 := cokernel.condition f.hom

end SerrePositivity.KST.LocalizingInvariants.DGBimoduleCokernel
