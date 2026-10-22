module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleQuotient
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
概要：実 dg 双加群射の cokernel へ、元の左右作用を降ろす。
方針：tensor の左随伴性による cokernel 保存と、元の作用保存の等式を使う。
規約：元の cokernel 射への可換式を保持。使われ方：係数の商と像の homotopy fiber。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGBimoduleCokernel
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} {M N : Bimod A A} (f : M ⟶ N)

local instance cokernelRightTensorAdjoint : (tensorRight A.X).IsLeftAdjoint :=
  (tensorRightHomAdjunction A.X).isLeftAdjoint

lemma left_zero : (A.X ◁ f.hom) ≫ (N.actLeft ≫ cokernel.π f.hom) = 0 := by
  rw [← Category.assoc, ← f.left_act_hom, Category.assoc, cokernel.condition, comp_zero]

lemma right_zero : (f.hom ▷ A.X) ≫ (N.actRight ≫ cokernel.π f.hom) = 0 := by
  rw [← Category.assoc, ← f.right_act_hom, Category.assoc, cokernel.condition, comp_zero]

def left : A.X ⊗ cokernel f.hom ⟶ cokernel f.hom :=
  (PreservesCokernel.iso (tensorLeft A.X) f.hom).hom ≫
    cokernel.desc (A.X ◁ f.hom) (N.actLeft ≫ cokernel.π f.hom) (left_zero f)

def right : cokernel f.hom ⊗ A.X ⟶ cokernel f.hom :=
  (PreservesCokernel.iso (tensorRight A.X) f.hom).hom ≫
    cokernel.desc (f.hom ▷ A.X) (N.actRight ≫ cokernel.π f.hom) (right_zero f)

lemma projection_left : (A.X ◁ cokernel.π f.hom) ≫ left f = N.actLeft ≫ cokernel.π f.hom := by
  change (tensorLeft A.X).map (cokernel.π f.hom) ≫
    ((PreservesCokernel.iso (tensorLeft A.X) f.hom).hom ≫ _) = _
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

lemma projection_right : (cokernel.π f.hom ▷ A.X) ≫ right f = N.actRight ≫ cokernel.π f.hom := by
  change (tensorRight A.X).map (cokernel.π f.hom) ≫
    ((PreservesCokernel.iso (tensorRight A.X) f.hom).hom ≫ _) = _
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGBimoduleCokernel
