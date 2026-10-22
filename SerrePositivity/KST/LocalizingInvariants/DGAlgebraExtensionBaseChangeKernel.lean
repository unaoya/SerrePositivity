module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraExtensionBaseChange

/-!
概要：底変更後の実拡大の kernel を、元の実 kernel と包含・射影を保って同定する。
方針：元の pullback 正方形の kernel 射の実逆を使い、元の零脚と包含を回収する。
規約：底射への準同型性は不要。使われ方：Postnikov 係数層の底変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.ExtensionBaseChange
variable (R : Type u) [CommRing R] {P U B : Mon (Complex R)} (b : P ⟶ B) (q : U ⟶ B)

def kernelMap : kernel (base R b q).hom ⟶ kernel q.hom :=
  kernel.map _ _ (upper R b q).hom b.hom (congrArg Mon.Hom.hom (condition R b q))

instance kernelMap_isIso : IsIso (kernelMap R b q) :=
  isIso_kernel_map_of_isPullback (IsPullback.of_hasPullback b.hom q.hom)

def kernelIso : kernel (base R b q).hom ≅ kernel q.hom := asIso (kernelMap R b q)

lemma kernelMap_inclusion : kernelMap R b q ≫ kernel.ι q.hom =
    kernel.ι (base R b q).hom ≫ (upper R b q).hom := kernel.lift_ι _ _ _

def kernelLift : kernel q.hom ⟶ (algebra R b q).X :=
  (kernelIso R b q).inv ≫ kernel.ι (base R b q).hom

lemma kernelLift_upper : kernelLift R b q ≫ (upper R b q).hom = kernel.ι q.hom := by
  change ((kernelIso R b q).inv ≫ kernel.ι (base R b q).hom) ≫ (upper R b q).hom = _
  rw [Category.assoc, ← kernelMap_inclusion, ← Category.assoc]
  exact (Iso.inv_hom_id_assoc (kernelIso R b q) (kernel.ι q.hom))

lemma kernelLift_base : kernelLift R b q ≫ (base R b q).hom = 0 := by
  rw [kernelLift, Category.assoc, kernel.condition, comp_zero]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.ExtensionBaseChange
