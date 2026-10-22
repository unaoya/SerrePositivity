module

public import SerrePositivity.KST.LocalizingInvariants.CochainKernelHomology

/-!
概要：直和の第二射影の kernel を、元の正符号・負符号の第一包含で実現する。
方針：元の二射影で普遍 lift を証明し、元の kernel lift が同型であることを得る。
規約：負符号を保持。使われ方：平方零代数の零切断の mapping cocone。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] (P T : Complex R)

def cochainBiprodInl_isKernel :
    IsLimit (KernelFork.ofι (f := (biprod.snd : P ⊞ T ⟶ T))
      (biprod.inl : P ⟶ P ⊞ T) (by simp)) := by
  refine KernelFork.IsLimit.ofι _ _ (fun a _ => a ≫ biprod.fst) ?_ ?_
  · intro W a ha
    apply biprod.hom_ext <;> simp [Category.assoc, ha]
  · intro W a ha m hm
    have h := congrArg (fun t => t ≫ (biprod.fst : P ⊞ T ⟶ P)) hm
    simpa only [Category.assoc, biprod.inl_fst, Category.comp_id] using h

def cochainBiprodNegInl_isKernel :
    IsLimit (KernelFork.ofι (f := (biprod.snd : P ⊞ T ⟶ T))
      (-(biprod.inl : P ⟶ P ⊞ T)) (by simp)) :=
  IsKernel.isoKernel (biprod.snd : P ⊞ T ⟶ T) (-(biprod.inl : P ⟶ P ⊞ T))
    (cochainBiprodInl_isKernel P T) (-Iso.refl P) (by simp)

def cochainBiprodNegInlKernelIso :=
  (cochainBiprodNegInl_isKernel P T).conePointUniqueUpToIso
    (kernelIsKernel (biprod.snd : P ⊞ T ⟶ T))

lemma cochainBiprodNegInlKernelIso_hom : (cochainBiprodNegInlKernelIso P T).hom =
    kernel.lift (biprod.snd : P ⊞ T ⟶ T) (-(biprod.inl : P ⟶ P ⊞ T)) (by simp) := by
  apply (cancel_mono (kernel.ι (biprod.snd : P ⊞ T ⟶ T))).1
  rw [kernel.lift_ι]
  exact (cochainBiprodNegInl_isKernel P T).conePointUniqueUpToIso_hom_comp
    (kernelIsKernel _) WalkingParallelPair.zero

lemma cochainBiprodNegInlKernelLift_isIso :
    IsIso (kernel.lift (biprod.snd : P ⊞ T ⟶ T) (-(biprod.inl : P ⟶ P ⊞ T)) (by simp)) := by
  rw [← cochainBiprodNegInlKernelIso_hom]
  infer_instance

end SerrePositivity.KST.LocalizingInvariants
