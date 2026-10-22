module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleCokernel
public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleImageSupport
public import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
概要：実係数像の包含は、元の係数 cokernel 射の kernel である。
方針：構成済みの鎖写像 lift と包含の単射性で、元の像を頂点とする普遍性を証明。
規約：同型な kernel の存在だけで代用しない。使われ方：平方零係数の実 pullback。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGBimoduleImage
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} {M N : Bimod A A} (f : M ⟶ N)

lemma inclusion_cokernel : (inclusion f).hom ≫ (DGBimoduleCokernel.projection f).hom = 0 := by
  have := projection_epi f
  apply (cancel_epi (projection f).hom).1
  rw [← Category.assoc]
  have hf : (projection f).hom ≫ (inclusion f).hom = f.hom :=
    congrArg Bimod.Hom.hom (projection_inclusion f)
  rw [hf, DGBimoduleCokernel.condition, comp_zero]

def inclusion_isKernel : IsLimit (KernelFork.ofι (inclusion f).hom (inclusion_cokernel f)) := by
  have := inclusion_mono f
  refine KernelFork.IsLimit.ofι _ _ (fun a ha => chainLift f a ha) ?_ ?_
  · intro K a ha
    exact chainLift_inclusion f a ha
  · intro K a ha m hm
    apply (cancel_mono (inclusion f).hom).1
    exact hm.trans (chainLift_inclusion f a ha).symm

def shortComplex : ShortComplex (Complex R) :=
  ShortComplex.mk (inclusion f).hom (DGBimoduleCokernel.projection f).hom (inclusion_cokernel f)

lemma shortComplex_shortExact : (shortComplex f).ShortExact := by
  have := inclusion_mono f
  have := DGBimoduleCokernel.projection_epi f
  exact { exact := (shortComplex f).exact_of_f_is_kernel (inclusion_isKernel f)
          mono_f := by change Mono (inclusion f).hom; infer_instance
          epi_g := by change Epi (DGBimoduleCokernel.projection f).hom; infer_instance }

end SerrePositivity.KST.LocalizingInvariants.DGBimoduleImage
