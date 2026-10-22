module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConeStrictPrimitive

/-! Hom 円錐の右包含と kernel comma の実閉包含による後合成との厳密な比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "F" => Morita.kernelTensor R D C M
local notation "KX" => dgGluingKernelObject R C D M X
local notation "KZ" => dgGluingKernelObject R C D M Z
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "i" => dgGluingKernelConeInr R C D M Y Z f

/-- 元の Hom 円錐の右包含は、同じ kernel Hom 比較と実閉包含の後合成に厳密に一致。 -/
lemma dgGluingHomConeKernelIso_inr :
    mappingCone.inr (dgGluingPostcomposition R C D M X Y Z f) ≫
      (dgGluingHomConeKernelIso R C D M X Y Z f).hom =
    (dgGluingKernelHomIso R C D M X Z).hom ≫
      dgGluingKernelConePost R C D M X Y Z f := by
  apply dgFunctorCommaHom_ext R (RightModule R D) (RightModule R C) F KX L
    (dgGluingHomComplex R C D M X Z)
  · have he := congrArg (fun a => a ≫ Limits.biprod.fst)
      (dgGluingHomConeKernelIso_inr_fst R C D M X Y Z f)
    exact he
  · have he := congrArg (fun a => a ≫ Limits.biprod.snd)
      (dgGluingHomConeKernelIso_inr_fst R C D M X Y Z f)
    exact he
  · exact (dgGluingHomConeKernelIso_inr_snd R C D M X Y Z f).trans
      (dgGluingKernelConeInr_post_primitive R C D M X Y Z f).symm

end SerrePositivity.InfinityCategories
