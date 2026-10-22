module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConeNullActionProjections
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConeNullActionPrimitive
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeTensorLeftInclusion
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaCochainExt

/-! 標準 kernel Hom 円錐の左包含は、指定した同じ境界元の全次数後合成。 -/
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
local notation "E" => DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "KX" => dgGluingKernelObject R C D M X
local notation "KY" => dgGluingKernelObject R C D M Y
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "k" => dgGluingPostcomposition R C D M X Y Z f

/-- 三成分を保持する、標準 kernel 円錐の左包含と指定境界元の作用との厳密な一致。 -/
lemma dgGluingHomConeKernelIso_inl :
    (mappingCone.inl k).comp
      (Cochain.ofHom (dgGluingHomConeKernelIso R C D M X Y Z f).hom) (add_zero (-1)) =
    (Cochain.ofHom (dgGluingKernelHomIso R C D M X Y).hom).comp
      ((dgGluingGradedPostcomposition R E KX KY L).f (-1)
        (dgGluingKernelConeNullElement R C D M Y Z f)) (zero_add (-1)) := by
  apply dgGluingCommaCochain_ext R (RightModule R D) (RightModule R C) F KX L
  · simpa only [Cochain.ofHom_comp, Cochain.comp_assoc_of_third_is_zero_cochain,
      Cochain.comp_assoc_of_first_is_zero_cochain] using
      dgGluingKernelConeNullAction_source R C D M X Y Z f
  · simpa only [Cochain.ofHom_comp, Cochain.comp_assoc_of_third_is_zero_cochain,
      Cochain.comp_assoc_of_first_is_zero_cochain] using
      dgGluingKernelConeNullAction_replacement R C D M X Y Z f
  · rw [Cochain.comp_assoc_of_second_is_zero_cochain]
    erw [dgGluingHomConeKernelIso_inl_snd R C D M X Y Z f]
    rw [Cochain.comp_assoc_of_first_is_zero_cochain,
      dgGluingKernelConeNullAction_primitive, Cochain.comp_neg,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, dgGluingKernelHomIso_primitive]
    rw [Cochain.neg_comp, Cochain.comp_assoc_of_third_is_zero_cochain,
      dgGluingHomConeRightTensorTargetIso_inl,
      ← Cochain.comp_assoc_of_second_is_zero_cochain]
    rfl

end SerrePositivity.InfinityCategories
