module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelConeNullActionProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelConeNullActionPrimitive
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomConeTensorLeftInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaCochainExt

/-! 標準 kernel Hom 円錐の左包含は、指定した同じ境界元の全次数後合成。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "F" => Morita.kernelTensor R D C M
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "KX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M X
local notation "KY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M Y
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeObject R C D M Y Z f
local notation "k" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f

/-- 三成分を保持する、標準 kernel 円錐の左包含と指定境界元の作用との厳密な一致。 -/
lemma dgGluingHomConeKernelIso_inl :
    (mappingCone.inl k).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso R C D M X Y Z f).hom) (add_zero (-1)) =
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso R C D M X Y).hom).comp
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition R E KX KY L).f (-1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullElement R C D M Y Z f)) (zero_add (-1)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaCochain_ext R (RightModule R D) (RightModule R C) F KX L
  · simpa only [Cochain.ofHom_comp, Cochain.comp_assoc_of_third_is_zero_cochain,
      Cochain.comp_assoc_of_first_is_zero_cochain] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullAction_source R C D M X Y Z f
  · simpa only [Cochain.ofHom_comp, Cochain.comp_assoc_of_third_is_zero_cochain,
      Cochain.comp_assoc_of_first_is_zero_cochain] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullAction_replacement R C D M X Y Z f
  · rw [Cochain.comp_assoc_of_second_is_zero_cochain]
    erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso_inl_snd R C D M X Y Z f]
    rw [Cochain.comp_assoc_of_first_is_zero_cochain,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullAction_primitive, Cochain.comp_neg,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso_primitive]
    rw [Cochain.neg_comp, Cochain.comp_assoc_of_third_is_zero_cochain,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorTargetIso_inl,
      ← Cochain.comp_assoc_of_second_is_zero_cochain]
    rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
