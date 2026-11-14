module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.HomConeTargetComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Objects.KernelCommaObjects

/-! gluing の実 Hom 円錐を、同じ通常 kernel の加群 comma 内の実 Hom と同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "l" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftArrow R C D M X Y Z f
local notation "r" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightArrow R C D M X Y Z f
local notation "F" => Morita.kernelTensor R D C M
local notation "B" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M X
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeObject R C D M Y Z f
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R (RightModule R D) (RightModule R C) F B K

/-- 左右 Hom 円錐を、同じ加群 comma の source・replacement の全 Hom へ送る同型。 -/
def dgGluingHomConeKernelSourceIso : mappingCone l ⊞ mappingCone r ≅
    homObject R (RightModule R D) (B).source (K).source ⊞
      homObject R (RightModule R C) (B).replacement (K).replacement :=
  biprod.braiding' (mappingCone l) (mappingCone r) ≪≫
    biprod.mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightModuleIso R C D M X Y Z f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftModuleIso R C D M X Y Z f)

/-- 両成分の Hom 円錐比較は、元の係数と同じ加群 comma の差を厳密に結ぶ。 -/
lemma dgGluingHomConeKernel_square :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitCoefficient R C D M X Y Z f ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorTargetIso R C D M X Y Z f).hom =
    (dgGluingHomConeKernelSourceIso R C D M X Y Z f).hom ≫ d := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitCoefficient_eq]
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc_assoc, dgGluingHomConeKernelSourceIso, Iso.trans_hom,
      biprod.braiding'_hom, biprod.mapIso_hom, biprod.inl_desc_assoc, biprod.inr_map_assoc,
      Category.assoc]
    erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeDifference_inr, Preadditive.comp_neg]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftCoefficient_kernel_module R C D M X Y Z f
  · simp only [biprod.inr_desc_assoc, dgGluingHomConeKernelSourceIso, Iso.trans_hom,
      biprod.braiding'_hom, biprod.mapIso_hom, biprod.inr_desc_assoc, biprod.inl_map_assoc,
      Category.assoc]
    erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeDifference_inl]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightCoefficient_kernel_module R C D M X Y Z f

/-- 元の gluing の実 Hom 後合成の円錐は、標準加群円錐への加群 comma の全 Hom に実鎖同型。 -/
def dgGluingHomConeKernelIso :
    mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f) ≅
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) F B K :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitIso R C D M X Y Z f ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitCoefficient R C D M X Y Z f) d
      (dgGluingHomConeKernelSourceIso R C D M X Y Z f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorTargetIso R C D M X Y Z f)
      (dgGluingHomConeKernel_square R C D M X Y Z f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
