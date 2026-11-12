module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomConeSplitLeftInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomConeKernelModel

/-! 標準 kernel 円錐への Hom 比較の次数 −1 左包含の二成分。 -/
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
local notation "k" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f
local notation "μ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents R C D M X Y Z f
local notation "b" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBiproductIso R C D M X Y Z f
local notation "s" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelSourceIso R C D M X Y Z f
local notation "t" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorTargetIso R C D M X Y Z f
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeObject R C D M Y Z f)

/-- kernel Hom の第一成分は、元の第一射影と左右の同じ円錐比較の合成。 -/
lemma dgGluingHomConeKernelIso_inl_fst :
    (mappingCone.inl k).comp
      (Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso R C D M X Y Z f).hom ≫
        mappingCocone.fst d)) (add_zero (-1)) =
    ((Cochain.ofHom (mappingCocone.fst μ)).comp (mappingCone.inl p)
      (zero_add (-1))).comp (Cochain.ofHom ((b).hom ≫ (s).hom)) (add_zero (-1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso,
    Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst, ← Category.assoc, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitIso_inl_fst]
  rw [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]

/-- kernel Hom の第三 cochain は、元の第三成分と係数左包含の合成の負。 -/
lemma dgGluingHomConeKernelIso_inl_snd :
    (mappingCone.inl k).comp
      ((Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso R C D M X Y Z f).hom).comp
        (mappingCocone.snd d) (zero_add (-1))) (by omega : -1 + -1 = -2) =
    (-(mappingCocone.snd μ).comp
      (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeAction R C D M X Y Z f))
      (by omega : -1 + -1 = -2)).comp (Cochain.ofHom (t).hom) (add_zero (-2)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso,
    Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_third_is_zero_cochain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitIso_inl_snd]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
