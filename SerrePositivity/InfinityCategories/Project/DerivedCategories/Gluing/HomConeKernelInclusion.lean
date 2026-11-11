module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomConeSplitInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelConeRightArrow
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaStrictPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaPostCocone

/-! 元の Hom 円錐の右包含を、kernel comma の実閉円錐包含による後合成と同定する。 -/
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
local notation "k" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f
local notation "ν" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Z
local notation "l" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftArrow R C D M X Y Z f
local notation "r" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightArrow R C D M X Y Z f
local notation "F" => Morita.kernelTensor R D C M
local notation "KX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M X
local notation "KZ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M Z
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeObject R C D M Y Z f
local notation "i" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeInr R C D M Y Z f

/-- 二つの Hom 円錐の右包含は、元の二成分の Yoneda と加群円錐包含の後合成に一致。 -/
lemma dgGluingHomConeKernelSourceIso_inr :
    biprod.map (mappingCone.inr l) (mappingCone.inr r) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelSourceIso R C D M X Y Z f).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomComponentsIso R C D M X Z).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPostComponents R (RightModule R D) (RightModule R C) F KX KZ L i := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPostComponents, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeInr_source,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeInr_replacement]
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelSourceIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomComponentsIso_hom,
      biprod.braiding'_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftModuleIso_inr,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightModuleIso_inr, Iso.trans_hom, biprod.mapIso_hom,
      biprod.inl_map_assoc, biprod.inr_map_assoc, Category.assoc,
      biprod.inl_desc_assoc, biprod.inr_desc_assoc, biprod.map_fst, biprod.map_snd,
      EnrichedFunctor.forget_obj, ForgetEnrichment.to_of, EnrichedFunctor.forget_map,
      biprod.inl_fst_assoc, biprod.inl_snd_assoc, biprod.inr_fst_assoc,
      biprod.inr_snd_assoc, zero_comp, comp_zero]
  all_goals
    first | erw [biprod.lift_fst_assoc] | erw [biprod.lift_snd_assoc]
    simp only [← Category.assoc, biprod.inl_fst, biprod.inl_snd, biprod.inr_fst,
      biprod.inr_snd, Category.id_comp, zero_comp]
  all_goals rfl

/-- 右包含の第一成分は、同じ kernel 閉包含の後合成と一致。 -/
lemma dgGluingHomConeKernelIso_inr_fst :
    mappingCone.inr k ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso R C D M X Y Z f).hom ≫
      mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R (RightModule R D) (RightModule R C)
        F KX L) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso R C D M X Z).hom ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) KX) i ≫
        mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R (RightModule R D) (RightModule R C)
          F KX L) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso,
    Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst]
  have he := congrArg (fun a => a ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelSourceIso R C D M X Y Z f).hom)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitIso_inr_fst R C D M X Y Z f)
  simp only [Category.assoc] at he
  rw [he, dgGluingHomConeKernelSourceIso_inr,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPost_fst R (RightModule R D) (RightModule R C) F KX KZ L i]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst]

/-- 右包含の第三 cochain は、同じ kernel 係数写像と tensor 像の包含の後合成。 -/
lemma dgGluingHomConeKernelIso_inr_snd :
    (Cochain.ofHom (mappingCone.inr k ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso R C D M X Y Z f).hom)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R (RightModule R D) (RightModule R C) F KX L)
      (zero_add (-1)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Z).comp
      (Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomTargetIso R C D M X Z).hom ≫
        eHomWhiskerLeft (Complex R)
          (ForgetEnrichment.of (Complex R) (representable R X.left))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPostImageArrow R (RightModule R D) (RightModule R C) F KZ L i)))
      (add_zero (-1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeKernelIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.ofHom_comp, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeSplitIso_inr_snd,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorTargetIso_inr R C D M X Y Z f]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPostImageArrow_eq R (RightModule R D) (RightModule R C) F KZ L i,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeInr_source]
  rw [Cochain.ofHom_comp]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
