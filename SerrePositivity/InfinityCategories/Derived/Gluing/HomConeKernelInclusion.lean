module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeSplitInclusion
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConeRightArrow
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaStrictPostcomposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPostCocone

/-! 元の Hom 円錐の右包含を、kernel comma の実閉円錐包含による後合成と同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "k" => dgGluingPostcomposition R C D M X Y Z f
local notation "ν" => dgGluingDifference R C D M X Z
local notation "l" => dgGluingHomConeLeftArrow R C D M X Y Z f
local notation "r" => dgGluingHomConeRightArrow R C D M X Y Z f
local notation "F" => Morita.kernelTensor R D C M
local notation "KX" => dgGluingKernelObject R C D M X
local notation "KZ" => dgGluingKernelObject R C D M Z
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "i" => dgGluingKernelConeInr R C D M Y Z f

/-- 二つの Hom 円錐の右包含は、元の二成分の Yoneda と加群円錐包含の後合成に一致。 -/
lemma dgGluingHomConeKernelSourceIso_inr :
    biprod.map (mappingCone.inr l) (mappingCone.inr r) ≫
      (dgGluingHomConeKernelSourceIso R C D M X Y Z f).hom =
    (dgGluingKernelHomComponentsIso R C D M X Z).hom ≫
      dgGluingCommaPostComponents R (RightModule R D) (RightModule R C) F KX KZ L i := by
  simp only [dgGluingCommaPostComponents, dgGluingKernelConeInr_source,
    dgGluingKernelConeInr_replacement]
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp only [dgGluingHomConeKernelSourceIso, dgGluingKernelHomComponentsIso_hom,
      biprod.braiding'_hom, dgGluingHomConeLeftModuleIso_inr,
      dgGluingHomConeRightModuleIso_inr, Iso.trans_hom, biprod.mapIso_hom,
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
    mappingCone.inr k ≫ (dgGluingHomConeKernelIso R C D M X Y Z f).hom ≫
      mappingCocone.fst (dgFunctorCommaDifference R (RightModule R D) (RightModule R C)
        F KX L) =
    (dgGluingKernelHomIso R C D M X Z).hom ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) KX) i ≫
        mappingCocone.fst (dgFunctorCommaDifference R (RightModule R D) (RightModule R C)
          F KX L) := by
  simp only [dgGluingHomConeKernelIso, Iso.trans_hom, complexMappingCoconeMapIso,
    Category.assoc]
  rw [complexMappingCoconeMap_fst]
  have he := congrArg (fun a => a ≫
    (dgGluingHomConeKernelSourceIso R C D M X Y Z f).hom)
    (dgGluingHomConeSplitIso_inr_fst R C D M X Y Z f)
  simp only [Category.assoc] at he
  rw [he, dgGluingHomConeKernelSourceIso_inr,
    dgGluingCommaPost_fst R (RightModule R D) (RightModule R C) F KX KZ L i]
  simp only [dgGluingKernelHomIso, complexMappingCoconeMapIso, ← Category.assoc,
    complexMappingCoconeMap_fst]

/-- 右包含の第三 cochain は、同じ kernel 係数写像と tensor 像の包含の後合成。 -/
lemma dgGluingHomConeKernelIso_inr_snd :
    (Cochain.ofHom (mappingCone.inr k ≫
      (dgGluingHomConeKernelIso R C D M X Y Z f).hom)).comp
      (dgFunctorCommaPrimitive R (RightModule R D) (RightModule R C) F KX L)
      (zero_add (-1)) =
    (dgGluingHomPrimitive R C D M X Z).comp
      (Cochain.ofHom ((dgGluingKernelHomTargetIso R C D M X Z).hom ≫
        eHomWhiskerLeft (Complex R)
          (ForgetEnrichment.of (Complex R) (representable R X.left))
          (dgGluingCommaPostImageArrow R (RightModule R D) (RightModule R C) F KZ L i)))
      (add_zero (-1)) := by
  simp only [dgGluingHomConeKernelIso, Iso.trans_hom, complexMappingCoconeMapIso,
    dgFunctorCommaPrimitive, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [complexMappingCoconeMap_snd, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.ofHom_comp, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    dgGluingHomConeSplitIso_inr_snd,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
    dgGluingHomConeRightTensorTargetIso_inr R C D M X Y Z f]
  rw [dgGluingCommaPostImageArrow_eq R (RightModule R D) (RightModule R C) F KZ L i,
    dgGluingKernelConeInr_source]
  rw [Cochain.ofHom_comp]
  rfl

end SerrePositivity.InfinityCategories
