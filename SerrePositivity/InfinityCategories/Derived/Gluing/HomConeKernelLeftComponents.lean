module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeKernelLeftInclusion
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeModuleLeftInclusions

/-! 標準 kernel 円錐への左包含の source・replacement を実加群の左包含で同定する。 -/
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
local notation "F" => Morita.kernelTensor R D C M
local notation "KX" => dgGluingKernelObject R C D M X
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "k" => dgGluingPostcomposition R C D M X Y Z f
local notation "p" => dgGluingPostcompositionComponents R C D M X Y Z f
local notation "b" => dgGluingHomConeBiproductIso R C D M X Y Z f
local notation "s" => dgGluingHomConeKernelSourceIso R C D M X Y Z f
local notation "Q" => ForgetEnrichment.of (Complex R) (representable R X.right)
local notation "rf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (dgYoneda R D)) (dgGluingConeRightArrow R C D M Y Z f)

/-- source の左包含は、元の右 Hom 射影・Yoneda と同じ加群 Hom 円錐左包含。 -/
lemma dgGluingHomConeKernelIso_inl_source :
    (mappingCone.inl k).comp
      (Cochain.ofHom ((dgGluingHomConeKernelIso R C D M X Y Z f).hom ≫
        dgFunctorCommaSourceHomMap R (RightModule R D) (RightModule R C) F KX L))
      (add_zero (-1)) =
    (Cochain.ofHom (dgGluingRightHomMap R C D M X Y ≫
      yonedaHom R D X.right Y.right)).comp
      (moduleHomConeLeftCochain R D Q rf) (zero_add (-1)) := by
  have hs : (s).hom ≫ biprod.fst =
      biprod.snd ≫ (dgGluingHomConeRightModuleIso R C D M X Y Z f).hom := by
    apply biprod.hom_ext' <;>
      simp [dgGluingHomConeKernelSourceIso, biprod.braiding'_hom]
  rw [dgFunctorCommaSourceHomMap, ← Category.assoc, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain, dgGluingHomConeKernelIso_inl_fst,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, Category.assoc,
    hs, ← Category.assoc]
  rw [Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    dgGluingHomConeBiproductIso_inl_snd]
  simp only [Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [dgGluingHomConeRightModuleIso_inl]
  simp only [dgGluingRightHomMap, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]

local notation "P" => ForgetEnrichment.of (Complex R) (representable R X.left)
local notation "lf" => dgGluingConeLeftArrow R C D M Y Z f

/-- replacement の左包含は、元の左 Hom 射影・Yoneda と同じ加群 Hom 円錐左包含。 -/
lemma dgGluingHomConeKernelIso_inl_replacement :
    (mappingCone.inl k).comp
      (Cochain.ofHom ((dgGluingHomConeKernelIso R C D M X Y Z f).hom ≫
        dgFunctorCommaReplacementHomMap R (RightModule R D) (RightModule R C) F KX L))
      (add_zero (-1)) =
    (Cochain.ofHom (dgGluingLeftHomMap R C D M X Y ≫
      yonedaHom R C X.left Y.left)).comp
      (moduleHomConeLeftCochain R C P lf) (zero_add (-1)) := by
  have hs : (s).hom ≫ biprod.snd =
      biprod.fst ≫ (dgGluingHomConeLeftModuleIso R C D M X Y Z f).hom := by
    apply biprod.hom_ext' <;>
      simp [dgGluingHomConeKernelSourceIso, biprod.braiding'_hom]
  rw [dgFunctorCommaReplacementHomMap, ← Category.assoc, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain, dgGluingHomConeKernelIso_inl_fst,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, Category.assoc,
    hs, ← Category.assoc]
  rw [Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    dgGluingHomConeBiproductIso_inl_fst]
  simp only [Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [dgGluingHomConeLeftModuleIso_inl]
  simp only [dgGluingLeftHomMap, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]

end SerrePositivity.InfinityCategories
