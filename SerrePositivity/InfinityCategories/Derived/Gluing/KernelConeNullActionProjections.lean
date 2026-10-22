module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConeNullElementComponents
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaGradedPostProjections

/-! 標準 Hom 円錐の左包含と指定 kernel 境界元の作用は、両 Hom 射影で一致する。 -/
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
local notation "g" => dgGluingKernelConeNullElement R C D M Y Z f


/-- 左包含と指定元の作用は、source 射影で同じ実加群円錐の左包含になる。 -/
lemma dgGluingKernelConeNullAction_source :
    (mappingCone.inl k).comp
      (Cochain.ofHom ((dgGluingHomConeKernelIso R C D M X Y Z f).hom ≫
        dgFunctorCommaSourceHomMap R (RightModule R D) (RightModule R C) F KX L))
      (add_zero (-1)) =
    (Cochain.ofHom (dgGluingKernelHomIso R C D M X Y).hom).comp
      (((dgGluingGradedPostcomposition R E KX KY L).f (-1)
        (dgGluingKernelConeNullElement R C D M Y Z f)).comp (Cochain.ofHom
        (dgFunctorCommaSourceHomMap R (RightModule R D) (RightModule R C) F KX L))
        (add_zero (-1))) (zero_add (-1)) := by
  rw [dgGluingHomConeKernelIso_inl_source]
  erw [dgGluingCommaGradedPost_source R (RightModule R D) (RightModule R C) F KX KY L g]
  rw [dgGluingKernelConeNullElement_source,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    dgGluingKernelHomIso_right]
  rfl

/-- 同じ二つの cochain は、replacement 射影でも同じ左包含になる。 -/
lemma dgGluingKernelConeNullAction_replacement :
    (mappingCone.inl k).comp
      (Cochain.ofHom ((dgGluingHomConeKernelIso R C D M X Y Z f).hom ≫
        dgFunctorCommaReplacementHomMap R (RightModule R D) (RightModule R C) F KX L))
      (add_zero (-1)) =
    (Cochain.ofHom (dgGluingKernelHomIso R C D M X Y).hom).comp
      (((dgGluingGradedPostcomposition R E KX KY L).f (-1)
        (dgGluingKernelConeNullElement R C D M Y Z f)).comp (Cochain.ofHom
        (dgFunctorCommaReplacementHomMap R (RightModule R D) (RightModule R C) F KX L))
        (add_zero (-1))) (zero_add (-1)) := by
  rw [dgGluingHomConeKernelIso_inl_replacement]
  erw [dgGluingCommaGradedPost_replacement R (RightModule R D) (RightModule R C) F KX KY L g]
  rw [dgGluingKernelConeNullElement_replacement,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    dgGluingKernelHomIso_left]
  rfl

end SerrePositivity.InfinityCategories
