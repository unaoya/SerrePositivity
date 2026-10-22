module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientCylinderCoefficients
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainCylinderExt

/-! 二作用と元の primitive から直接作る円柱 extension は、主係数 path の extension と一致する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomNegativePrimitive_boundary (X Y : DGGluingObject R C D M) :
    δ (-1) 0 (-dgGluingHomPrimitive R C D M X Y) =
      Cochain.ofHom (dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y -
        dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y) := by
  have h := congrArg (fun c =>
    (Cochain.ofHom (dgGluingHomTwoEndpointPath R C D M X Y)).comp c (zero_add 0))
    (dgGluingComplexPathNegativePrimitive_boundary (M.value X.left Y.right))
  rw [← δ_ofHom_comp, Cochain.comp_neg, dgGluingHomTwoEndpointPath_primitive,
    Cochain.ofHom_sub, Cochain.comp_sub, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    dgGluingHomTwoEndpointPath_end, dgGluingHomTwoEndpointPath_start,
    ← Cochain.ofHom_sub] at h
  exact h

def dgGluingHomCoefficientDirectCylinderExtension (X Y : DGGluingObject R C D M) :=
  dgGluingCochainCylinderExtension
    (dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y)
    (dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y)
    (-dgGluingHomPrimitive R C D M X Y) (dgGluingHomNegativePrimitive_boundary R C D M X Y)

lemma dgGluingHomCoefficientCylinderExtension_direct (X Y : DGGluingObject R C D M) :
    dgGluingHomCoefficientCylinderExtension R C D M X Y =
      dgGluingHomCoefficientDirectCylinderExtension R C D M X Y := by
  apply dgGluingCochainCylinder_hom_ext
  · rw [dgGluingHomCoefficientCylinderExtension_zero,
      dgGluingHomCoefficientDirectCylinderExtension, dgGluingCochainCylinderExtension_zero]
  · rw [dgGluingHomCoefficientCylinderExtension_one,
      dgGluingHomCoefficientDirectCylinderExtension, dgGluingCochainCylinderExtension_one]
  · rw [dgGluingHomCoefficientCylinderExtension_primitive,
      dgGluingHomCoefficientDirectCylinderExtension, dgGluingCochainCylinderPrimitive_extension]

end SerrePositivity.InfinityCategories
