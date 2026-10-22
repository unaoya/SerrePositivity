module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientCylinder
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainCylinderPrimitive

/-! 元 Hom の円柱からの係数族は νf・gμ と、元の比較 primitive の負号を全次数で保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomCoefficientCylinderExtension_zero (X Y : DGGluingObject R C D M) :
    dgGluingCochainCylinderZero (dgGluingHomComplex R C D M X Y) ≫
        dgGluingHomCoefficientCylinderExtension R C D M X Y =
      dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y := by
  rw [dgGluingHomCoefficientCylinderExtension, ← Category.assoc,
    dgGluingCochainCylinderMap_zero, Category.assoc, dgGluingCoefficientCylinderExtension,
    dgGluingCochainCylinderExtension_zero, dgGluingHomTwoEndpointPath_start]

lemma dgGluingHomCoefficientCylinderExtension_one (X Y : DGGluingObject R C D M) :
    dgGluingCochainCylinderOne (dgGluingHomComplex R C D M X Y) ≫
        dgGluingHomCoefficientCylinderExtension R C D M X Y =
      dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y := by
  rw [dgGluingHomCoefficientCylinderExtension, ← Category.assoc,
    dgGluingCochainCylinderMap_one, Category.assoc, dgGluingCoefficientCylinderExtension,
    dgGluingCochainCylinderExtension_one, dgGluingHomTwoEndpointPath_end]

lemma dgGluingHomCoefficientCylinderExtension_primitive (X Y : DGGluingObject R C D M) :
    (dgGluingCochainCylinderPrimitive (dgGluingHomComplex R C D M X Y)).comp
        (Cochain.ofHom (dgGluingHomCoefficientCylinderExtension R C D M X Y))
        (add_zero (-1)) =
      -dgGluingHomPrimitive R C D M X Y := by
  rw [dgGluingHomCoefficientCylinderExtension, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_third_is_zero_cochain, dgGluingCochainCylinderPrimitive_map,
    Cochain.comp_assoc_of_first_is_zero_cochain, dgGluingCoefficientCylinderExtension,
    dgGluingCochainCylinderPrimitive_extension, Cochain.comp_neg,
    dgGluingHomTwoEndpointPath_primitive]

end SerrePositivity.InfinityCategories
