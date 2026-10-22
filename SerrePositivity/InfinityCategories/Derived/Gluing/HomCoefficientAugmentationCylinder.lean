module
public import SerrePositivity.InfinityCategories.Derived.Gluing.AugmentationCylinderExtension
public import SerrePositivity.InfinityCategories.Derived.Gluing.AugmentationCylinderNaturality
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientAugmentationHomotopy

/-! 元 Hom の二端点 path の円柱写像と実 extension は、負 primitive の明示 prism 全体を回収。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomCoefficientAugmentationCylinder_extension (X Y : DGGluingObject R C D M) :
    dgGluingAugmentationCylinderMapPrism.{u, max u v w}
        (dgGluingHomTwoEndpointPath R C D M X Y) ≫
      complexPinchedMap.{u, max u v w} (dgGluingCoefficientCylinderExtension R C D M X Y) =
        dgGluingHomCoefficientAugmentationPrism R C D M X Y := by
  rw [dgGluingAugmentationCylinderMapPrism, Category.assoc, ← complexPinchedMap_comp]
  change dgGluingAugmentationCylinderPrism _ ≫
    complexPinchedMap (dgGluingHomCoefficientCylinderExtension R C D M X Y) = _
  rw [dgGluingHomCoefficientCylinderExtension_direct]
  exact dgGluingAugmentationCylinderPrism_extension _ _ _ _

end SerrePositivity.InfinityCategories
