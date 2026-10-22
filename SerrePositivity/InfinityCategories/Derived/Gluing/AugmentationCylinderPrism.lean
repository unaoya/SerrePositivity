module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexCochainAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainCylinderProjectionPrimitive

/-! 元円柱の実 primitive を augmentation 構成へ入れた明示的な全区間族。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory
open scoped Simplicial
variable {R : Type u} [CommRing R] (K : Complex R)

def dgGluingAugmentationCylinderPrism :=
  dgGluingComplexCochainAugmentationPrism.{u, v}
    (dgGluingCochainCylinderZero K) (dgGluingCochainCylinderOne K)
    (dgGluingCochainCylinderPrimitive K) (dgGluingCochainCylinderPrimitive_boundary K)

lemma dgGluingAugmentationCylinderPrism_zero :
    prismEndpoint 0 _ ≫ dgGluingAugmentationCylinderPrism.{u, v} K =
      complexPinchedMap.{u, max u v} (dgGluingCochainCylinderZero K) :=
  dgGluingComplexCochainAugmentationPrism_zero _ _ _ _

lemma dgGluingAugmentationCylinderPrism_one :
    prismEndpoint 1 _ ≫ dgGluingAugmentationCylinderPrism.{u, v} K =
      complexPinchedMap.{u, max u v} (dgGluingCochainCylinderOne K) :=
  dgGluingComplexCochainAugmentationPrism_one _ _ _ _

end SerrePositivity.InfinityCategories
