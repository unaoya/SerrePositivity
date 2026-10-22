module
public import SerrePositivity.InfinityCategories.Derived.Gluing.AugmentationCylinderPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexAugmentationProjection

/-! 元 augmentation から作った円柱の全区間は、実円柱射影の下で元複体上に固定される。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
variable {R : Type u} [CommRing R] (K : Complex R)

lemma dgGluingAugmentationCylinderPrism_over :
    dgGluingAugmentationCylinderPrism.{u, v} K ≫
        complexPinchedMap.{u, max u v} (dgGluingCochainCylinderProjection K) =
      snd Δ[1] (complexPinchedSpace.{u, max u v} K) := by
  have hp : dgGluingCochainCylinderOne K ≫ dgGluingCochainCylinderProjection K =
      dgGluingCochainCylinderZero K ≫ dgGluingCochainCylinderProjection K := by
    rw [dgGluingCochainCylinderOne_projection, dgGluingCochainCylinderZero_projection]
  have ht := dgGluingComplexCochainAugmentationPrism_post_zero.{u, v}
    (dgGluingCochainCylinderZero K) (dgGluingCochainCylinderOne K)
    (dgGluingCochainCylinderPrimitive K) (dgGluingCochainCylinderPrimitive_boundary K)
    (dgGluingCochainCylinderProjection K) hp (dgGluingCochainCylinderPrimitive_projection K)
  rw [dgGluingCochainCylinderZero_projection, complexPinchedMap_id, Category.comp_id] at ht
  exact ht

end SerrePositivity.InfinityCategories
