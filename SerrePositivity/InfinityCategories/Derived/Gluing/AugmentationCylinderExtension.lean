module
public import SerrePositivity.InfinityCategories.Derived.Gluing.AugmentationCylinderPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexAugmentationPost
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexAugmentationCongr

/-! 明示円柱を実 extension で写すと、同じ二作用・primitive の元の全 cochain prism を回収する。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {R : Type u} [CommRing R] {K L : Complex R}
  (f g : K ⟶ L) (h : Cochain K L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))

lemma dgGluingAugmentationCylinderPrism_extension :
    dgGluingAugmentationCylinderPrism.{u, v} K ≫
        complexPinchedMap.{u, max u v} (dgGluingCochainCylinderExtension f g h he) =
      dgGluingComplexCochainAugmentationPrism.{u, v} f g h he := by
  have ht := dgGluingComplexCochainAugmentationPrism_post.{u, v}
    (dgGluingCochainCylinderZero K) (dgGluingCochainCylinderOne K)
    (dgGluingCochainCylinderPrimitive K) (dgGluingCochainCylinderPrimitive_boundary K)
    (dgGluingCochainCylinderExtension f g h he)
  refine ht.trans ?_
  apply dgGluingComplexCochainAugmentationPrism_congr
  · exact dgGluingCochainCylinderExtension_zero f g h he
  · exact dgGluingCochainCylinderExtension_one f g h he
  · exact dgGluingCochainCylinderPrimitive_extension f g h he

end SerrePositivity.InfinityCategories
