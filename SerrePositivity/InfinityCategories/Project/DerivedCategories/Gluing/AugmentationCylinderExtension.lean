module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.AugmentationCylinderPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexAugmentationPost
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexAugmentationCongr

/-! 明示円柱を実 extension で写すと、同じ二作用・primitive の元の全 cochain prism を回収する。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {R : Type u} [CommRing R] {K L : Complex R}
  (f g : K ⟶ L) (h : Cochain K L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))

lemma dgGluingAugmentationCylinderPrism_extension :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentationCylinderPrism.{u, v} K ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderExtension f g h he) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism.{u, v} f g h he := by
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism_post.{u, v}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderZero K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderOne K)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderPrimitive K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderPrimitive_boundary K)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderExtension f g h he)
  refine ht.trans ?_
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism_congr
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderExtension_zero f g h he
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderExtension_one f g h he
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderPrimitive_extension f g h he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
