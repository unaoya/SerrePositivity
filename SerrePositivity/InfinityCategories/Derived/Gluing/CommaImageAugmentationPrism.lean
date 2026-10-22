module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaImagePrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaAugmentationSliceCube

/-! 元 comma と恒等 comma の augmentation は、実 dg 関手に沿い全単体族として厳密に可換。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C E : Type (max u v)) [DGCategory R C] [DGCategory R E]
  (F : DGFunctor R C E)

lemma dgGluingCommaImageAugmentationPrism :
    (Δ[1] ◁ dgNerve.map (dgGluingCommaImageFunctor R C E F)) ≫
        dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) =
      dgGluingCommaAugmentationPrism R C E F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change (dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      (s.2.map (dgGluingCommaImageFunctor R C E F))
      (SSet.stdSimplex.objEquiv s.1).toOrderHom).map
        (dgUniverseLiftUp.{u, max u v, max u v} R E) =
    (dgCommaAugmentationPrismSimplex R C E F s.2
      (SSet.stdSimplex.objEquiv s.1).toOrderHom).map
        (dgUniverseLiftUp.{u, max u v, max u v} R E)
  rw [dgGluingCommaImagePrismSimplex]

end SerrePositivity.InfinityCategories
