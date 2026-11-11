module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TwoEndpointPathProduct

/-! 元の二つの作用を直積に束ねたまま、同じ差の cocone 空間を引き戻しとして表示する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory CochainComplex
open DifferentialGraded
variable {R : Type u} [CommRing R] {A B Q : Complex R} (f : A ⟶ Q) (g : B ⟶ Q)

lemma dgGluingTwoEndpointProduct_isPullback :
    IsPullback
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeTwoEndpointPath (biprod.fst ≫ f) (biprod.snd ≫ g)))
      (lift
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v}
          (mappingCocone.fst (biprod.snd ≫ g - biprod.fst ≫ f) ≫ biprod.fst))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v}
          (mappingCocone.fst (biprod.snd ≫ g - biprod.fst ≫ f) ≫ biprod.snd)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathSpaceEndpointPair.{u, v} Q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} f ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} g) := by
  refine (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTwoEndpointPathSpace_isPullback.{u, v}
    (biprod.fst ≫ f) (biprod.snd ≫ g)).of_iso
      (Iso.refl _) (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedBiprodIso.{u, v} A B)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedBiprodIso.{u, v} Q Q) ?_ ?_ ?_ ?_
  · simp
  · simpa only [Iso.refl_hom, Category.id_comp] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedBiprodIso_projection_pair.{u, v}
        (mappingCocone.fst (biprod.snd ≫ g - biprod.fst ≫ f))
  · simpa only [Iso.refl_hom, Category.id_comp] using
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathSpaceEndpointPair_eq.{u, v} Q).symm
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedBiprodIso_pair_action f g

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
