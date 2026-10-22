module
public import SerrePositivity.InfinityCategories.Derived.Gluing.TwoEndpointPathProduct

/-! 元の二つの作用を直積に束ねたまま、同じ差の cocone 空間を引き戻しとして表示する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory CochainComplex
open DifferentialGraded
variable {R : Type u} [CommRing R] {A B Q : Complex R} (f : A ⟶ Q) (g : B ⟶ Q)

lemma dgGluingTwoEndpointProduct_isPullback :
    IsPullback
      (complexPinchedMap.{u, v}
        (dgGluingCoconeTwoEndpointPath (biprod.fst ≫ f) (biprod.snd ≫ g)))
      (lift
        (complexPinchedMap.{u, v}
          (mappingCocone.fst (biprod.snd ≫ g - biprod.fst ≫ f) ≫ biprod.fst))
        (complexPinchedMap.{u, v}
          (mappingCocone.fst (biprod.snd ≫ g - biprod.fst ≫ f) ≫ biprod.snd)))
      (dgGluingComplexPathSpaceEndpointPair.{u, v} Q)
      (complexPinchedMap.{u, v} f ⊗ₘ complexPinchedMap.{u, v} g) := by
  refine (dgGluingTwoEndpointPathSpace_isPullback.{u, v}
    (biprod.fst ≫ f) (biprod.snd ≫ g)).of_iso
      (Iso.refl _) (Iso.refl _) (dgGluingComplexPinchedBiprodIso.{u, v} A B)
      (dgGluingComplexPinchedBiprodIso.{u, v} Q Q) ?_ ?_ ?_ ?_
  · simp
  · simpa only [Iso.refl_hom, Category.id_comp] using
      dgGluingComplexPinchedBiprodIso_projection_pair.{u, v}
        (mappingCocone.fst (biprod.snd ≫ g - biprod.fst ≫ f))
  · simpa only [Iso.refl_hom, Category.id_comp] using
      (dgGluingComplexPathSpaceEndpointPair_eq.{u, v} Q).symm
  · exact dgGluingComplexPinchedBiprodIso_pair_action f g

end SerrePositivity.InfinityCategories
