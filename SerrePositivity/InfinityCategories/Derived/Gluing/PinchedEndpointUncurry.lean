module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedIntervalEndpointTransport

/-! 端点表示の同型は、元の pinched Hom の全 join 族を変更しない。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

lemma dgGluingPinchedEndpointIso_hom_uncurry {T X : SSet.{u}}
    {x y x' y' : X _⦋0⦌} (hx : x = x') (hy : y = y') (a : T ⟶ pinchedHom x y) :
    pinchedHomUncurry (a ≫ (pinchedEndpointIso hx hy).hom) = pinchedHomUncurry a := by
  subst x'
  subst y'
  simp only [pinchedEndpointIso, Iso.refl_hom, Category.comp_id]

lemma dgGluingPinchedEndpointIso_interval_uncurry {T X : SSet.{u}}
    {x y x' y' : X _⦋0⦌} (hx : x = x') (hy : y = y') (a : T ⟶ pinchedHom x y) :
    intervalMappingUncurry (a ≫ (pinchedEndpointIso hx hy).hom ≫
        pinchedHomToIntervalMappingSpace x' y') =
      rightMappingSpacePrism T ≫ pinchedHomUncurry a := by
  rw [← Category.assoc, pinchedHomToIntervalMappingSpace_uncurry,
    dgGluingPinchedEndpointIso_hom_uncurry]

end SerrePositivity.InfinityCategories
