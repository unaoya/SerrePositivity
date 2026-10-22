module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCoefficientMapping
public import SerrePositivity.InfinityCategories.F1.RightIntervalEquivalence

/-! pinched Hom の端点輸送は、同じ区間族の評価を変更しない。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

lemma dgGluingPinchedIntervalEndpointTransport_uncurry {T X : SSet.{u}}
    {x y x' y' : X _⦋0⦌} (hx : x = x') (hy : y = y')
    (f : T ⟶ pinchedHom x' y') :
    intervalMappingUncurry (f ≫ (pinchedEndpointIso hx hy).inv ≫
        pinchedHomToIntervalMappingSpace x y) =
      intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace x' y') := by
  subst x'
  subst y'
  simp only [pinchedEndpointIso, Iso.refl_inv, Category.id_comp]

end SerrePositivity.InfinityCategories
