module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowHomTrianglePair
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedEndpointUncurry

/-! 関手値の実 Hom 作用の全四角形は、元 Hom の同じ区間評価と元関手族の評価の合成。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial

lemma dgGluingArrowHomActionPrism {A B X P : SSet.{u}} (a : A ⟶ (ihom B).obj X)
    {x y : A _⦋0⦌} {F G : B ⟶ X}
    (hx : a.app (Opposite.op ⦋0⦌) x = functorVertex F)
    (hy : a.app (Opposite.op ⦋0⦌) y = functorVertex G)
    (f : P ⟶ pinchedHom x y) :
    intervalFunctorHomPrism (f ≫ pinchedHomMap a x y ≫
      (pinchedEndpointIso hx hy).hom ≫ pinchedHomToIntervalMappingSpace _ _) =
      ((β_ (Δ[1] : SSet.{u}) B).hom ▷ P) ≫ (α_ B Δ[1] P).hom ≫
        (B ◁ intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace x y)) ≫ uncurry a := by
  have he : intervalMappingUncurry (f ≫ pinchedHomMap a x y ≫
      (pinchedEndpointIso hx hy).hom ≫ pinchedHomToIntervalMappingSpace _ _) =
      intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace x y) ≫ a := by
    rw [← Category.assoc f, dgGluingPinchedEndpointIso_interval_uncurry,
      pinchedHomUncurry_postcomp, pinchedHomToIntervalMappingSpace_uncurry, Category.assoc]
  rw [intervalFunctorHomPrism, he, functorParameterizedPrism, uncurry_natural_left]

end SerrePositivity.InfinityCategories
