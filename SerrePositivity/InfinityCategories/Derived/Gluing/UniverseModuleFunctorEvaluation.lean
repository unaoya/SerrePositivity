module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseModuleFunctorFamily

/-! 同じ加群値 dg 関手の導来区間族は、元の全 pinched 族に同じ実導来関手を作用させたもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (E : Type (max u v w)) [DGCategory R E]

lemma dgGluingUniverseModuleFunctorEvaluation (F : DGFunctor R E (RightModule R C)) (x y : E) :
    intervalMappingUncurry (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
      (complexPinchedMap.{u, max (u + 1) v} (F.map x y) ≫
        (pinchedComplexModelIso (F.obj x) (F.obj y)).inv)) =
      rightMappingSpacePrism
        ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (homObject R E x y))) ≫
        pinchedHomUncurry (dgGluingUniversePinchedComplexIso.{u, max u v w,
          max (u + 1) v w} R E x y).inv ≫
          dgGluingUniverseNerveMap.{u, max u v w, max (u + 1) v, max (u + 1) v w} F ≫
            dgGluingUniverseModuleDerivedComparison.{u, v, w} R C := by
  rw [dgGluingUniverseModuleFunctorFamily R C E F x y]
  exact dgGluingUniverseFunctorIntervalImage.{u, max u v w, max (u + 1) v,
    max (u + 1) v w} F x y (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)

end SerrePositivity.InfinityCategories
