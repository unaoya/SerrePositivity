module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseModuleFunctorFamily

/-! 同じ加群値 dg 関手の導来区間族は、元の全 pinched 族に同じ実導来関手を作用させたもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (E : Type (max u v w)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]

lemma dgGluingUniverseModuleFunctorEvaluation (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R E (_root_.SerrePositivity.DifferentialGraded.RightModule R C)) (x y : E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (F.map x y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (F.obj x) (F.obj y)).inv)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism
        ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (homObject R E x y))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniversePinchedComplexIso.{u, max u v w,
          max (u + 1) v w} R E x y).inv ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u, max u v w, max (u + 1) v, max (u + 1) v w} F ≫
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleFunctorFamily R C E F x y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseFunctorIntervalImage.{u, max u v w, max (u + 1) v,
    max (u + 1) v w} F x y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
