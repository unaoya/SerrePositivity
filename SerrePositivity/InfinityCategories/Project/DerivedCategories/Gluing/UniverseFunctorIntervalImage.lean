module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseFunctorPinchedModelMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PinchedEndpointUncurry

/-! dg 関手の同じ Hom 鎖写像を任意の実関手で後合成した区間族を、元の全 nerve 作用へ照合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

lemma dgGluingUniverseFunctorIntervalImage (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D) (x y : C)
    {Z : SSet.{max u v w r}}
    (q : (SSet.uliftFunctor.{max u v w r, max u w}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
      (((SSet.uliftFunctor.{max u v w r, max u v}).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (F.map x y)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r}
          (_root_.SerrePositivity.DifferentialGraded.homObject R D (F.obj x) (F.obj y))).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniversePinchedComplexIso.{u, w, max u v w r}
          R D (F.obj x) (F.obj y)).inv) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap q (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x)))
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y))) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism
        ((SSet.uliftFunctor.{max u v w r, max u v}).obj
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} (homObject R C x y))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniversePinchedComplexIso.{u, v, max u v w r} R C x y).inv ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u, v, w, max u v w r} F ≫ q := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_postcomp,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseFunctorPinchedModelMap.{u, v, w, r} F x y]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniversePinchedComplexIso _ _ _ _).inv,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedEndpointIso_hom_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_postcomp]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
