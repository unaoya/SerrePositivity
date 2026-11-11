module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexPinchedModelInverseNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PinchedEndpointUncurry
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorPinchedMap
/-!
概要：任意 dg 関手の元 Hom 複体上の全区間評価は、同じ nerve の実作用に等しい。
方針：実 Hom 模型同型の自然性と同じ pinched 全 join 評価を合成する。
規約：全次数・全区間を保持する。使われ方：元 lax 標的の二脚の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {C D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
lemma dgGluingFunctorRawIntervalEvaluation (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D) (x y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u,v} (F.map x y) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (F.obj x) (F.obj y)).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedModelInverse_naturality,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_pinchedHomMap_eq]
  simp only [Category.assoc]
  rw [← Category.assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedEndpointIso_interval_uncurry]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_postcomp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
