module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseFunctorHomAction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseHomModelComparison

/-! 元の一般宇宙の nerve の全 Hom 作用を、同じ Hom 複体の空間模型へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

def dgGluingUniverseFunctorHomModelComparison (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D) (x y : C) :
    (SSet.uliftFunctor.{max u v w r, max u v}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} (homObject R C x y)) ⟶
      (SSet.uliftFunctor.{max u v w r, max u w}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, w} (homObject R D (F.obj x) (F.obj y))) :=
  (SSet.uliftFunctor.{max u v w r, max u v}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftPinchedHomIso.{max u v, max u v w r}
      (C := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u, v, w, max u v w r} F)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap_vertex.{u, v, w, max u v w r} F x)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap_vertex.{u, v, w, max u v w r} F y)).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftPinchedHomIso.{max u w, max u v w r} (C := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y))).inv) ≫
    (SSet.uliftFunctor.{max u v w r, max u w}).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (F.obj x) (F.obj y)).hom

lemma dgGluingUniverseFunctorHomModelComparison_eq (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D) (x y : C) :
    dgGluingUniverseFunctorHomModelComparison.{u, v, w, r} F x y =
    (SSet.uliftFunctor.{max u v w r, max u v}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (F.map x y)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r}
        (_root_.SerrePositivity.DifferentialGraded.homObject R D (F.obj x) (F.obj y))).hom := by
  rw [dgGluingUniverseFunctorHomModelComparison,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseFunctorHomAction.{u, v, w, max u v w r}]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomModelComparison_eq.{u, v, w, r} (F.map x y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
