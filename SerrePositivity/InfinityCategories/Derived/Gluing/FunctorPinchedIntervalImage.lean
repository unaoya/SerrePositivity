module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedEndpointUncurry

/-! 任意 dg 関手の実 Hom 鎖作用は、端点輸送を含め元の同じ全区間族の nerve 像になる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {R : Type u} [CommRing R] {C D : Type v} [DGCategory R C] [DGCategory R D]

lemma dgGluingFunctorPinchedIntervalImage (F : DGFunctor R C D) {x y : C}
    {K : SSet.{max u v}} (f : K ⟶ DGNerve.pinchedHom R C x y) :
    intervalMappingUncurry ((f ≫ pinchedHomChainMap (F.map x y)) ≫
      pinchedHomToIntervalMappingSpace (X := dgNerve R D)
        (Simplex.vertex (F.obj x)) (Simplex.vertex (F.obj y))) =
      intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace (X := dgNerve R C)
        (Simplex.vertex x) (Simplex.vertex y)) ≫ dgNerve.map F := by
  rw [← dgFunctor_pinchedHomMap_eq F x y, ← Category.assoc f,
    pinchedHomToIntervalMappingSpace_uncurry, dgGluingPinchedEndpointIso_hom_uncurry,
    pinchedHomUncurry_postcomp, pinchedHomToIntervalMappingSpace_uncurry, Category.assoc]

end SerrePositivity.InfinityCategories
