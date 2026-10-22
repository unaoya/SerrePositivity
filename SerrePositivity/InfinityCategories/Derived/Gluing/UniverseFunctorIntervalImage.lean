module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseFunctorPinchedModelMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedEndpointUncurry

/-! dg 関手の同じ Hom 鎖写像を任意の実関手で後合成した区間族を、元の全 nerve 作用へ照合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [DGCategory R C] [DGCategory R D]

lemma dgGluingUniverseFunctorIntervalImage (F : DGFunctor R C D) (x y : C)
    {Z : SSet.{max u v w r}}
    (q : (SSet.uliftFunctor.{max u v w r, max u w}).obj (dgNerve R D) ⟶ Z) :
    intervalMappingUncurry
      (((SSet.uliftFunctor.{max u v w r, max u v}).map
          (complexPinchedMap.{u, v} (F.map x y)) ≫
        (dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r}
          (homObject R D (F.obj x) (F.obj y))).hom ≫
        (dgGluingUniversePinchedComplexIso.{u, w, max u v w r}
          R D (F.obj x) (F.obj y)).inv) ≫
        pinchedHomMap q (ULift.up (Simplex.vertex (F.obj x)))
          (ULift.up (Simplex.vertex (F.obj y))) ≫ pinchedHomToIntervalMappingSpace _ _) =
      rightMappingSpacePrism
        ((SSet.uliftFunctor.{max u v w r, max u v}).obj
          (complexPinchedSpace.{u, v} (homObject R C x y))) ≫
        pinchedHomUncurry (dgGluingUniversePinchedComplexIso.{u, v, max u v w r} R C x y).inv ≫
          dgGluingUniverseNerveMap.{u, v, w, max u v w r} F ≫ q := by
  rw [← Category.assoc, pinchedHomToIntervalMappingSpace_uncurry, pinchedHomUncurry_postcomp,
    ← dgGluingUniverseFunctorPinchedModelMap.{u, v, w, r} F x y]
  rw [← Category.assoc (dgGluingUniversePinchedComplexIso _ _ _ _).inv,
    dgGluingPinchedEndpointIso_hom_uncurry, pinchedHomUncurry_postcomp]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories
