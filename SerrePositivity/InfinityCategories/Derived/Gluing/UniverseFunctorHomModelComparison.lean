module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseFunctorHomAction
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseHomModelComparison

/-! 元の一般宇宙の nerve の全 Hom 作用を、同じ Hom 複体の空間模型へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [DGCategory R C] [DGCategory R D]

def dgGluingUniverseFunctorHomModelComparison (F : DGFunctor R C D) (x y : C) :
    (SSet.uliftFunctor.{max u v w r, max u v}).obj
        (complexPinchedSpace.{u, v} (homObject R C x y)) ⟶
      (SSet.uliftFunctor.{max u v w r, max u w}).obj
        (complexPinchedSpace.{u, w} (homObject R D (F.obj x) (F.obj y))) :=
  (SSet.uliftFunctor.{max u v w r, max u v}).map (pinchedComplexModelIso x y).inv ≫
    ((uliftPinchedHomIso.{max u v, max u v w r}
      (C := dgNerve R C) (Simplex.vertex x) (Simplex.vertex y)).hom ≫
    pinchedHomMap (dgGluingUniverseNerveMap.{u, v, w, max u v w r} F)
      (ULift.up (Simplex.vertex x)) (ULift.up (Simplex.vertex y)) ≫
    (pinchedEndpointIso
      (dgGluingUniverseNerveMap_vertex.{u, v, w, max u v w r} F x)
      (dgGluingUniverseNerveMap_vertex.{u, v, w, max u v w r} F y)).hom ≫
    (uliftPinchedHomIso.{max u w, max u v w r} (C := dgNerve R D)
      (Simplex.vertex (F.obj x)) (Simplex.vertex (F.obj y))).inv) ≫
    (SSet.uliftFunctor.{max u v w r, max u w}).map
      (pinchedComplexModelIso (F.obj x) (F.obj y)).hom

lemma dgGluingUniverseFunctorHomModelComparison_eq (F : DGFunctor R C D) (x y : C) :
    dgGluingUniverseFunctorHomModelComparison.{u, v, w, r} F x y =
    (SSet.uliftFunctor.{max u v w r, max u v}).map (complexPinchedMap.{u, v} (F.map x y)) ≫
      (dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r}
        (homObject R D (F.obj x) (F.obj y))).hom := by
  rw [dgGluingUniverseFunctorHomModelComparison,
    dgGluingUniverseFunctorHomAction.{u, v, w, max u v w r}]
  exact dgGluingUniverseHomModelComparison_eq.{u, v, w, r} (F.map x y)

end SerrePositivity.InfinityCategories
