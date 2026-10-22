module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniversePinchedComplexIso

/-! 元の一般宇宙の dg 関手の実 Hom 作用を、標的の pinched 模型まで厳密に回収する。 -/
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

lemma dgGluingUniverseFunctorPinchedModelMap (F : DGFunctor R C D) (x y : C) :
    (dgGluingUniversePinchedComplexIso.{u, v, max u v w r} R C x y).inv ≫
        pinchedHomMap (dgGluingUniverseNerveMap.{u, v, w, max u v w r} F)
          (ULift.up (Simplex.vertex x)) (ULift.up (Simplex.vertex y)) ≫
        (pinchedEndpointIso (dgGluingUniverseNerveMap_vertex.{u, v, w, max u v w r} F x)
          (dgGluingUniverseNerveMap_vertex.{u, v, w, max u v w r} F y)).hom =
      (SSet.uliftFunctor.{max u v w r, max u v}).map (complexPinchedMap.{u, v} (F.map x y)) ≫
        (dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r}
          (homObject R D (F.obj x) (F.obj y))).hom ≫
        (dgGluingUniversePinchedComplexIso.{u, w, max u v w r}
          R D (F.obj x) (F.obj y)).inv := by
  have hh := congrArg
    (fun k => k ≫ (dgGluingUniversePinchedComplexIso.{u, w, max u v w r}
      R D (F.obj x) (F.obj y)).inv)
    (dgGluingUniverseFunctorHomModelComparison_eq.{u, v, w, r} F x y)
  change (((dgGluingUniversePinchedComplexIso.{u, v, max u v w r} R C x y).inv ≫
    pinchedHomMap (dgGluingUniverseNerveMap.{u, v, w, max u v w r} F)
      (ULift.up (Simplex.vertex x)) (ULift.up (Simplex.vertex y)) ≫
    (pinchedEndpointIso (dgGluingUniverseNerveMap_vertex.{u, v, w, max u v w r} F x)
      (dgGluingUniverseNerveMap_vertex.{u, v, w, max u v w r} F y)).hom) ≫
    (dgGluingUniversePinchedComplexIso.{u, w, max u v w r}
      R D (F.obj x) (F.obj y)).hom) ≫ _ = _ at hh
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh

end SerrePositivity.InfinityCategories
