module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseFunctorHomAction
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseNerveProjections

/-! 元の一般宇宙の二射影は、全写像空間で元の左右 Hom 鎖写像を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingUniverseLeftNerve_hom_action (X Y : DGGluingObject R C D M) :
    (uliftPinchedHomIso.{max u v w, max (u + 1) v w}
      (C := dgNerve R (DGGluingObject R C D M))
      (Simplex.vertex X) (Simplex.vertex Y)).hom ≫
      pinchedHomMap (dgGluingUniverseLeftNerve R C D M)
        (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y)) ≫
      (pinchedEndpointIso (dgGluingUniverseNerveMap_vertex.{u, max u v w, v, max (u + 1) v w}
        (dgGluingLeft R C D M) X)
        (dgGluingUniverseNerveMap_vertex.{u, max u v w, v, max (u + 1) v w}
        (dgGluingLeft R C D M) Y)).hom ≫
      (uliftPinchedHomIso.{max u v, max (u + 1) v w} (C := dgNerve R C)
        (Simplex.vertex X.left) (Simplex.vertex Y.left)).inv =
    dgGluingUniverseHomChainMap.{u, max u v w, v, max (u + 1) v w}
      (dgGluingLeftHomMap R C D M X Y) :=
  dgGluingUniverseFunctorHomAction (dgGluingLeft R C D M) X Y

lemma dgGluingUniverseRightNerve_hom_action (X Y : DGGluingObject R C D M) :
    (uliftPinchedHomIso.{max u v w, max (u + 1) v w}
      (C := dgNerve R (DGGluingObject R C D M))
      (Simplex.vertex X) (Simplex.vertex Y)).hom ≫
      pinchedHomMap (dgGluingUniverseRightNerve R C D M)
        (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y)) ≫
      (pinchedEndpointIso (dgGluingUniverseNerveMap_vertex.{u, max u v w, w, max (u + 1) v w}
        (dgGluingRight R C D M) X)
        (dgGluingUniverseNerveMap_vertex.{u, max u v w, w, max (u + 1) v w}
        (dgGluingRight R C D M) Y)).hom ≫
      (uliftPinchedHomIso.{max u w, max (u + 1) v w} (C := dgNerve R D)
        (Simplex.vertex X.right) (Simplex.vertex Y.right)).inv =
    dgGluingUniverseHomChainMap.{u, max u v w, w, max (u + 1) v w}
      (dgGluingRightHomMap R C D M X Y) := by
  rw [← dgGluingRight_map]
  exact dgGluingUniverseFunctorHomAction (dgGluingRight R C D M) X Y

end SerrePositivity.InfinityCategories
