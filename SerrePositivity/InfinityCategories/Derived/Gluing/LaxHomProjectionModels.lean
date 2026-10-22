module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseFunctorHomModelComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomInputTransport

/-! 導来 lax 比較の二脚を全 Hom 複体模型へ戻すと、元の左右鎖射影になる。 -/
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
local notation "F" => dgGluingUniverseDerivedNerveLaxComparison R C D M

def dgGluingLaxHomLeftModelComparison (X Y : DGGluingObject R C D M) :=
  (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
    (pinchedHomMap (F) (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y)) ≫
      pinchedHomMap (F2.laxPullbackFst (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M))
        ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex X)))
        ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex Y))) ≫
      (dgGluingPinchedCompositeIso (F)
        (F2.laxPullbackFst (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M))
        (dgGluingUniverseLeftNerve R C D M) (dgGluingUniverseDerivedNerveLaxComparison_fst R C D M)
        (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y))).hom) ≫
    (pinchedEndpointIso (dgGluingUniverseNerveMap_vertex.{u, max u v w, v, max (u + 1) v w}
        (dgGluingLeft R C D M) X)
      (dgGluingUniverseNerveMap_vertex.{u, max u v w, v, max (u + 1) v w}
        (dgGluingLeft R C D M) Y)).hom ≫
    (uliftPinchedHomIso.{max u v, max (u + 1) v w} (C := dgNerve R C)
      (Simplex.vertex X.left) (Simplex.vertex Y.left)).inv ≫
    (SSet.uliftFunctor.{max (u + 1) v w, max u v}).map
      (pinchedComplexModelIso X.left Y.left).hom

lemma dgGluingLaxHomLeftModelComparison_eq (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomLeftModelComparison R C D M X Y =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)) ≫
      (dgGluingCommonComplexPinchedUniverseIso.{u, max u v w, v, max (u + 1) v w}
        (homObject R C X.left Y.left)).hom := by
  rw [dgGluingLaxHomLeftModelComparison, dgGluingPinchedComposite_naturality]
  change dgGluingUniverseFunctorHomModelComparison.{u, max u v w, v, max (u + 1) v w}
    (dgGluingLeft R C D M) X Y = _
  rw [dgGluingUniverseFunctorHomModelComparison_eq]
  rfl

def dgGluingLaxHomRightModelComparison (X Y : DGGluingObject R C D M) :=
  (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
    (pinchedHomMap (F) (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y)) ≫
      pinchedHomMap (F2.laxPullbackSnd (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M))
        ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex X)))
        ((F).app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex Y))) ≫
      (dgGluingPinchedCompositeIso (F)
        (F2.laxPullbackSnd (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M))
        (dgGluingUniverseRightNerve R C D M) (dgGluingUniverseDerivedNerveLaxComparison_snd R C D M)
        (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y))).hom) ≫
    (pinchedEndpointIso (dgGluingUniverseNerveMap_vertex.{u, max u v w, w, max (u + 1) v w}
        (dgGluingRight R C D M) X)
      (dgGluingUniverseNerveMap_vertex.{u, max u v w, w, max (u + 1) v w}
        (dgGluingRight R C D M) Y)).hom ≫
    (uliftPinchedHomIso.{max u w, max (u + 1) v w} (C := dgNerve R D)
      (Simplex.vertex X.right) (Simplex.vertex Y.right)).inv ≫
    (SSet.uliftFunctor.{max (u + 1) v w, max u w}).map
      (pinchedComplexModelIso X.right Y.right).hom

lemma dgGluingLaxHomRightModelComparison_eq (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomRightModelComparison R C D M X Y =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)) ≫
      (dgGluingCommonComplexPinchedUniverseIso.{u, max u v w, w, max (u + 1) v w}
        (homObject R D X.right Y.right)).hom := by
  rw [dgGluingLaxHomRightModelComparison, dgGluingPinchedComposite_naturality]
  change dgGluingUniverseFunctorHomModelComparison.{u, max u v w, w, max (u + 1) v w}
    (dgGluingRight R C D M) X Y = _
  rw [dgGluingUniverseFunctorHomModelComparison_eq]
  rw [dgGluingRight_map]
  rfl

end SerrePositivity.InfinityCategories
