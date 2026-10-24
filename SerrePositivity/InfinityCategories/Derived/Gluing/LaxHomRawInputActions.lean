module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomRawInputIso
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseHomModelRoundTrip
/-!
概要：正本 Hom 模型からの二射影作用を元の左右 Hom 鎖射影へ戻す。
方針：一般宇宙の dg 関手の実 Hom 作用と共通宇宙変更の往復則を適用する。
規約：元の端点輸送と全線形成分を保持する。
使われ方：元入力付き区間座標と既存の四座標比較の第二射影を照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
lemma dgGluingLaxHomLeftRawInput_action :
    (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
      pinchedHomMap (dgGluingUniverseLeftNerve R C D M)
        (ULift.up (Simplex.vertex (A := R) X)) (ULift.up (Simplex.vertex (A := R) Y)) ≫
      (pinchedEndpointIso (dgGluingUniverseLeftNerve_vertex R C D M X)
        (dgGluingUniverseLeftNerve_vertex R C D M Y)).hom ≫
      (dgGluingLaxHomLeftRawInputIso R C D M X Y).hom =
    (SSet.uliftFunctor.{max (u + 1) v w,max u v w}).map
      (complexPinchedMap.{u,max u v w} (dgGluingLeftHomMap R C D M X Y)) := by
  simpa only [dgGluingUniverseHomMappingIso, dgGluingHomMappingIso,
    dgGluingLaxHomLeftRawInputIso, dgGluingUniversePinchedComplexIso,
    dgGluingUniverseLeftNerve, dgGluingLeft,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, Iso.symm_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc] using
    dgGluingUniversePinchedComplexIso_functor_same_universe.{u,max u v w,v,max (u + 1) v w}
      (dgGluingLeft R C D M) X Y
lemma dgGluingLaxHomRightRawInput_action :
    (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
      pinchedHomMap (dgGluingUniverseRightNerve R C D M)
        (ULift.up (Simplex.vertex (A := R) X)) (ULift.up (Simplex.vertex (A := R) Y)) ≫
      (pinchedEndpointIso (dgGluingUniverseRightNerve_vertex R C D M X)
        (dgGluingUniverseRightNerve_vertex R C D M Y)).hom ≫
      (dgGluingLaxHomRightRawInputIso R C D M X Y).hom =
    (SSet.uliftFunctor.{max (u + 1) v w,max u v w}).map
      (complexPinchedMap.{u,max u v w} (dgGluingRightHomMap R C D M X Y)) := by
  have hobj (Z : DGGluingObject R C D M) : (dgGluingRight R C D M).obj Z = Z.right := rfl
  simpa only [dgGluingUniverseHomMappingIso, dgGluingHomMappingIso,
    dgGluingLaxHomRightRawInputIso, dgGluingUniversePinchedComplexIso,
    dgGluingUniverseRightNerve,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, Iso.symm_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc, dgGluingRight_map, hobj] using!
    dgGluingUniversePinchedComplexIso_functor_same_universe.{u,max u v w,w,max (u + 1) v w}
      (dgGluingRight R C D M) X Y
end SerrePositivity.InfinityCategories
