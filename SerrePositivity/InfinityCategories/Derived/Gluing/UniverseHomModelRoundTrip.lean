module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniversePinchedComplexIso
/-!
概要：一般宇宙の dg 関手作用を元の Hom 複体模型と同じ対象宇宙へ戻す。
方針：標準模型比較の自然性と、共通宇宙変更の厳密な逆射を合成する。
規約：全線形成分・元入力・端点輸送を保持する。
使われ方：正本の第二射影を元の左右 Hom 鎖射影へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable {R : Type u} [CommRing R]
lemma dgGluingCommonComplexUniverse_round_trip (K : Complex R) :
    (dgGluingCommonComplexPinchedUniverseIso.{u,v,w,r} K).hom ≫
      (dgGluingCommonComplexPinchedUniverseIso.{u,w,v,r} K).hom = 𝟙 _ := by
  have hi : (dgGluingCommonComplexPinchedUniverseIso.{u,w,v,r} K).hom =
      (dgGluingCommonComplexPinchedUniverseIso.{u,v,w,r} K).inv := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [hi, Iso.hom_inv_id]

lemma dgGluingUniversePinchedComplexIso_functor
    {A : Type v} {B : Type w} [DGCategory R A] [DGCategory R B]
    (F : DGFunctor R A B) (x y : A) :
    (dgGluingUniversePinchedComplexIso.{u,v,max u v w r} R A x y).inv ≫
      pinchedHomMap (dgGluingUniverseNerveMap.{u,v,w,max u v w r} F)
        (ULift.up (Simplex.vertex x)) (ULift.up (Simplex.vertex y)) ≫
      (pinchedEndpointIso
        (dgGluingUniverseNerveMap_vertex.{u,v,w,max u v w r} F x)
        (dgGluingUniverseNerveMap_vertex.{u,v,w,max u v w r} F y)).hom ≫
      (dgGluingUniversePinchedComplexIso.{u,w,max u v w r} R B (F.obj x) (F.obj y)).hom =
    (SSet.uliftFunctor.{max u v w r,max u v}).map (complexPinchedMap.{u,v} (F.map x y)) ≫
      (dgGluingCommonComplexPinchedUniverseIso.{u,v,w,r}
        (homObject R B (F.obj x) (F.obj y))).hom := by
  simpa only [dgGluingUniverseFunctorHomModelComparison, dgGluingUniversePinchedComplexIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_inv, Iso.symm_hom, Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc] using
    dgGluingUniverseFunctorHomModelComparison_eq.{u,v,w,r} F x y

lemma dgGluingUniversePinchedComplexIso_functor_same_universe
    {A : Type v} {B : Type w} [DGCategory R A] [DGCategory R B]
    (F : DGFunctor R A B) (x y : A) :
    (dgGluingUniversePinchedComplexIso.{u,v,max u v w r} R A x y).inv ≫
      pinchedHomMap (dgGluingUniverseNerveMap.{u,v,w,max u v w r} F)
        (ULift.up (Simplex.vertex x)) (ULift.up (Simplex.vertex y)) ≫
      (pinchedEndpointIso
        (dgGluingUniverseNerveMap_vertex.{u,v,w,max u v w r} F x)
        (dgGluingUniverseNerveMap_vertex.{u,v,w,max u v w r} F y)).hom ≫
      (dgGluingUniversePinchedComplexIso.{u,w,max u v w r} R B (F.obj x) (F.obj y)).hom ≫
      (dgGluingCommonComplexPinchedUniverseIso.{u,w,v,r}
        (homObject R B (F.obj x) (F.obj y))).hom =
    (SSet.uliftFunctor.{max u v w r,max u v}).map (complexPinchedMap.{u,v} (F.map x y)) := by
  rw [reassoc_of% dgGluingUniversePinchedComplexIso_functor.{u,v,w,r} F x y,
    dgGluingCommonComplexUniverse_round_trip.{u,v,w,r}, Category.comp_id]
end SerrePositivity.InfinityCategories
