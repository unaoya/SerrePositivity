module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniversePinchedComplexIso
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R]
lemma dgGluingCommonComplexUniverse_round_trip (K : _root_.SerrePositivity.DifferentialGraded.Complex R) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,v,w,r} K).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,w,v,r} K).hom = 𝟙 _ := by
  have hi : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,w,v,r} K).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,v,w,r} K).inv := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [hi, Iso.hom_inv_id]

lemma dgGluingUniversePinchedComplexIso_functor
    {A : Type v} {B : Type w} [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R B]
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A B) (x y : A) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniversePinchedComplexIso.{u,v,max u v w r} R A x y).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u,v,w,max u v w r} F)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap_vertex.{u,v,w,max u v w r} F x)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap_vertex.{u,v,w,max u v w r} F y)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniversePinchedComplexIso.{u,w,max u v w r} R B (F.obj x) (F.obj y)).hom =
    (SSet.uliftFunctor.{max u v w r,max u v}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u,v} (F.map x y)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,v,w,r}
        (_root_.SerrePositivity.DifferentialGraded.homObject R B (F.obj x) (F.obj y))).hom := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseFunctorHomModelComparison, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniversePinchedComplexIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_inv, Iso.symm_hom, Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc] using
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseFunctorHomModelComparison_eq.{u,v,w,r} F x y

lemma dgGluingUniversePinchedComplexIso_functor_same_universe
    {A : Type v} {B : Type w} [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R B]
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A B) (x y : A) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniversePinchedComplexIso.{u,v,max u v w r} R A x y).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u,v,w,max u v w r} F)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap_vertex.{u,v,w,max u v w r} F x)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap_vertex.{u,v,w,max u v w r} F y)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniversePinchedComplexIso.{u,w,max u v w r} R B (F.obj x) (F.obj y)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,w,v,r}
        (_root_.SerrePositivity.DifferentialGraded.homObject R B (F.obj x) (F.obj y))).hom =
    (SSet.uliftFunctor.{max u v w r,max u v}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u,v} (F.map x y)) := by
  rw [reassoc_of% dgGluingUniversePinchedComplexIso_functor.{u,v,w,r} F x y,
    dgGluingCommonComplexUniverse_round_trip.{u,v,w,r}, Category.comp_id]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
