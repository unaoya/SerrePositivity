module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveUniverseLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLiftFunctor
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseBoundaryHom
/-!
概要：独立の対象宇宙にある dg 圏の間の関手を共通宇宙の nerve 写像へ送る。
方針：元の単体の実 dg 関手像をとり、対象と全単体を同じ上位宇宙へ持ち上げる。
規約：係数宇宙と Hom 複体は変えない。Small 仮定は不要。
使われ方：混在宇宙の dg 加群値関手と実 tensor・Yoneda の比較。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} {E : Type w} {B : Type z}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R B]

def dgNerveCommonMap (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) :
    (SSet.uliftFunctor.{max u v w t, max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) ⟶
      (SSet.uliftFunctor.{max u v w t, max u w}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) where
  app _ := ↾fun s => ULift.up (s.down.map F)
  naturality _ _ f := by
    ext s
    apply ULift.ext
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map_pullback s.down.toSimplexData F f.unop.toOrderHom

lemma dgNerveCommonMap_comp (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) (G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R E B) :
    dgNerveCommonMap.{u, v, w, max u v w z t} F ≫
      dgNerveCommonMap.{u, w, z, max u v w z t} G =
        dgNerveCommonMap.{u, v, z, max u v w z t} (F.comp G) := by
  ext n s
  apply ULift.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp s.down.toSimplexData F G).symm

lemma dgNerveCommonMap_id :
    dgNerveCommonMap.{u, v, v, t} (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (A := R) D) =
      𝟙 ((SSet.uliftFunctor.{max u v t, max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)) := by
  ext n s
  apply ULift.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_id s.down.toSimplexData

lemma dgNerveCommonMap_sameUniverse {E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) :
    dgNerveCommonMap.{u, v, v, t} F =
      (SSet.uliftFunctor.{max u v t, max u v}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) := rfl

lemma dgNerveCommonMap_lifted (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) :
    dgNerveCommonMap.{u, v, w, t} F =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, v, max u v w t} R D).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, w, max u v w t, max u v w t} F) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, w, max u v w t} R E).inv := by
  ext n s
  apply ULift.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
