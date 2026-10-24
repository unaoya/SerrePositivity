module
public import SerrePositivity.InfinityCategories.Derived.DGNerveUniverseLift
public import SerrePositivity.InfinityCategories.Derived.DGUniverseLiftFunctor
public import SerrePositivity.InfinityCategories.Core.UniverseBoundaryHom
/-!
概要：独立の対象宇宙にある dg 圏の間の関手を共通宇宙の nerve 写像へ送る。
方針：元の単体の実 dg 関手像をとり、対象と全単体を同じ上位宇宙へ持ち上げる。
規約：係数宇宙と Hom 複体は変えない。Small 仮定は不要。
使われ方：混在宇宙の dg 加群値関手と実 tensor・Yoneda の比較。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} {E : Type w} {B : Type z}
  [DGCategory R D] [DGCategory R E] [DGCategory R B]

def dgNerveCommonMap (F : DGFunctor R D E) :
    (SSet.uliftFunctor.{max u v w t, max u v}).obj (dgNerve R D) ⟶
      (SSet.uliftFunctor.{max u v w t, max u w}).obj (dgNerve R E) where
  app _ := ↾fun s => ULift.up (s.down.map F)
  naturality _ _ f := by
    ext s
    apply ULift.ext
    apply Simplex.ext
    exact SimplexData.map_pullback s.down.toSimplexData F f.unop.toOrderHom

lemma dgNerveCommonMap_comp (F : DGFunctor R D E) (G : DGFunctor R E B) :
    dgNerveCommonMap.{u, v, w, max u v w z t} F ≫
      dgNerveCommonMap.{u, w, z, max u v w z t} G =
        dgNerveCommonMap.{u, v, z, max u v w z t} (F.comp G) := by
  ext n s
  apply ULift.ext
  apply Simplex.ext
  exact (SimplexData.map_comp s.down.toSimplexData F G).symm

lemma dgNerveCommonMap_id :
    dgNerveCommonMap.{u, v, v, t} (DGFunctor.id (A := R) D) =
      𝟙 ((SSet.uliftFunctor.{max u v t, max u v}).obj (dgNerve R D)) := by
  ext n s
  apply ULift.ext
  apply Simplex.ext
  exact SimplexData.map_id s.down.toSimplexData

lemma dgNerveCommonMap_sameUniverse {E : Type v} [DGCategory R E] (F : DGFunctor R D E) :
    dgNerveCommonMap.{u, v, v, t} F =
      (SSet.uliftFunctor.{max u v t, max u v}).map (dgNerve.map F) := rfl

lemma dgNerveCommonMap_lifted (F : DGFunctor R D E) :
    dgNerveCommonMap.{u, v, w, t} F =
      (dgNerveUniverseLiftIso.{u, v, max u v w t} R D).hom ≫
        dgNerve.map (dgUniverseLiftFunctor.{u, v, w, max u v w t, max u v w t} F) ≫
          (dgNerveUniverseLiftIso.{u, w, max u v w t} R E).inv := by
  ext n s
  apply ULift.ext
  apply Simplex.ext
  rfl

end SerrePositivity.InfinityCategories
