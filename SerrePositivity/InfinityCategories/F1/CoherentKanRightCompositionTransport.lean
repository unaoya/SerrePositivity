module

public import SerrePositivity.InfinityCategories.F1.CoherentCompositionIntervalSquare
public import SerrePositivity.InfinityCategories.F1.TransportIntervalSquareConstant
public import SerrePositivity.InfinityCategories.F1.TransportIntervalSquareVertices
public import SerrePositivity.InfinityCategories.F1.PointedRightFiberComparison

/-!
概要：元の Kan の右 Hom の豊穣合成と、同じ pointed-space 輸送の合成則を比較する。
方針：標準 Kan 頂点で正規化した同じ合成四角形から、定値辺の輸送を消去する。
規約：二つの元の Hom と動く始点の全パラメーターを保つ。
使われ方：右 Hom の点評価を、元の内部 Hom の評価と同じ fiber 比較へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の Kan の右 Hom の区間族を、同じ標準の空間の頂点で正規化する。 -/
def coherentKanRightHomInterval (K L : KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L) ⟶
      intervalMappingSpace (spaceInfinityVertex K) (spaceInfinityVertex L) :=
  coherentHomComparison K L ≫
    pinchedHomToIntervalMappingSpace (coherentNerveVertex K) (coherentNerveVertex L) ≫
    intervalMappingPostOfEq (𝟙 SpaceInfinity.{u}) (coherentNerveVertex K) (coherentNerveVertex L)
      (spaceInfinityVertex_eq_coherent K).symm (spaceInfinityVertex_eq_coherent L).symm

/-- 元の Kan の二つの Hom の合成四角形を、同じ標準頂点で正規化する。 -/
def coherentKanRightCompositionSquare (K L M : KanObject.{u}) :
    TransportIntervalSquare
      ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L) ⊗
        (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom L M))
      (spaceInfinityVertex K) (spaceInfinityVertex L) (spaceInfinityVertex M)
      (spaceInfinityVertex M) :=
  (coherentCompositionIntervalSquare K L M).changeVertices
    (spaceInfinityVertex_eq_coherent K).symm (spaceInfinityVertex_eq_coherent L).symm
    (spaceInfinityVertex_eq_coherent M).symm (spaceInfinityVertex_eq_coherent M).symm

/-- 正規化後も、同じ最終辺の区間全体は最終対象に厳密に定値。 -/
lemma coherentKanRightCompositionSquare_top (K L M : KanObject.{u}) :
    intervalMappingUncurry (coherentKanRightCompositionSquare K L M).top =
      SSet.const (spaceInfinityVertex M) := by
  dsimp only [coherentKanRightCompositionSquare, TransportIntervalSquare.changeVertices]
  rw [intervalMappingPostOfEq_uncurry, Category.comp_id, coherentCompositionIntervalSquare_top]
  exact congrArg (fun z ↦ SSet.const z) (spaceInfinityVertex_eq_coherent M).symm

/-- 元の全 Kan Hom 上で、二段の pointed 輸送は実際の豊穣合成に沿う輸送と同型。 -/
def coherentKanRightCompositionTransportIso (K L M : KanObject.{u})
    (f : ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L) ⊗
      (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom L M)) ⟶
      vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) :
    FunctorIso
      (diagonalFiberTransport pointedSpaceProjection
        (diagonalFiberTransport pointedSpaceProjection f
          (fst _ _ ≫ coherentKanRightHomInterval K L))
        (snd _ _ ≫ coherentKanRightHomInterval L M))
      (diagonalFiberTransport pointedSpaceProjection f
        (coherentHomComposition K L M ≫ coherentKanRightHomInterval K M)) :=
  (coherentKanRightCompositionSquare K L M).constantTopIso pointedSpaceProjection f
    (coherentKanRightCompositionSquare_top K L M)

/-- 任意のパラメーター上の二つの元の Hom を、同じ固定始点からの合成則へ同時に制限する。 -/
def coherentKanRightCompositionTransport_diagonalIso (K L M : KanObject.{u})
    {P : SSet.{u + 1}}
    (v : (vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) _⦋0⦌)
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
    (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom L M)) :
    FunctorIso
      (diagonalFiberTransport pointedSpaceProjection
        (diagonalFiberTransport pointedSpaceProjection (SSet.const v)
          (x ≫ coherentKanRightHomInterval K L))
        (y ≫ coherentKanRightHomInterval L M))
      (diagonalFiberTransport pointedSpaceProjection (SSet.const v)
        (lift x y ≫ coherentHomComposition K L M ≫ coherentKanRightHomInterval K M)) := by
  have h := FunctorIso.precomp
    (coherentKanRightCompositionTransportIso K L M (SSet.const v)) (lift x y)
  simpa only [diagonalFiberTransport_precomp, SSet.comp_const, ← Category.assoc,
    lift_fst, lift_snd] using h

end SerrePositivity.InfinityCategories
