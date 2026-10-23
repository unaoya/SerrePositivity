module

public import SerrePositivity.InfinityCategories.F2.Ind.CoherentMapRealizationLarge
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingNaturality

/-!
概要：元の c1 の実現同型を、同じ変換の底変換後の実際の像へ比較する。
方針：元の写像空間比較の全パラメータ自然性を指定変換で評価する。
規約：元の相対射を大きい全空間へ戻したものへの同型を保持する。
使われ方：密度変換の評価を元の全評価の制限へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {B : SSet.{u}}
  (H G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (L : smallLeftUnstraightening H ⟶ smallLeftUnstraightening G)
  (hL : L ≫ smallLeftUnstraighteningProjection G = smallLeftUnstraighteningProjection H)
  (R : CoherentMapRealization H G L hL)
  {D : SSet.{u + 1}} (k : D ⟶ (SSet.uliftFunctor.{u + 1, u}).obj B)

/-- 元の指定変換を制限して unstraighten した像は、元の実現射の制限と相対的に同型。 -/
def coherentMapRealizationBaseChangeIso :
    VertexIso
      (((leftUnstraighteningTransformationRestriction H G k ≫
        leftUnstraighteningMappingSpaceMap (k ≫ H) (k ≫ G)) ≫
          relativeFunctorSquarePost (leftUnstraighteningProjection (k ≫ G))
            (leftUnstraighteningProjection G) k (leftUnstraighteningMap (k ≫ G) G k rfl)
            (leftUnstraighteningMap_projection (k ≫ G) G k rfl)
            (leftUnstraighteningProjection (k ≫ H))).app (Opposite.op ⦋0⦌)
        ((smallLeftUnstraighteningTransformationSpaceIso H G).hom.app (Opposite.op ⦋0⦌)
          (ULift.up R.transformation)))
      ((relativeFunctorOverPre (leftUnstraighteningProjection G)
        (leftUnstraighteningOverBaseMap H k)).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection H)
          (coherentRealizationLargeMap H G L)
          (coherentRealizationLargeMap_projection H G L hL))) :=
  ((leftUnstraighteningMappingSpaceMap_baseChangeIso H G k).app
    ((smallLeftUnstraighteningTransformationSpaceIso H G).hom.app (Opposite.op ⦋0⦌)
      (ULift.up R.transformation))).symm ≪≫
    VertexIso.map (coherentMapRealizationLargeIso H G L hL R)
      (relativeFunctorOverPre (leftUnstraighteningProjection G)
        (leftUnstraighteningOverBaseMap H k))

end SerrePositivity.InfinityCategories.F2.Ind
