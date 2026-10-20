module

public import SerrePositivity.InfinityCategories.F1.FullyFaithfulIntervalMapping
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningMappingNaturality
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorPullbackSquare
public import SerrePositivity.InfinityCategories.F1.CoherentUnstraighteningMappingEquivalence
public import SerrePositivity.InfinityCategories.F1.TransportLocalizationUlift
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningRepresentation

/-!
概要：図式制限が充満忠実なら、同じ unstraightening の相対 Hom の始域制限は同値。
方針：c1 の全変換空間の底変換自然性で、比較射と引き戻し正方形の相対後合成を消去する。
規約：制限する底の射自体を圏同値と仮定しない。初頂点の局所化へ無条件に適用する。
使われ方：一般の S の充満忠実性に残る、初頂点引き戻しの実際の Hom 作用の証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 図式の充満忠実な制限は、元の unstraightening の始域制限の相対 Hom 作用を同値にする。 -/
lemma leftUnstraighteningSourceRestriction_isQCatEquivalence
    {B D : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B)
    (hk : IsFullyFaithful ((pre k).app SpaceInfinity.{u})) :
    IsQCatEquivalence
      (relativeFunctorOverPre (leftUnstraighteningProjection G)
        (leftUnstraighteningOverBaseMap F k)) := by
  have ht := hk.intervalMappingPost_isQCatEquivalence (functorVertex F) (functorVertex G)
  change IsQCatEquivalence (leftUnstraighteningTransformationRestriction F G k) at ht
  have hs := (qCatEquivalenceOfIso
    (relativeFunctorPullbackSquareIso (leftUnstraighteningProjection (k ≫ G))
      (leftUnstraighteningProjection G) k (leftUnstraighteningMap (k ≫ G) G k rfl)
      (leftUnstraighteningMap_isPullback (k ≫ G) G k rfl)
      (leftUnstraighteningProjection (k ≫ F)))).isQCatEquivalence
  have he := (ht.comp
    (leftUnstraighteningMappingSpaceMap_isQCatEquivalence (k ≫ F) (k ≫ G))).comp hs
  have hf := he.ofFunctorIso (leftUnstraighteningMappingSpaceMap_baseChangeIso F G k).symm
  exact (leftUnstraighteningMappingSpaceMap_isQCatEquivalence F G).cancel_left hf

/-- 初頂点の局所化に沿う、元の coherent unstraightening の始域制限は全相対 Hom で同値。 -/
lemma leftUnstraighteningFirstVertexSourceRestriction_isQCatEquivalence
    (B : SSet.{u})
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    IsQCatEquivalence
      (relativeFunctorOverPre (leftUnstraighteningProjection G)
        (leftUnstraighteningOverBaseMap F
          ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B)))) :=
  leftUnstraighteningSourceRestriction_isQCatEquivalence F G _
    (localization_pre_isFullyFaithful
      (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} B) SpaceInfinity.{u})

end SerrePositivity.InfinityCategories
