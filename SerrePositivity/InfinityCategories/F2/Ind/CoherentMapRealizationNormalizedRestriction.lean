module

public import SerrePositivity.InfinityCategories.F2.Ind.CoherentMapRealizationBaseChange
public import SerrePositivity.InfinityCategories.F1.Transport.ParametrizedPointTransportSquare

/-!
概要：元の c1 の底変換比較を、制限後の指定された二図式の表示で保持する。
方針：図式の等式で両端だけを正規化し、元の全変換空間の自然性を使う。
規約：元の変換頂点と元の全空間の射を保持する。
使われ方：評価密度変換の unstraightening の像の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 制限した図式の指定表示を両端とする、元の変換空間の実際の制限射。 -/
def normalizedLeftTransformationRestriction {B D : SSet.{u + 1}}
    (H G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) (H' G' : D ⟶ SpaceInfinity.{u})
    (hf : k ≫ H = H') (hg : k ≫ G = G') :
    leftUnstraighteningTransformationSpace H G ⟶ leftUnstraighteningTransformationSpace H' G' :=
  intervalMappingPostOfEq ((pre k).app SpaceInfinity) (functorVertex H) (functorVertex G)
    (congrArg functorVertex hf) (congrArg functorVertex hg)

/-- 表示を正規化した同じ制限変換の像は、元の実現射の底変換と相対的に同型。 -/
def coherentMapRealizationNormalizedRestrictionIso {B : SSet.{u}}
    (H G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (L : smallLeftUnstraightening H ⟶ smallLeftUnstraightening G)
    (hL : L ≫ smallLeftUnstraighteningProjection G = smallLeftUnstraighteningProjection H)
    (R : CoherentMapRealization H G L hL) {D : SSet.{u + 1}}
    (k : D ⟶ (SSet.uliftFunctor.{u + 1, u}).obj B) (H' G' : D ⟶ SpaceInfinity.{u})
    (hf : k ≫ H = H') (hg : k ≫ G = G') :
    VertexIso
      (((normalizedLeftTransformationRestriction H G k H' G' hf hg ≫
        leftUnstraighteningMappingSpaceMap H' G') ≫
          relativeFunctorSquarePost (leftUnstraighteningProjection G')
            (leftUnstraighteningProjection G) k (leftUnstraighteningMap G' G k hg)
            (leftUnstraighteningMap_projection G' G k hg)
            (leftUnstraighteningProjection H')).app (Opposite.op ⦋0⦌)
        ((smallLeftUnstraighteningTransformationSpaceIso H G).hom.app (Opposite.op ⦋0⦌)
          (ULift.up R.transformation)))
      ((relativeFunctorOverPre (leftUnstraighteningProjection G)
        (Over.homMk (leftUnstraighteningMap H' H k hf)
          (leftUnstraighteningMap_projection H' H k hf) :
            Over.mk (leftUnstraighteningProjection H' ≫ k) ⟶
              Over.mk (leftUnstraighteningProjection H))).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection H)
          (coherentRealizationLargeMap H G L)
          (coherentRealizationLargeMap_projection H G L hL))) := by
  subst H'
  subst G'
  simpa only [normalizedLeftTransformationRestriction, intervalMappingPostOfEq_refl,
    leftUnstraighteningTransformationRestriction, leftUnstraighteningOverBaseMap] using
      coherentMapRealizationBaseChangeIso H G L hL R k

end SerrePositivity.InfinityCategories.F2.Ind
