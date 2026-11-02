module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CospanRectificationMaps
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IntervalPullbackDoubleReplacement

/-!
概要：同型で可換な Kan cospan 比較を共通の二脚置換後の厳密な引き戻しへ送る。
方針：元の指定同型で厳密化した左右成分と底成分を pullback.map に入れる。
規約：元の成分比較の同値性を保持。使われ方：native 比較候補への弱同値性の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {X Y Z X' Y' Z' : SSet.{u}}
  [KanComplex X] [KanComplex Y] [KanComplex Z]
  [KanComplex X'] [KanComplex Y'] [KanComplex Z']
  (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z')
  (s : X ⟶ X') (t : Y ⟶ Y') (v : Z ⟶ Z')
  (e : FunctorIso (f ≫ v) (s ≫ f')) (d : FunctorIso (g ≫ v) (t ≫ g'))

/-- 元の指定左右同型に沿う厳密化から構成する、同じ二脚置換後への実際の比較射。 -/
def cospanRectifiedPullbackComparison : intervalPullback f g ⟶
    pullback (intervalReplacementEndpoint f') (intervalReplacementEndpoint g') :=
  pullback.map (intervalReplacementEndpoint f) g
    (intervalReplacementEndpoint f') (intervalReplacementEndpoint g')
    (cospanRectificationLeftMap f f' s v e) (cospanRectificationRightMap g g' t v d) v
    (cospanRectificationLeftMap_over f f' s v e).symm
    (cospanRectificationRightMap_over g g' t v d).symm

/-- 同じ比較の第一射影は元の第一射影と指定左厳密化の合成。 -/
lemma cospanRectifiedPullbackComparison_left :
    cospanRectifiedPullbackComparison f g f' g' s t v e d ≫
      pullback.fst (intervalReplacementEndpoint f') (intervalReplacementEndpoint g') =
        pullback.fst (intervalReplacementEndpoint f) g ≫
          cospanRectificationLeftMap f f' s v e := pullback.lift_fst _ _ _

/-- 同じ比較の第二射影は元の第二入力と指定右厳密化の合成。 -/
lemma cospanRectifiedPullbackComparison_right :
    cospanRectifiedPullbackComparison f g f' g' s t v e d ≫
      pullback.snd (intervalReplacementEndpoint f') (intervalReplacementEndpoint g') =
        intervalPullbackRight f g ≫ cospanRectificationRightMap g g' t v d :=
  pullback.lift_snd _ _ _

/-- 元の三成分が同値なら、指定同型で厳密化した同じ引き戻し比較も同値。 -/
lemma cospanRectifiedPullbackComparison_homotopyEquivalence
    (hs : IsSimplicialHomotopyEquivalence s) (ht : IsSimplicialHomotopyEquivalence t)
    (hv : IsSimplicialHomotopyEquivalence v) :
    IsSimplicialHomotopyEquivalence (cospanRectifiedPullbackComparison f g f' g' s t v e d) := by
  apply strictKanPullbackMap_homotopyEquivalence
    (intervalReplacementEndpoint f) g (intervalReplacementEndpoint f')
    (intervalReplacementEndpoint g') (cospanRectificationLeftMap f f' s v e)
    (cospanRectificationRightMap g g' t v d) v
    (cospanRectificationLeftMap_over f f' s v e).symm
    (cospanRectificationRightMap_over g g' t v d).symm
  · exact cospanRectificationLeftMap_homotopyEquivalence f f' s v e hs
  · exact cospanRectificationRightMap_homotopyEquivalence g g' t v d ht
  · exact hv

end SerrePositivity.InfinityCategories.F2
