module

public import SerrePositivity.KST.Spectra.DoubleCircleRestriction
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeRestriction

/-!
概要：二つの Kan 円からの制限は源の交換と標的の後合成に関して自然。
方針：閉構造の両源の制限の一般的な自然性を適用する。
規約：Kan 性はこの厳密な可換式には不要。
使われ方：Goerss–Jardine I §7、HA §1.4.2。通常の二重円での計算を Kan 円へ戻す。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Kan 円から通常の円への二変数の制限は内部 Hom の交換と可換。
方針：両源の制限と交換の一般式を適用する。
規約：二つの円には同じ Kan 置換の単位を使う。
使われ方：Goerss–Jardine I §7。二重 loop の交換の成分を通常の円で判定する。 -/
theorem doubleCircleRestriction_exchange (Y : PointedSimplicialSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u} Y).hom ≫
      doubleCircleRestriction Y =
      doubleCircleRestriction Y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u}
          PointedSimplicialSet.circle.{u} Y).hom := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.restrictBoth_exchange
    (C := PointedSimplicialSet.{u}) CirclePower.unit.{u} CirclePower.unit.{u} Y
  simp only [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.restrictBoth, ← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  change (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u} Y).hom ≫
      doubleCircleRestriction Y = doubleCircleRestriction Y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u}
          PointedSimplicialSet.circle.{u} Y).hom at h
  exact h

/-- 概要：Kan 円からの二変数の制限は標的の写像の二重の後合成と可換。
方針：両源の制限の標的に関する自然性を適用する。
規約：標的の写像は任意。
使われ方：HA §1.4.2。標的の loop の符号反転の比較を制限で保つ。 -/
theorem doubleCircleRestriction_post {Y Z : PointedSimplicialSet.{u}} (v : Y ⟶ Z) :
    PointedObject.basedHomMap CirclePower.space.{u}
        (PointedObject.basedHomMap CirclePower.space.{u} v) ≫ doubleCircleRestriction Z =
      doubleCircleRestriction Y ≫ PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
        (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} v) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.restrictBoth_post
    (C := PointedSimplicialSet.{u}) CirclePower.unit.{u} CirclePower.unit.{u} v
  simp only [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.restrictBoth, ← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  change PointedObject.basedHomMap CirclePower.space.{u}
      (PointedObject.basedHomMap CirclePower.space.{u} v) ≫ doubleCircleRestriction Z =
    doubleCircleRestriction Y ≫ PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
      (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} v) at h
  exact h

end

end SerrePositivity.KST.Spectra
