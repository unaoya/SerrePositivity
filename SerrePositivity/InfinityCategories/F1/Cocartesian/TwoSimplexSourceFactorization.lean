module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexSourceRestrictionMap
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexSourceDiagramIdentity

/-!
概要：元の補正比較は、同じ source 制限と既存の厳密 pullback 比較の合成。
方針：元の二つの射影で同じ元の底変換と補正成分を回収する。
規約：元の全 Hom・元の source 制限・指定補正比較を保持する。
使われ方：source Segal 同値から元の分類 Hom 作用の同値性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "S" => cocartesianTwoSimplexLocalSource k p q

/-- 同じ厳密 pullback 比較の最初の射影は、元の最初の補正成分。 -/
lemma cocartesianTwoSimplexStrictPullbackMap_fst :
    cocartesianTwoSimplexStrictPullbackMap k p q ≫ pullback.fst _ _ =
    pullback.fst ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) ≫
      (cocartesianTwoSimplexCorrectedFirstSquare k p q).map :=
  spanPullbackMap_fst _ _ _ _ _ _ _ _ _

/-- 同じ厳密 pullback 比較の次の射影は、元の次の補正成分。 -/
lemma cocartesianTwoSimplexStrictPullbackMap_snd :
    cocartesianTwoSimplexStrictPullbackMap k p q ≫ pullback.snd _ _ =
    pullback.snd ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) ≫
      (cocartesianTwoSimplexCorrectedSecondSquare k p q).map :=
  spanPullbackMap_snd _ _ _ _ _ _ _ _ _

/-- 元の全 Hom 上の補正比較は、同じ source 制限と既存の厳密 pullback 同値の合成。 -/
lemma cocartesianTwoSimplexCorrectedGlobalPullbackMap_factor :
    cocartesianTwoSimplexSourceRestrictionMap k p q ≫
      cocartesianTwoSimplexStrictPullbackMap k p q =
    cocartesianTwoSimplexCorrectedGlobalPullbackMap k p q := by
  apply pullback.hom_ext
  · rw [Category.assoc, cocartesianTwoSimplexStrictPullbackMap_fst, ← Category.assoc,
      cocartesianTwoSimplexSourceRestrictionMap_fst,
      cocartesianTwoSimplexCorrectedGlobalPullbackMap_fst]
    rfl
  · rw [Category.assoc, cocartesianTwoSimplexStrictPullbackMap_snd, ← Category.assoc,
      cocartesianTwoSimplexSourceRestrictionMap_snd,
      cocartesianTwoSimplexCorrectedGlobalPullbackMap_snd]
    rfl

end SerrePositivity.InfinityCategories
