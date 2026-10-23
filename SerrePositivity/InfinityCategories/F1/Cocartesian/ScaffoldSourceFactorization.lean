module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldSourceRestrictionMap
public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldSourceDiagramIdentity

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

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "S" => cocartesianScaffoldLocalSource n k p q

/-- 同じ厳密 pullback 比較の最初の射影は、元の最初の補正成分。 -/
lemma cocartesianScaffoldStrictPullbackMap_fst :
    cocartesianScaffoldStrictPullbackMap n k p q ≫ pullback.fst _ _ =
    pullback.fst ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) ≫
      (cocartesianScaffoldCorrectedFirstSquare n k p q).map :=
  spanPullbackMap_fst _ _ _ _ _ _ _ _ _

/-- 同じ厳密 pullback 比較の次の射影は、元の次の補正成分。 -/
lemma cocartesianScaffoldStrictPullbackMap_snd :
    cocartesianScaffoldStrictPullbackMap n k p q ≫ pullback.snd _ _ =
    pullback.snd ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) ≫
      (cocartesianScaffoldCorrectedSecondSquare n k p q).map :=
  spanPullbackMap_snd _ _ _ _ _ _ _ _ _

/-- 元の全 Hom 上の補正比較は、同じ source 制限と既存の厳密 pullback 同値の合成。 -/
lemma cocartesianScaffoldCorrectedGlobalPullbackMap_factor :
    cocartesianScaffoldSourceRestrictionMap n k p q ≫
      cocartesianScaffoldStrictPullbackMap n k p q =
    cocartesianScaffoldCorrectedGlobalPullbackMap n k p q := by
  apply pullback.hom_ext
  · rw [Category.assoc, cocartesianScaffoldStrictPullbackMap_fst, ← Category.assoc,
      cocartesianScaffoldSourceRestrictionMap_fst,
      cocartesianScaffoldCorrectedGlobalPullbackMap_fst]
    rfl
  · rw [Category.assoc, cocartesianScaffoldStrictPullbackMap_snd, ← Category.assoc,
      cocartesianScaffoldSourceRestrictionMap_snd,
      cocartesianScaffoldCorrectedGlobalPullbackMap_snd]
    rfl

end SerrePositivity.InfinityCategories
