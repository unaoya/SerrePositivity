module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldSourceRestrictionMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldSourceDiagramIdentity

/-!
概要：元の補正比較は、同じ source 制限と既存の厳密 pullback 比較の合成。
方針：元の二つの射影で同じ元の底変換と補正成分を回収する。
規約：元の全 Hom・元の source 制限・指定補正比較を保持する。
使われ方：source Segal 同値から元の分類 Hom 作用の同値性への接続。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))
local notation "S" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldLocalSource n k p q

/-- 同じ厳密 pullback 比較の最初の射影は、元の最初の補正成分。 -/
lemma cocartesianScaffoldStrictPullbackMap_fst :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldStrictPullbackMap n k p q ≫ pullback.fst _ _ =
    pullback.fst ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedFirstSquare n k p q).map :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap_fst _ _ _ _ _ _ _ _ _

/-- 同じ厳密 pullback 比較の次の射影は、元の次の補正成分。 -/
lemma cocartesianScaffoldStrictPullbackMap_snd :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldStrictPullbackMap n k p q ≫ pullback.snd _ _ =
    pullback.snd ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedSecondSquare n k p q).map :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap_snd _ _ _ _ _ _ _ _ _

/-- 元の全 Hom 上の補正比較は、同じ source 制限と既存の厳密 pullback 同値の合成。 -/
lemma cocartesianScaffoldCorrectedGlobalPullbackMap_factor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSourceRestrictionMap n k p q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldStrictPullbackMap n k p q =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedGlobalPullbackMap n k p q := by
  apply pullback.hom_ext
  · rw [Category.assoc, cocartesianScaffoldStrictPullbackMap_fst, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSourceRestrictionMap_fst,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedGlobalPullbackMap_fst]
    rfl
  · rw [Category.assoc, cocartesianScaffoldStrictPullbackMap_snd, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSourceRestrictionMap_snd,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldCorrectedGlobalPullbackMap_snd]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
