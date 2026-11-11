module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TwoSimplexTargetRestrictionLegs

/-!
概要：元の分類側の pullback 射は、同じ分類 Hom 作用と target 制限の合成。
方針：元の二辺への制限を同じ共有頂点で貼り、二射影を照合する。
規約：元の分類 Hom 作用を置き換えない。
使われ方：target Segal 同値による同じ分類 Hom 作用の同値性の反映。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory (nerve C))
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexLocalTarget k p q

/-- 元の分類先の同じ区間 Hom を、同じ二辺の厳密な pullback へ制限する。 -/
def cocartesianTwoSimplexTargetRestrictionMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram p.val.hom))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportCoherentDiagram q.val.hom)) ⟶
      pullback ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr) :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexTargetFirstRestriction k p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexTargetSecondRestriction k p q)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexTargetFirstRestriction_shared k p q).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexTargetSecondRestriction_shared k p q).symm)

/-- target 制限の最初の射影は同じ最初の辺への制限。 -/
lemma cocartesianTwoSimplexTargetRestrictionMap_fst :
    cocartesianTwoSimplexTargetRestrictionMap k p q ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexTargetFirstRestriction k p q := pullback.lift_fst _ _ _

/-- target 制限の次の射影は同じ次の辺への制限。 -/
lemma cocartesianTwoSimplexTargetRestrictionMap_snd :
    cocartesianTwoSimplexTargetRestrictionMap k p q ≫ pullback.snd _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexTargetSecondRestriction k p q := pullback.lift_snd _ _ _

/-- 元の分類側の二辺制限は、同じ元の分類 Hom 作用と target 制限の合成そのもの。 -/
lemma cocartesianTwoSimplexOriginalGlobalPullbackMap_factor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStraighteningHomInterval p q ≫ cocartesianTwoSimplexTargetRestrictionMap k p q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexOriginalGlobalPullbackMap k p q := by
  apply pullback.hom_ext
  · rw [Category.assoc, cocartesianTwoSimplexTargetRestrictionMap_fst,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexOriginalGlobalPullbackMap_fst]
    rfl
  · rw [Category.assoc, cocartesianTwoSimplexTargetRestrictionMap_snd,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTwoSimplexOriginalGlobalPullbackMap_snd]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
