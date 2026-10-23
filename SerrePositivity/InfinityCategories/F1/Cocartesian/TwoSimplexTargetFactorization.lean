module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexTargetRestrictionLegs

/-!
概要：元の分類側の pullback 射は、同じ分類 Hom 作用と target 制限の合成。
方針：元の二辺への制限を同じ共有頂点で貼り、二射影を照合する。
規約：元の分類 Hom 作用を置き換えない。
使われ方：target Segal 同値による同じ分類 Hom 作用の同値性の反映。
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
local notation "T" => cocartesianTwoSimplexLocalTarget k p q

/-- 元の分類先の同じ区間 Hom を、同じ二辺の厳密な pullback へ制限する。 -/
def cocartesianTwoSimplexTargetRestrictionMap :
    intervalMappingSpace
      (functorVertex (cocartesianStrictTransportCoherentDiagram p.val.hom))
      (functorVertex (cocartesianStrictTransportCoherentDiagram q.val.hom)) ⟶
      pullback ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr) :=
  pullback.lift (cocartesianTwoSimplexTargetFirstRestriction k p q)
    (cocartesianTwoSimplexTargetSecondRestriction k p q)
    ((cocartesianTwoSimplexTargetFirstRestriction_shared k p q).trans
      (cocartesianTwoSimplexTargetSecondRestriction_shared k p q).symm)

/-- target 制限の最初の射影は同じ最初の辺への制限。 -/
lemma cocartesianTwoSimplexTargetRestrictionMap_fst :
    cocartesianTwoSimplexTargetRestrictionMap k p q ≫ pullback.fst _ _ =
      cocartesianTwoSimplexTargetFirstRestriction k p q := pullback.lift_fst _ _ _

/-- target 制限の次の射影は同じ次の辺への制限。 -/
lemma cocartesianTwoSimplexTargetRestrictionMap_snd :
    cocartesianTwoSimplexTargetRestrictionMap k p q ≫ pullback.snd _ _ =
      cocartesianTwoSimplexTargetSecondRestriction k p q := pullback.lift_snd _ _ _

/-- 元の分類側の二辺制限は、同じ元の分類 Hom 作用と target 制限の合成そのもの。 -/
lemma cocartesianTwoSimplexOriginalGlobalPullbackMap_factor :
    cocartesianStraighteningHomInterval p q ≫ cocartesianTwoSimplexTargetRestrictionMap k p q =
      cocartesianTwoSimplexOriginalGlobalPullbackMap k p q := by
  apply pullback.hom_ext
  · rw [Category.assoc, cocartesianTwoSimplexTargetRestrictionMap_fst,
      cocartesianTwoSimplexOriginalGlobalPullbackMap_fst]
    rfl
  · rw [Category.assoc, cocartesianTwoSimplexTargetRestrictionMap_snd,
      cocartesianTwoSimplexOriginalGlobalPullbackMap_snd]
    rfl

end SerrePositivity.InfinityCategories
