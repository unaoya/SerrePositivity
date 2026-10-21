module

public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldTargetRestrictionLegs

/-!
概要：元の分類側の pullback 射は、同じ分類 Hom 作用と target 制限の合成。
方針：元の最初の辺と尾部への制限を同じ共有頂点で貼り、二射影を照合する。
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

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "T" => cocartesianScaffoldLocalTarget n k p q

/-- 元の分類先の同じ区間 Hom を、同じ最初の辺と尾部の厳密な pullback へ制限する。 -/
def cocartesianScaffoldTargetRestrictionMap :
    intervalMappingSpace
      (functorVertex (cocartesianStrictTransportCoherentDiagram p.val.hom))
      (functorVertex (cocartesianStrictTransportCoherentDiagram q.val.hom)) ⟶
      pullback ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr) :=
  pullback.lift (cocartesianScaffoldTargetFirstRestriction n k p q)
    (cocartesianScaffoldTargetSecondRestriction n k p q)
    ((cocartesianScaffoldTargetFirstRestriction_shared n k p q).trans
      (cocartesianScaffoldTargetSecondRestriction_shared n k p q).symm)

/-- target 制限の最初の射影は同じ最初の辺への制限。 -/
lemma cocartesianScaffoldTargetRestrictionMap_fst :
    cocartesianScaffoldTargetRestrictionMap n k p q ≫ pullback.fst _ _ =
      cocartesianScaffoldTargetFirstRestriction n k p q := pullback.lift_fst _ _ _

/-- target 制限の次の射影は同じ次の辺への制限。 -/
lemma cocartesianScaffoldTargetRestrictionMap_snd :
    cocartesianScaffoldTargetRestrictionMap n k p q ≫ pullback.snd _ _ =
      cocartesianScaffoldTargetSecondRestriction n k p q := pullback.lift_snd _ _ _

/-- 元の分類側の最初の辺と尾部制限は、同じ元の分類 Hom 作用と target 制限の合成そのもの。 -/
lemma cocartesianScaffoldOriginalGlobalPullbackMap_factor :
    cocartesianStraighteningHomInterval p q ≫ cocartesianScaffoldTargetRestrictionMap n k p q =
      cocartesianScaffoldOriginalGlobalPullbackMap n k p q := by
  apply pullback.hom_ext
  · rw [Category.assoc, cocartesianScaffoldTargetRestrictionMap_fst,
      cocartesianScaffoldOriginalGlobalPullbackMap_fst]
    rfl
  · rw [Category.assoc, cocartesianScaffoldTargetRestrictionMap_snd,
      cocartesianScaffoldOriginalGlobalPullbackMap_snd]
    rfl

end SerrePositivity.InfinityCategories
