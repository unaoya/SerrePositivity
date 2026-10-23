module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomTransportRestriction
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNaturalitySectionCoherence
public import SerrePositivity.InfinityCategories.F1.HomTransportSquareIdentity

/-!
概要：元の底制限の輸送正方形は、同じ比較 Hom 上で指定境界の等式を満たす。
方針：同じ元の span・切断・制限射に輸送正方形の回収則を適用する。
規約：既存の制限自然性同型を選び直さない。
使われ方：元の分類 Hom の大域自然性を共有頂点へ制限する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の底制限した比較 span の一射影は充満忠実。 -/
lemma cocartesianBaseChangeRestrictedHomSpanOne_isFullyFaithful :
    IsFullyFaithful (cocartesianBaseChangeRestrictedHomSpanOne l k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeRestrictedHomSpanOne l k p q) :=
    cocartesianBaseChangeRestrictedHomSpanOne_trivialKanFibration l k p q
  exact isFullyFaithful_of_trivialKanFibration _

/-- 既存の元の制限自然性は、同じ共通 Hom 上で指定された四辺の等式を満たす。 -/
lemma cocartesianBaseChangeHomTransport_restrictionIso_identity :
    HomTransportSquareCommutes
      (cocartesianBaseChangeHomSpanZero k p q) (cocartesianBaseChangeHomSpanOne k p q)
      (cocartesianBaseChangeRestrictedHomSpanZero l k p q)
      (cocartesianBaseChangeRestrictedHomSpanOne l k p q)
      (cocartesianBaseChangeRestrictedHomMap l k p q)
      (cocartesianBaseChangeHomTransport k p q)
      (cocartesianBaseChangeRestrictedHomTransport l k p q) (cocartesianBaseChangeHomRestrictionZero l k p q) (cocartesianBaseChangeHomRestrictionOne l k p q)
      (homSpanSectionBoundaryIso
        (cocartesianBaseChangeHomSpanOne k p q) (cocartesianBaseChangeHomSpanZero k p q)
        (cocartesianBaseChangeHomSpanOneSection k p q)
        (cocartesianBaseChangeHomSpanOne_isFullyFaithful k p q)
        (cocartesianBaseChangeHomSpanOneSection_projection k p q))
      (homSpanSectionBoundaryIso
        (cocartesianBaseChangeRestrictedHomSpanOne l k p q)
        (cocartesianBaseChangeRestrictedHomSpanZero l k p q)
        (cocartesianBaseChangeRestrictedHomSpanOneSection l k p q)
        (cocartesianBaseChangeRestrictedHomSpanOne_isFullyFaithful l k p q)
        (cocartesianBaseChangeRestrictedHomSpanOneSection_projection l k p q))
      (eqToIso (congrArg (fun f ↦ SSet.HomotopyCategory.mk (functorVertex f))
        (cocartesianBaseChangeRestrictedHomMap_zero l k p q)))
      (eqToIso (congrArg (fun f ↦ SSet.HomotopyCategory.mk (functorVertex f))
        (cocartesianBaseChangeRestrictedHomMap_one l k p q)))
      (cocartesianBaseChangeHomTransport_restrictionIso l k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne k p q) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration k p q
  have : TrivialKanFibration (cocartesianBaseChangeRestrictedHomSpanOne l k p q) :=
    cocartesianBaseChangeRestrictedHomSpanOne_trivialKanFibration l k p q
  exact homSpanSectionTransportNaturalityIso_identity
    (cocartesianBaseChangeHomSpanZero k p q) (cocartesianBaseChangeHomSpanOne k p q)
    (cocartesianBaseChangeRestrictedHomSpanZero l k p q)
    (cocartesianBaseChangeRestrictedHomSpanOne l k p q)
    (cocartesianBaseChangeRestrictedHomMap l k p q)
    (cocartesianBaseChangeHomSpanOneSection k p q)
    (cocartesianBaseChangeRestrictedHomSpanOneSection l k p q) (cocartesianBaseChangeHomRestrictionZero l k p q) (cocartesianBaseChangeHomRestrictionOne l k p q)
    (isQCatEquivalence_of_trivialKanFibration _) (isFullyFaithful_of_trivialKanFibration _)
    (cocartesianBaseChangeHomSpanOneSection_projection k p q)
    (cocartesianBaseChangeRestrictedHomSpanOneSection_projection l k p q)
    (cocartesianBaseChangeRestrictedHomMap_zero l k p q)
    (cocartesianBaseChangeRestrictedHomMap_one l k p q)

end SerrePositivity.InfinityCategories
