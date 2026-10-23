module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeRestrictionSquareIdentity
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.HomTransportSquarePrecomposition
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNaturalitySectionCoherence
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.HomTransportSquareIdentity

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

/-- 元の全 Hom 作用上で、同じ指定底制限正方形の四辺が整合する。 -/
lemma cocartesianBaseChangeHomTransport_restrictionIso_originalHom_identity :
    let a := (cocartesianBaseChangeHomComparison k p q)
    HomTransportSquareCommutes
      (a ≫ cocartesianBaseChangeHomSpanZero k p q)
      (a ≫ cocartesianBaseChangeHomSpanOne k p q)
      (cocartesianBaseChangeRestrictedHomSpanZero l k p q)
      (cocartesianBaseChangeRestrictedHomSpanOne l k p q)
      (a ≫ cocartesianBaseChangeRestrictedHomMap l k p q)
      (cocartesianBaseChangeHomTransport k p q)
      (cocartesianBaseChangeRestrictedHomTransport l k p q)
      (cocartesianBaseChangeHomRestrictionZero l k p q)
      (cocartesianBaseChangeHomRestrictionOne l k p q)
      ((homSpanSectionBoundaryIso
        (cocartesianBaseChangeHomSpanOne k p q) (cocartesianBaseChangeHomSpanZero k p q)
        (cocartesianBaseChangeHomSpanOneSection k p q)
        (cocartesianBaseChangeHomSpanOne_isFullyFaithful k p q)
        (cocartesianBaseChangeHomSpanOneSection_projection k p q)).precomp a)
      (homSpanSectionBoundaryIso
        (cocartesianBaseChangeRestrictedHomSpanOne l k p q)
        (cocartesianBaseChangeRestrictedHomSpanZero l k p q)
        (cocartesianBaseChangeRestrictedHomSpanOneSection l k p q)
        (cocartesianBaseChangeRestrictedHomSpanOne_isFullyFaithful l k p q)
        (cocartesianBaseChangeRestrictedHomSpanOneSection_projection l k p q))
      (FunctorIso.precomp (eqToIso (congrArg
        (fun f ↦ SSet.HomotopyCategory.mk (functorVertex f))
        (cocartesianBaseChangeRestrictedHomMap_zero l k p q))) a)
      (FunctorIso.precomp (eqToIso (congrArg
        (fun f ↦ SSet.HomotopyCategory.mk (functorVertex f))
        (cocartesianBaseChangeRestrictedHomMap_one l k p q))) a)
      (cocartesianBaseChangeHomTransport_restrictionIso l k p q) := by
  exact HomTransportSquareCommutes.precomp _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (cocartesianBaseChangeHomTransport_restrictionIso_identity l k p q)
    (cocartesianBaseChangeHomComparison k p q)

end SerrePositivity.InfinityCategories
