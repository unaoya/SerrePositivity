module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeRestrictionNaturalityTriangle
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeGlobalFactorNaturality
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.HomSpanSectionRestrictionRebase

/-!
概要：第一辺の制限自然性と指定因子の合成は、元の大域自然性の制限を回収する。
方針：同じ span の正規化した制限正方形と、源の指定因子の回収を貼り合わせる。
規約：既存の制限自然性と元の第一辺の指定同型を保持する。
使われ方：三辺の指定比較を元の大域自然性と局所自然性の同じ貼り合わせへ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の全 Hom 上で、制限自然性と第一辺の正規化した因子比較は元の源の因子比較。 -/
lemma cocartesianBaseChangeHomTransport_restrictionIso_rebasedNaturality_heq
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    HomSpanSectionRestrictionRebasedNaturalityAt
    (cocartesianBaseChangeHomSpanZero k p q) (cocartesianBaseChangeHomSpanOne k p q)
    (cocartesianBaseChangeRestrictedHomSpanZero l k p q)
    (cocartesianBaseChangeRestrictedHomSpanOne l k p q)
    (cocartesianBaseChangeRestrictedHomMap l k p q)
    (cocartesianBaseChangeHomSpanOneSection k p q)
    (cocartesianBaseChangeRestrictedHomSpanOneSection l k p q)
    (cocartesianBaseChangeHomRestrictionZero l k p q)
    (cocartesianBaseChangeHomRestrictionOne l k p q)
    (cocartesianBaseChangeHomSpanOne_isQCatEquivalence k p q)
    (cocartesianBaseChangeRestrictedHomSpanOne_isFullyFaithful l k p q)
    (cocartesianBaseChangeHomSpanOneSection_projection k p q)
    (cocartesianBaseChangeRestrictedHomSpanOneSection_projection l k p q)
    (cocartesianBaseChangeRestrictedHomMap_zero l k p q)
    (cocartesianBaseChangeRestrictedHomMap_one l k p q)
    (cocartesianBaseChangeHomComparison k p q)
    (cocartesianBaseChangeRestrictedGlobalFactor_source l k p q)
    (cocartesianBaseChangeRestrictedGlobalFactor_target l k p q)
    ((SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))
    (cocartesianStraighteningHomInterval p q ≫
      intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))
        (cocartesianStrictTransportCoherentDiagram p.val.hom)
        (cocartesianStrictTransportCoherentDiagram q.val.hom))
    (cocartesianBaseChangeHomComparison_one k p q)
    (cocartesianBaseChangeHomComparison_zero k p q)
    ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp
      (cocartesianBaseChangeHomRestrictionZero l k p q)) := by
  exact HomSpanSectionRestrictionNaturalityAt.rebase
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (cocartesianBaseChangeHomTransport_restrictionIso_originalNaturality_heq l k p q)

end SerrePositivity.InfinityCategories
