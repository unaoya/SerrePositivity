module

public import SerrePositivity.InfinityCategories.F1.CocartesianLocalHomComparison
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeHomTransportRestriction

/-!
概要：元の局所 Hom 比較をさらに制限し、元の局所分類作用との自然な正方形を構成する。
方針：二回目の元の底変換自然性と、既存の元の Hom 輸送の底制限自然性を合成する。
規約：元の全相対 Hom と元の分類図式の同じ二つの制限を保つ。
使われ方：二次元 Segal 比較の局所 Hom 作用の共有頂点との整合性。
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

/-- 元の二回の pullback 対象の全 Hom を、同じ二回の底制限をした元の分類 Hom へ写す。 -/
def cocartesianIteratedLocalHomComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p))
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))) ⟶
      intervalMappingSpace
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
          (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
            cocartesianStrictTransportCoherentDiagram p.val.hom))
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
          (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
            cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  cocartesianLocalHomComparison l
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) ≫
      cocartesianBaseChangeRestrictedHomTransport l k p q

/-- 元の局所 Hom の底変換と、元の分類 Hom のさらに底の制限は関手同型で整合する。 -/
def cocartesianIteratedLocalHomComparison_restrictionIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ≫
        cocartesianIteratedLocalHomComparison l k p q)
      (cocartesianLocalHomComparison k p q ≫
        intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
            cocartesianStrictTransportCoherentDiagram p.val.hom)
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
            cocartesianStrictTransportCoherentDiagram q.val.hom)) := by
  have e₁ := (cocartesianBaseChangeHomNaturalityIso l
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)).postcomp
      (cocartesianBaseChangeRestrictedHomTransport l k p q)
  have e₂ := FunctorIso.precomp (cocartesianBaseChangeHomTransport_restrictionIso l k p q).symm
    (cocartesianStraighteningHomInterval
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))
  simpa only [cocartesianIteratedLocalHomComparison, cocartesianLocalHomComparison,
    cocartesianBaseChangeHomRestrictionZero, Category.assoc] using e₁ ≪≫ e₂

end SerrePositivity.InfinityCategories
