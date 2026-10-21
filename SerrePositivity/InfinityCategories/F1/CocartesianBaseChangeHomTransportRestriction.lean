module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeRestrictedHomMapEndpoints
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeRestrictedHomTransport
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeHomTransport
public import SerrePositivity.InfinityCategories.F1.HomTransportSquareCoherence

/-!
概要：既存の元の底変換 Hom 輸送は、元の図式の底の制限に関して自然。
方針：同じ比較 Hom の span の厳密な射と、指定された元の切断を使う。
規約：既存の cocartesianBaseChangeHomTransport を選び直さない。
使われ方：元の直接の Hom 輸送と二回の輸送の合成則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 既存の元の Hom 輸送と底の制限の正方形は、同じ全 Hom 作用の関手同型で可換。 -/
def cocartesianBaseChangeHomTransport_restrictionIso
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    FunctorIso
      (cocartesianBaseChangeHomTransport k p q ≫
        intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
            cocartesianStrictTransportCoherentDiagram p.val.hom)
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
            cocartesianStrictTransportCoherentDiagram q.val.hom))
      (intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))
          (cocartesianStrictTransportCoherentDiagram
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom)
          (cocartesianStrictTransportCoherentDiagram
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom) ≫
        cocartesianBaseChangeRestrictedHomTransport l k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne k p q) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration k p q
  have : TrivialKanFibration (cocartesianBaseChangeRestrictedHomSpanOne l k p q) :=
    cocartesianBaseChangeRestrictedHomSpanOne_trivialKanFibration l k p q
  exact homSpanSectionTransportNaturalityIso
    (cocartesianBaseChangeHomSpanZero k p q) (cocartesianBaseChangeHomSpanOne k p q)
    (cocartesianBaseChangeRestrictedHomSpanZero l k p q)
    (cocartesianBaseChangeRestrictedHomSpanOne l k p q)
    (cocartesianBaseChangeRestrictedHomMap l k p q)
    (cocartesianBaseChangeHomSpanOneSection k p q)
    (cocartesianBaseChangeRestrictedHomSpanOneSection l k p q)
    (intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
        cocartesianStrictTransportCoherentDiagram p.val.hom)
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
        cocartesianStrictTransportCoherentDiagram q.val.hom))
    (intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))
      (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom)
      (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom))
    (isQCatEquivalence_of_trivialKanFibration _) (isFullyFaithful_of_trivialKanFibration _)
    (cocartesianBaseChangeHomSpanOneSection_projection k p q)
    (cocartesianBaseChangeRestrictedHomSpanOneSection_projection l k p q)
    (cocartesianBaseChangeRestrictedHomMap_zero l k p q)
    (cocartesianBaseChangeRestrictedHomMap_one l k p q)

end SerrePositivity.InfinityCategories
