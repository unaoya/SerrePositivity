module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSimplicialHomMapEndpoints
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSimplicialHomTransport
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomTransport
public import SerrePositivity.InfinityCategories.F1.HomTransportSquareCoherence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSimplicialRestrictionMaps

/-!
概要：既存の元の底変換 Hom 輸送は、元の図式の任意の単体集合への制限に関して自然。
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
def cocartesianBaseChangeHomTransport_simplicialRestrictionIso
    {D C : Type u} [Category.{u} D] [Category.{u} C] {A : SSet.{u + 1}}
    (a : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve D)) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    FunctorIso
      (cocartesianBaseChangeHomTransport k p q ≫
        cocartesianBaseChangeSimplicialRestrictionZero a k p q)
      (cocartesianBaseChangeSimplicialRestrictionOne a k p q ≫
        cocartesianBaseChangeSimplicialHomTransport a k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne k p q) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration k p q
  have : TrivialKanFibration (cocartesianBaseChangeSimplicialHomSpanOne a k p q) :=
    cocartesianBaseChangeSimplicialHomSpanOne_trivialKanFibration a k p q
  exact homSpanSectionTransportNaturalityIso
    (cocartesianBaseChangeHomSpanZero k p q) (cocartesianBaseChangeHomSpanOne k p q)
    (cocartesianBaseChangeSimplicialHomSpanZero a k p q)
    (cocartesianBaseChangeSimplicialHomSpanOne a k p q)
    (cocartesianBaseChangeSimplicialHomMap a k p q)
    (cocartesianBaseChangeHomSpanOneSection k p q)
    (cocartesianBaseChangeSimplicialHomSpanOneSection a k p q)
    (cocartesianBaseChangeSimplicialRestrictionZero a k p q)
    (cocartesianBaseChangeSimplicialRestrictionOne a k p q)
    (isQCatEquivalence_of_trivialKanFibration _) (isFullyFaithful_of_trivialKanFibration _)
    (cocartesianBaseChangeHomSpanOneSection_projection k p q)
    (cocartesianBaseChangeSimplicialHomSpanOneSection_projection a k p q)
    (cocartesianBaseChangeSimplicialHomMap_zero a k p q)
    (cocartesianBaseChangeSimplicialHomMap_one a k p q)

end SerrePositivity.InfinityCategories
