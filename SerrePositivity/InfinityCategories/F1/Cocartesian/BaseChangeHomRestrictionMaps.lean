module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeRestrictedHomMapEndpoints
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeRestrictedHomTransport
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomTransport
public import SerrePositivity.InfinityCategories.F1.HomTransportSquareCoherence

/-!
概要：元の底変換 Hom 輸送の両端に作用する同じ底制限の射を明示する。
方針：既存の intervalDiagramRestriction を元の二つの端点空間に型付けする。
規約：元の底制限作用そのもの。使われ方：指定輸送正方形の境界の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の同じ分類 Hom の底制限。 -/
def cocartesianBaseChangeHomRestrictionZero
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    intervalMappingSpace
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫ cocartesianStrictTransportCoherentDiagram p.val.hom))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫ cocartesianStrictTransportCoherentDiagram q.val.hom)) ⟶
    intervalMappingSpace
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫ (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫ cocartesianStrictTransportCoherentDiagram p.val.hom))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫ (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫ cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
            cocartesianStrictTransportCoherentDiagram p.val.hom)
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
            cocartesianStrictTransportCoherentDiagram q.val.hom)

/-- 元の同じ分類 Hom の底制限。 -/
def cocartesianBaseChangeHomRestrictionOne
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    intervalMappingSpace
      (functorVertex (cocartesianStrictTransportCoherentDiagram ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
      (functorVertex (cocartesianStrictTransportCoherentDiagram ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom)) ⟶
    intervalMappingSpace
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫ cocartesianStrictTransportCoherentDiagram ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫ cocartesianStrictTransportCoherentDiagram ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom)) :=
  intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))
          (cocartesianStrictTransportCoherentDiagram
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom)
          (cocartesianStrictTransportCoherentDiagram
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom)

end SerrePositivity.InfinityCategories
