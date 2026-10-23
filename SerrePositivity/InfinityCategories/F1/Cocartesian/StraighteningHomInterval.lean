module

public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedHomIntervalNaturality
public import SerrePositivity.InfinityCategories.F1.Cocartesian.StrictTransportEnrichedRealization
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeDiagramComparison
public import SerrePositivity.InfinityCategories.F1.Cocartesian.StrictTransportDiagram

/-!
概要：元の cocartesian Hom の core を、同じ分類図式間の実際の区間 Hom へ写す。
方針：元の全対象・全高次の豊穣図式の作用を使い、元の分類主写像へ戻す。
規約：底の制限と底変換後の作用も、元の同じ相対 Hom の作用として計算する。
使われ方：同じ分類 Hom 比較のセルによる降下と充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C]

/-- 元の相対 Hom の core から、同じ二つの分類図式の区間 Hom への実際の作用。 -/
def cocartesianStraighteningHomInterval (p q : CocartesianFibrationCategory (nerve C)) :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom p q) ⟶
      intervalMappingSpace
        (functorVertex (cocartesianStrictTransportCoherentDiagram p.val.hom))
        (functorVertex (cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  quasicategoryEnrichedDiagramHomInterval (cocartesianStrictTransportEnrichedDiagram C) p q

/-- 同じ作用を展開すると、元の Hom の prism と元の分類主写像の合成。 -/
lemma cocartesianStraighteningHomInterval_uncurry
    (p q : CocartesianFibrationCategory (nerve C)) :
    intervalMappingUncurry (cocartesianStraighteningHomInterval p q) =
      rightMappingSpacePrism _ ≫ pinchedHomUncurry (coherentHomComparison p q) ≫
        cocartesianStraighteningCoherentMap C := by
  rw [cocartesianStraighteningHomInterval, quasicategoryEnrichedDiagramHomInterval_uncurry,
    cocartesianStrictTransportEnrichedDiagram_realization]

/-- 同じ元の Hom 作用の底の制限は、元の豊穣図式を制限した同じ区間作用。 -/
lemma cocartesianStraighteningHomInterval_restrict
    {D : Type u} [Category.{u} D] (k : D ⥤ C)
    (p q : CocartesianFibrationCategory (nerve C)) :
    cocartesianStraighteningHomInterval p q ≫
      intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))
        (cocartesianStrictTransportCoherentDiagram p.val.hom)
        (cocartesianStrictTransportCoherentDiagram q.val.hom) =
      quasicategoryEnrichedDiagramHomInterval
        ((cocartesianStrictTransportEnrichedDiagram C).reindex k) p q :=
  (quasicategoryEnrichedDiagramHomInterval_reindex
    (cocartesianStrictTransportEnrichedDiagram C) k p q).symm

/-- 底変換した元の Hom に沿う同じ作用は、元の豊穣前合成の作用。 -/
lemma cocartesianStraighteningHomInterval_baseChange
    {D : Type u} [Category.{u} D] (k : D ⥤ C)
    (p q : CocartesianFibrationCategory (nerve C)) :
    quasicategoryEnrichedDiagramHomInterval
      ((cocartesianStrictTransportEnrichedDiagram D).precompose
        (cocartesianFibrationBaseChangeEnriched (nerveMap k))) p q =
      (SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
          cocartesianStraighteningHomInterval
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) :=
  quasicategoryEnrichedDiagramHomInterval_precompose
    (cocartesianStrictTransportEnrichedDiagram D)
    (cocartesianFibrationBaseChangeEnriched (nerveMap k)) p q

end SerrePositivity.InfinityCategories
