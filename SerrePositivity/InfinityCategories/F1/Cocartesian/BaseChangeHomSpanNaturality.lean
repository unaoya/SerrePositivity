module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomSpan

/-!
概要：同じ比較 Hom の二射影は、元の二つの分類 Hom 作用を厳密に回収する。
方針：元の全区間族を展開し、同じ比較 path の両端の等式を使う。
規約：元の全相対 Hom の core、元の分類写像、元の底変換を固定する。
使われ方：同じ Hom 比較作用のセルによる降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ比較 Hom の零射影は、元の Hom 作用を同じ底で制限したもの。 -/
lemma cocartesianBaseChangeHomComparison_zero :
    cocartesianBaseChangeHomComparison k p q ≫ cocartesianBaseChangeHomSpanZero k p q =
      cocartesianStraighteningHomInterval p q ≫
        intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))
          (cocartesianStrictTransportCoherentDiagram p.val.hom)
          (cocartesianStrictTransportCoherentDiagram q.val.hom) := by
  apply intervalMappingUncurry_injective
  rw [cocartesianBaseChangeHomSpanZero, intervalHomPathEndpoint_uncurry,
    cocartesianBaseChangeHomComparison_uncurry, intervalDiagramRestriction_uncurry,
    cocartesianStraighteningHomInterval_uncurry]
  have h := congrArg (fun m ↦ rightMappingSpacePrism _ ≫
    pinchedHomUncurry (coherentHomComparison p q) ≫ m) (cocartesianBaseChangeHomPath_zero k)
  simpa only [CatInfinityFunctor, Category.assoc] using h

/-- 同じ比較 Hom の一射影は、元の Hom の底変換後の同じ分類作用。 -/
lemma cocartesianBaseChangeHomComparison_one :
    cocartesianBaseChangeHomComparison k p q ≫ cocartesianBaseChangeHomSpanOne k p q =
      (SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
          cocartesianStraighteningHomInterval
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) := by
  rw [← cocartesianStraighteningHomInterval_baseChange k p q]
  apply intervalMappingUncurry_injective
  rw [cocartesianBaseChangeHomSpanOne, intervalHomPathEndpoint_uncurry,
    cocartesianBaseChangeHomComparison_uncurry, quasicategoryEnrichedDiagramHomInterval_uncurry,
    QuasicategoryEnrichedDiagram.realization_precompose,
    cocartesianStrictTransportEnrichedDiagram_realization]
  have h := congrArg (fun m ↦ rightMappingSpacePrism _ ≫
    pinchedHomUncurry (coherentHomComparison p q) ≫ m) (cocartesianBaseChangeHomPath_one k)
  simpa only [CatInfinityFunctor, Category.assoc, cocartesianFibrationInfinityBaseChange,
    cocartesianFibrationBaseChangeCoreEnriched] using h

end SerrePositivity.InfinityCategories
