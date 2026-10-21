module

public import SerrePositivity.InfinityCategories.F1.QuasicategoryDiagramRealizationVertices
public import SerrePositivity.InfinityCategories.F1.MappingSpaceIntervalComparison
public import SerrePositivity.InfinityCategories.F1.IntervalDiagramRestriction

/-!
概要：元の全高次 Hom の core を、同じ評価図式間の実際の区間 Hom へ写す。
方針：標準右 Hom の全区間族を共同実現し、両端を元の図式に正規化する。
規約：変換空間の Kan 性を要求しない。
使われ方：元の分類 Hom 比較のセル制限に関する自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

local instance quasicategoryHomInterval_sourceCore_simplicialCategory
    {C : Type v} [Category.{u} C] [SimplicialCategory C] :
    SimplicialCategory (TransportEnrichment quasicategoryCoreFunctor.{u} C) :=
  TransportEnrichment.enrichedOrdinaryCategory C quasicategoryCoreFunctor.{u}
    quasicategoryCoreUnitHomEquiv quasicategoryCoreUnitHomEquiv_eq

variable {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
  {J : Type u} [Category.{u} J] (D : QuasicategoryEnrichedDiagram C J)
  (X Y : TransportEnrichment quasicategoryCoreFunctor.{u} C)

/-- 元の全 Hom の標準区間を、同じ二図式の間の区間変換の族へ写す。 -/
def quasicategoryEnrichedDiagramHomInterval :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y) ⟶
      intervalMappingSpace
        (functorVertex (qCatDiagramCoherentNerve
          (quasicategoryDiagramValueFunctor (D.toCoreEnrichedFunctor.obj X))))
        (functorVertex (qCatDiagramCoherentNerve
          (quasicategoryDiagramValueFunctor (D.toCoreEnrichedFunctor.obj Y)))) :=
  coherentHomComparison X Y ≫
    pinchedHomToIntervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y) ≫
      intervalMappingPostOfEq D.realization (coherentNerveVertex X) (coherentNerveVertex Y)
        (D.realization_vertex X) (D.realization_vertex Y)

/-- 同じ区間作用の展開は、元の全 Hom の prism の同じ共同実現。 -/
lemma quasicategoryEnrichedDiagramHomInterval_uncurry :
    intervalMappingUncurry (quasicategoryEnrichedDiagramHomInterval D X Y) =
      rightMappingSpacePrism _ ≫ pinchedHomUncurry (coherentHomComparison X Y) ≫
        D.realization := by
  rw [quasicategoryEnrichedDiagramHomInterval, ← Category.assoc,
    intervalMappingPostOfEq_uncurry, pinchedHomToIntervalMappingSpace_uncurry]
  rfl

end SerrePositivity.InfinityCategories
