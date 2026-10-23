module

public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramUniversalEnriched
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalComparison
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostIso
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningTransformationFamily
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseOrdinaryLift

/-!
概要：豊穣図式の全 Hom を、実際の coherent な図式間の区間変換の族へ写す。
方針：標準右 Hom の全区間を共同実現へ後合成し、端点を元の図式に正規化する。
規約：変換空間や始域の局所 Kan 性を要求しない。
使われ方：反転 unstraightening の自然性四角形の全パラメーターの底の族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 全 Hom の元の標準区間を実現し、指定した二つの strict 図式間の変換空間へ写す。 -/
def kanEnrichedDiagramHomInterval {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I) (X Y : C)
    {F G : I ⥤ KanObject.{u}} (hF : D.evaluate X = F) (hG : D.evaluate Y = G) :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y) ⟶
      leftUnstraighteningTransformationSpace (kanDiagramCoherentNerve F)
        (kanDiagramCoherentNerve G) :=
  coherentHomComparison X Y ≫
    pinchedHomToIntervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y) ≫
    intervalMappingPostOfEq D.realization (coherentNerveVertex X) (coherentNerveVertex Y)
      ((D.realization_vertex X).trans (congrArg (fun F => functorVertex
        (kanDiagramCoherentNerve F)) hF))
      ((D.realization_vertex Y).trans (congrArg (fun G => functorVertex
        (kanDiagramCoherentNerve G)) hG))

/-- この同じ区間族の展開は、元の Hom の prism の共同実現への後合成そのもの。 -/
lemma kanEnrichedDiagramHomInterval_uncurry
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I) (X Y : C)
    {F G : I ⥤ KanObject.{u}} (hF : D.evaluate X = F) (hG : D.evaluate Y = G) :
    intervalMappingUncurry (kanEnrichedDiagramHomInterval D X Y hF hG) =
      rightMappingSpacePrism _ ≫ pinchedHomUncurry (coherentHomComparison X Y) ≫
        D.realization := by
  rw [kanEnrichedDiagramHomInterval, ← Category.assoc, intervalMappingPostOfEq_uncurry,
    pinchedHomToIntervalMappingSpace_uncurry]
  rfl

/-- 全 Hom の同じ区間族を底の対象で評価すると、対応する豊穣評価の元の作用。 -/
lemma kanEnrichedDiagramHomInterval_evaluate
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I) (X Y : C)
    {F G : I ⥤ KanObject.{u}} (hF : D.evaluate X = F) (hG : D.evaluate Y = G) (i : I) :
    intervalMappingUncurry (kanEnrichedDiagramHomInterval D X Y hF hG) ≫
      evaluateFunctorAt (ULift.up (nerveVertex i)) =
    rightMappingSpacePrism _ ≫ pinchedHomUncurry (coherentHomComparison X Y) ≫
      coherentNerveMap (D.obj i) := by
  rw [kanEnrichedDiagramHomInterval_uncurry, Category.assoc, Category.assoc,
    D.realization_evaluate]

/-- 全 strict 変換の共通 Hom 解像から、元の反転図式間の実際の coherent 区間族。 -/
def kanDiagramOppositeHomInterval {I : Type u} [SmallCategory I] (F G : KanDiagramObject I) :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (edgewiseSubdivision (SimplicialCategory.sHom F G)) ⟶
    leftUnstraighteningTransformationSpace
      (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))
      (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)) :=
  kanEnrichedDiagramHomInterval (kanDiagramUniversalEnriched I).opposite
    (edgewiseOrdinaryObject F) (edgewiseOrdinaryObject G) rfl rfl

/-- 反転変換の全区間族の各底対象での評価は、同じ反転した豊穣 Hom の実際の作用。 -/
lemma kanDiagramOppositeHomInterval_evaluate {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (i : I) :
    intervalMappingUncurry (kanDiagramOppositeHomInterval F G) ≫
      evaluateFunctorAt (ULift.up (nerveVertex i)) =
    rightMappingSpacePrism _ ≫ pinchedHomUncurry
      (coherentHomComparison (edgewiseOrdinaryObject F) (edgewiseOrdinaryObject G)) ≫
      coherentNerveMap (kanEnrichedFunctorOpposite (kanDiagramEvaluationEnriched i)) :=
  kanEnrichedDiagramHomInterval_evaluate (kanDiagramUniversalEnriched I).opposite
    (edgewiseOrdinaryObject F) (edgewiseOrdinaryObject G) rfl rfl i

end SerrePositivity.InfinityCategories
