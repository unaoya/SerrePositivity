module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedHomIntervalNaturality

/-!
概要：豊穣図式の実際の区間作用は、始域の豊穣関手による前合成と厳密に可換。
方針：元の coherent な右 Hom prism の自然性と、共同実現の前合成の式を合成する。
規約：始域の局所 Kan 性は要求しない。
使われ方：strict transport の像の区間作用を、その同じ共同実現の充満忠実性へ渡す。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 実際の区間作用は、同じ豊穣 Hom の作用による前合成を厳密に回収する。 -/
lemma kanEnrichedDiagramHomInterval_precompose
    {C L : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L] {I : Type u} [SmallCategory I]
    (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C I) (R : EnrichedFunctor SSet.{u} L C) (X Y : L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramHomInterval (D.precompose R) X Y rfl rfl =
      (SSet.uliftFunctor.{u + 1, u}).map (R.map X Y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramHomInterval D (R.obj X) (R.obj Y) rfl rfl := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramHomInterval_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramHomInterval_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram.realization_precompose]
  have h := congrArg (fun f => f ≫ D.realization)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.coherentRightHomInterval_enriched_naturality R X Y)
  simpa only [Category.assoc] using h

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
