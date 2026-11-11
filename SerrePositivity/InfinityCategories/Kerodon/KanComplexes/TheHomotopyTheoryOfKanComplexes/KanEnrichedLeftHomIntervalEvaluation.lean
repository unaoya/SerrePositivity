module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedTwoSidedHomInterval
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.LeftIntervalNaturality

/-!
概要：共同実現した左 Hom 区間を、各対象の実際の豊穣作用で展開する。
方針：反転と宇宙持ち上げの交換を明示し、同じ左区間の豊穣自然性を使う。
規約：端点だけでなく区間と Hom の全パラメーターを保持する。
使われ方：weighted pointed prism の底の族を、元の係数の作用と照合する。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes


/-- 左区間の展開は、同じ反転係数を用いた元の左区間への共同実現の後合成。 -/
lemma kanEnrichedDiagramLeftHomInterval_uncurry
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {I : Type u} [SmallCategory I] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C I) (X Y : C)
    {F G : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (hF : D.evaluate X = F) (hG : D.evaluate Y = G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramLeftHomInterval D X Y hF hG) =
      (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom X Y)).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval X Y ≫ D.realization := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramLeftHomInterval, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, ← Category.assoc, ← whiskerLeft_comp,
    Iso.hom_inv_id,
    Category.id_comp]

/-- 全左区間を添字で評価すると、その添字の豊穣関手の coherent nerve を回収する。 -/
lemma kanEnrichedDiagramLeftHomInterval_evaluate
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {I : Type u} [SmallCategory I] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C I) (X Y : C)
    {F G : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (hF : D.evaluate X = F) (hG : D.evaluate Y = G) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramLeftHomInterval D X Y hF hG) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) =
      (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom X Y)).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (D.obj i) := by
  rw [kanEnrichedDiagramLeftHomInterval_uncurry, Category.assoc, Category.assoc,
    D.realization_evaluate]

/-- 評価後の左区間の全パラメーターは、同じ対象での実際の豊穣 Hom の作用。 -/
lemma kanEnrichedDiagramLeftHomInterval_evaluate_action
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {I : Type u} [SmallCategory I] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C I) (X Y : C)
    {F G : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (hF : D.evaluate X = F) (hG : D.evaluate Y = G) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramLeftHomInterval D X Y hF hG) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) =
      (Δ[1] ◁ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom X Y)).hom ≫
        SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map ((D.obj i).map X Y)))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval ((D.obj i).obj X) ((D.obj i).obj Y) := by
  rw [kanEnrichedDiagramLeftHomInterval_evaluate]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_enriched_naturality (D.obj i) X Y
  have h' := congrArg (fun f =>
    (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom X Y)).hom) ≫ f) h
  simpa only [whiskerLeft_comp, Category.assoc] using h'

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
