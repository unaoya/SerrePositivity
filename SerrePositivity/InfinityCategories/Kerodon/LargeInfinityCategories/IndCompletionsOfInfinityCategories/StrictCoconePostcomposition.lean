module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CoherentReturnPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.StrictConeFunctorImage
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.StrictNativeCocones
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareOpposite

/-!
概要：元の通常の余錐全体の coherent な表示は、豊穣関手の実際の後合成と可換。
方針：反対の錐の同じ比較を反転し、標準帰還写像の自然性で元へ戻す。
規約：join からの射の全次数の等式。脚や頂点だけの比較で代用しない。
使われ方：strict right straightening の指定余錐の fiber 比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

variable {I : Type u} [SmallCategory I] {C D : Type v}
  [Category.{u} C] [Category.{u} D] [SimplicialCategory C] [SimplicialCategory D]

/-- 余錐を写して反対にした錐の coherent な射は、元の反対の錐の同じ後合成。 -/
lemma strictCocone_oppositeCone_postcomp {F : I ⥤ C} (c : Cocone F)
    (R : EnrichedFunctor SSet.{u} C D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c.op).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialEnrichedOpposite R) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).mapCocone c).op).val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeMap c.op ≫ _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeMap _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.strictCoherentConeMap_postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coherentUnderlying_opposite]
  rfl

/-- 元の native な通常の余錐の全 join 射は、豊穣関手の実際の後合成で保たれる。 -/
lemma strictNativeCocone_postcomp_val {F : I ⥤ C} (c : Cocone F)
    (R : EnrichedFunctor SSet.{u} C D) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).mapCocone c)).val := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_val, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_val]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCocone
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconePost_val, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconePost_val]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeIndexIso I).hom (𝟙 Δ[0]) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c.op).reverseCocone.val) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentOppositeReturnIso C).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeIndexIso I).hom (𝟙 Δ[0]) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).mapCocone c).op).reverseCocone.val) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentOppositeReturnIso D).hom
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.JoinCone.reverseCocone_val, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.JoinCone.reverseCocone_val]
  simp only [Category.assoc]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coherentReturn_postcomp R,
    ← Category.assoc (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c.op).val)
      (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialEnrichedOpposite R)))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentOppositeReturnIso D).hom,
    ← CategoryTheory.Functor.map_comp, strictCocone_oppositeCone_postcomp]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
