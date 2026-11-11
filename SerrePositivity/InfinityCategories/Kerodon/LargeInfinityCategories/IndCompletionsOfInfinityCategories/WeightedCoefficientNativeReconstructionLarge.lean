module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedCoefficientNativeReconstruction
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoherentMapRealizationLarge

/-!
概要：同じ native 評価復元の大きい全空間への像と、元の共同実現射との合成を計算する。
方針：小さい復元の厳密な制限公式と、小さい unstraightening 比較の自然性を使う。
規約：元の native 評価図式と復元射を保持。使われ方：元の全評価の相対同型との合成。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject C) (i : I) (x : C _⦋0⦌)
local notation "H" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsHomDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityProjection F)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityJointTargetDiagram F
local notation "D" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeEvaluationDiagram κ F i x
local notation "k" => CategoryTheory.Functor.map SSet.uliftFunctor
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientEvaluationBase F i x)

/-- 同じ native 評価復元の大きい全空間への像は、元の全復元の同じ制限。 -/
lemma weightedCoefficientNativeReconstruction_largeMap :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeReconstruction κ F i x) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso D).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap D H k
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeEvaluationBase_source κ F i x) =
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientSourceIntoTotal F i x) ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsReconstruction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityProjection F)) ≫
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso H).hom := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningMap_naturality, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeReconstruction_map,
    CategoryTheory.Functor.map_comp, Category.assoc]

/-- 同じ native 評価復元と共同実現射の合成は、元の全評価同型の始域の同じ射。 -/
lemma weightedCoefficientNativeReconstruction_realization :
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeReconstruction κ F i x) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso D).hom) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap D H k
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeEvaluationBase_source κ F i x) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coherentRealizationLargeMap H G (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityTransformation F).map =
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientSourceIntoTotal F i x) ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsReconstruction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityProjection F) ≫
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityTransformation F).map) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso G).hom := by
  rw [← Category.assoc, Category.assoc
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeReconstruction κ F i x)),
    weightedCoefficientNativeReconstruction_largeMap]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coherentRealizationLargeMap, CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
