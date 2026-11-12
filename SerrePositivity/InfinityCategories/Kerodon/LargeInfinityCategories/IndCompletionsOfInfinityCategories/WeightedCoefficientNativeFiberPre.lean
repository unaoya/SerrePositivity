module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedCoefficientNativeValueFactorization

/-!
概要：元の native 評価余錐の実際の fiber 値写像は、必要な持ち上げた Kan 標的で前合成同値。
方針：元の係数値作用の前合成同値を同じ fiber 比較で写し、同じ native 復元を消去する。
規約：元の余錐と実際の fiber 値写像を固定。使われ方：指定係数余錐の native 余極限判定。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject C)
  (hF : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I) (x : C _⦋0⦌)
local notation "D" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeEvaluationDiagram κ F i x
local notation "z" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeEvaluationVertex κ F hF i x

/-- 元の制限全評価の値写像への前合成は、必要な持ち上げた Kan 標的で同値。 -/
lemma weightedCoefficientNativeRestrictedValueMap_pre (Z : SSet.{u}) [KanComplex Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeRestrictedValueMap κ F hF i x)).app
      ((SSet.uliftFunctor.{u + 1, u}).obj Z)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeFiberPointedIso κ F hF i x)
  have hg := e.isQCatEquivalence.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberValueEquivalence z).isQCatEquivalence
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeRestrictedValueMap_factorization, pre_map, NatTrans.comp_app]
  exact (hg.precompose ((SSet.uliftFunctor.{u + 1, u}).obj Z)).isSimplicialHomotopyEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientSourceValue_ulift_pre F i x Z)

omit hF in
/-- 同じ native 評価復元の持ち上げも、必要な Kan 標的で前合成同値。 -/
lemma weightedCoefficientNativeReconstructionLift_pre (Z : SSet.{u}) [KanComplex Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeReconstructionLift κ F i x)).app
      ((SSet.uliftFunctor.{u + 1, u}).obj Z)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeReconstructionLift, pre_map, NatTrans.comp_app]
  have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeReconstruction_isPrecompositionEquivalence κ F i x) Z
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso D))
    ((SSet.uliftFunctor.{u + 1, u}).obj Z)).isSimplicialHomotopyEquivalence.comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ulift_pre_homotopyEquivalence _ hs.isSimplicialHomotopyEquivalence)

/-- 元の native 評価余錐の実際の fiber 値写像への前合成も、必要な Kan 標的で同値。 -/
lemma weightedCoefficientNativeCoconeFiberValueMap_pre (Z : SSet.{u}) [KanComplex Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeFiberValueMapAt (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeEvaluationCocone κ F hF i x) z
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeEvaluationCocone_vertex κ F hF i x))).app
          ((SSet.uliftFunctor.{u + 1, u}).obj Z)) := by
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeValueComparisonIso κ F hF i x).map_pre
    ((SSet.uliftFunctor.{u + 1, u}).obj Z)
  have hq := (weightedCoefficientNativeRestrictedValueMap_pre κ F hF i x Z).isQCatEquivalence
  have hc := (hq.ofFunctorIso he.symm).isSimplicialHomotopyEquivalence
  rw [pre_map, NatTrans.comp_app] at hc
  exact (weightedCoefficientNativeReconstructionLift_pre κ F i x Z).cancel_right hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
