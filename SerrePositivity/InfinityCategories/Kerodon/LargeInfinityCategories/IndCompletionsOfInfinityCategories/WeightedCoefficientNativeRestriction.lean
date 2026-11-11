module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedCoefficientNativeHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedCoefficientEvaluationImage
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.HomotopyTransformationRestriction

/-!
概要：共同密度変換の同じ係数・始点制限は、元の native 評価変換の指定頂点に一致する。
方針：元の native 評価の両端を厳密に回収し、同じ全円柱の制限公式を使う。
規約：元の図式・頂点を保持。使われ方：native 評価余錐の実際の unstraightening の像。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject C)
  (hF : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I) (x : C _⦋0⦌)
local notation "H" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsHomDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityProjection F)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityJointTargetDiagram F
local notation "D" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeEvaluationDiagram κ F i x
local notation "z" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeEvaluationVertex κ F hF i x
local notation "k" => CategoryTheory.Functor.map SSet.uliftFunctor
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientEvaluationBase F i x)

/-- 共同 Hom の同じ制限を、元の native 評価図式に厳密に正規化する。 -/
lemma weightedCoefficientNativeEvaluationBase_source : k ≫ H = D :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientEvaluationBase_source F i x).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeEvaluationDiagram_eq κ F i x).symm

/-- 共同分類の同じ制限を、元の native 評価頂点に厳密に正規化する。 -/
lemma weightedCoefficientNativeEvaluationBase_target : k ≫ G = SSet.const z :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientEvaluationBase_target F i x).trans
    (congrArg SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeEvaluationVertex_eq κ F hF i x).symm)

/-- 元の native 評価の両端を保持した、共同変換空間の実際の制限射。 -/
def weightedCoefficientNativeJointRestriction :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.normalizedLeftTransformationRestriction H G k D (SSet.const z)
    (weightedCoefficientNativeEvaluationBase_source κ F i x)
    (weightedCoefficientNativeEvaluationBase_target κ F hF i x)

/-- c1 の元の指定変換頂点を制限すると、同じ native 評価変換の指定頂点そのもの。 -/
lemma weightedCoefficientNativeJointRestriction_vertex :
    (weightedCoefficientNativeJointRestriction κ F hF i x).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningTransformationSpaceIso H G).hom.app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityTransformation F).realization.transformation)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeEvaluatedTransformation κ F hF i x := by
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homotopyTransformationVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityJointHomotopy F) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningTransformationSpaceIso H G).hom.app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityTransformation F).realization.transformation) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homotopyTransformationVertex_recovered _
  rw [← ht]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homotopyTransformationVertex_restriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityJointHomotopy F) k
    (weightedCoefficientNativeEvaluationBase_source κ F i x)
    (weightedCoefficientNativeEvaluationBase_target κ F hF i x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeEvaluationHomotopy κ F hF i x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeEvaluationHomotopy_h κ F hF i x)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficientNativeEvaluatedTransformation_eq κ F hF i x).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
