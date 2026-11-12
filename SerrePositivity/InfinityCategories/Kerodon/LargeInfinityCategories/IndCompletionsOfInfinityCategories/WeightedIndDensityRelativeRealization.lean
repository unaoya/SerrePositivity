module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedIndDensityCoefficient
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinTransformationClass

/-!
概要：元の weighted 密度変換を、両端と指定単位の類を保持する一つの相対 join 図式へ実現。
方針：既存の相対 join 円柱実現と、同じ円柱比較による両端の同時厳密化を使う。
規約：元の全変換と共同分類を固定。使われ方：同じ係数余錐の余極限性から大域比較へ戻す。

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
      (Opposite.op ⦋0⦌) v))

/-- 元の weighted 添字射影の同じ宇宙への持ち上げ。 -/
abbrev weightedIndDensityIndexProjection :=
  (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F))

/-- 元の weighted 全空間上の同じ Indκ 値の表現可能図式。 -/
abbrev weightedIndDensitySource :=
  (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityProjection F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C
local notation "p" => weightedIndDensityIndexProjection F
local notation "A" => weightedIndDensitySource κ F
local notation "B" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndClassification κ F hF

/-- 元の全変換の一つの相対 join 実現を、元の全円柱との比較とともに固定する。 -/
def weightedIndDensityRelativeRealization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanRelativeJoinRealization p A B (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndDensityHomotopy κ F hF) :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanRelativeJoinRealization_nonempty p A B
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndDensityHomotopy κ F hF))

/-- 同じ実現の両端を、一つの補正で元の二図式へ厳密化する。 -/
def weightedIndDensityRelativeStrictification :
    (weightedIndDensityRelativeRealization κ F hF).Strictification :=
  Classical.choice (weightedIndDensityRelativeRealization κ F hF).strictification_nonempty

/-- 同じ全変換を実現し、元の両端を厳密に持つ相対 join 図式。 -/
def weightedIndDensityRelativeDiagram : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 _) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C :=
  (weightedIndDensityRelativeStrictification κ F hF).diagram

lemma weightedIndDensityRelativeDiagram_left : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 _) ≫
    weightedIndDensityRelativeDiagram κ F hF = A :=
  (weightedIndDensityRelativeStrictification κ F hF).left_eq

lemma weightedIndDensityRelativeDiagram_right : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr p (𝟙 _) ≫
    weightedIndDensityRelativeDiagram κ F hF = B :=
  (weightedIndDensityRelativeStrictification κ F hF).right_eq

/-- 同じ相対 join 図式の prism を、元の全変換と同じ両端のホモトピーとして読む。 -/
def weightedIndDensityRelativeHomotopy : SSet.Homotopy A (p ≫ B) :=
  (weightedIndDensityRelativeStrictification κ F hF).transformation

/-- 同じ両端の厳密化は、元の指定単位の h Fun の類を保持する。 -/
lemma weightedIndDensityRelativeHomotopy_hom_eq :
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (weightedIndDensityRelativeHomotopy κ F hF)) =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedIndDensityHomotopy κ F hF)) :=
  (weightedIndDensityRelativeStrictification κ F hF).transformation_hom_eq

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
