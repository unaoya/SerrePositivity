module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NativeCoconeIsoRepresentative
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PresheafEvaluationCoconeComparison

/-!
概要：指定前層余極限の各点の一意比較を、元の余錐変換と標準単位変換の可換式へ移す。
方針：同じ coslice の代表辺を全余錐と頂点で共有し、底が恒等となる正方形を使う。
規約：各点の比較が自然な族だとは仮定せず、元の全余錐の代表辺を保持する。
使われ方：実際の余極限頂点関手の全脚と標準全評価 Kan 脚の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SSet.Truncated.HomotopyCategory
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)
  (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r)
  (hq : ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x) q))
  (x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌)

/-- 同じ元の評価余錐比較を全余錐と頂点で共有する、一つの可逆な代表辺。 -/
def presheafEvaluationComparisonEdge :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationCoconeIso r q hq x)

/-- 同じ代表を元の全余錐の関手間へ写した、元の評価余錐と標準余錐の変換。 -/
def presheafEvaluationComparisonWholeEdge :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge (presheafEvaluationComparisonEdge r q hq x)

/-- 同じ元の代表を頂点へ写した、元の評価余極限頂点と標準頂点の比較辺。 -/
def presheafEvaluationComparisonApexEdge :=
  (presheafEvaluationComparisonEdge r q hq x).map
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x)))

/-- 同じ全余錐比較の右頂点制限は、同じ元の頂点比較辺の全一単体。 -/
lemma presheafEvaluationComparisonWholeEdge_apex :
    ((presheafEvaluationComparisonWholeEdge r q hq x).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRightApexVertex ((SSet.uliftFunctor.{u + 1, u}).obj B)))).edge =
        (presheafEvaluationComparisonApexEdge r q hq x).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge_apex (presheafEvaluationComparisonEdge r q hq x)

/-- 元の標準単位変換は、元の評価余錐の変換と同じ頂点比較変換の合成を表す。 -/
lemma presheafEvaluationComparison_unit_square :
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x)))).toTruncated =
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x) q))).toTruncated ≫
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeTop (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x) q)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x))
      (presheafEvaluationComparisonWholeEdge r q hq x).toTruncated).toTruncated :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge_unit_square (presheafEvaluationComparisonEdge r q hq x)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
