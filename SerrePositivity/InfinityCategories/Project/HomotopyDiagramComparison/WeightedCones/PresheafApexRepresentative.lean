module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.Presheaves.PresheafEvaluationUnitComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.NativeCoconeApexIso

/-!
概要：同じ元の評価 coslice 代表の頂点辺を、元の頂点同型の類と可逆性へ照合する。
方針：元の coslice 射影のホモトピー圏への関手性を使う。
規約：代表辺を変更せず、元の評価余錐と標準余錐の頂点を保持する。
使われ方：実際の有限錐像と標準全錐の比較辺の端点正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SSet.Truncated.HomotopyCategory
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)
  (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r)
  (hq : ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x) q))
  (x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌)

/-- 元の同じ代表の頂点辺の類は、元の同じ coslice 比較の頂点同型の順方向。 -/
lemma presheafEvaluationComparisonApexEdge_homMk :
    homMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationComparisonApexEdge r q hq x) =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeApexIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationCoconeIso r q hq x)).hom := by
  change homMk ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationCoconeIso r q hq x)).map
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x)))) =
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x))).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationCoconeIso r q hq x).hom
  rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative_homMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationCoconeIso r q hq x)]
  rfl

/-- 同じ元の評価 coslice 代表の頂点射影は可逆。 -/
lemma presheafEvaluationComparisonApexEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationComparisonApexEdge r q hq x) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeIsoRepresentative_isInvertible (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationCoconeIso r q hq x)).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x))

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
