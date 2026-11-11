module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeStandardTriangles
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PresheafCoconeLegRestrictions
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PresheafEvaluationUnitComparison

/-!
概要：実際の前層余極限の元の各脚を、両端の標準余極限単位の正方形へ移す。
方針：同じ評価余錐の一意比較の代表を使い、一般の共役正方形を適用する。
規約：元の脚・両端の標準余錐・各点の比較を保持し、自然な比較族を仮定しない。
使われ方：実際の前層余極限頂点関手の非空有限積保存。
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
variable {B C K : SSet.{u}}
  {r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C}
  (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r)
  (hq : ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x) q))
  {p : K ⟶ C.op} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
  (k : ((SSet.uliftFunctor.{u + 1, u}).obj K) _⦋0⦌)
local notation "x₀" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift c)
local notation "x₁" => NatTrans.app (CategoryTheory.Functor.map SSet.uliftFunctor p)
  (Opposite.op ⦋0⦌) k
local notation "q₀" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x₀) q
local notation "q₁" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x₁) q

/-- 実際の同じ頂点脚を、両評価余錐の同じ代表で標準余極限頂点間へ移した射。 -/
def presheafCoconeStandardApexHom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeStandardApexHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationCoconeIso r q hq x₀)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationCoconeIso r q hq x₁) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeImageLeg q c k).toTruncated

/-- 実際の元の評価脚と標準単位は、同じ比較で移した実際の頂点脚について可換。 -/
lemma presheafCoconeStandardUnit_square :
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeBottom q₀ q₁ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeImageLeg q c k).toTruncated).toTruncated ≫
      homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x₁)))).toTruncated =
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x₀)))).toTruncated ≫
        presheafCoconeStandardApexHom q hq c k :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeStandardUnit_square (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationCoconeIso r q hq x₀)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationCoconeIso r q hq x₁) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeImageLeg q c k).toTruncated

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
