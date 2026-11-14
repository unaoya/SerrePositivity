module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.StandardCoconeKanLeg
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.Presheaves.PresheafStandardUnitSquare

/-!
概要：実際の前層余極限の元の頂点脚を同じ比較で共役し、元の全評価 Kan 脚へ同定する。
方針：同じ全余錐の頂点評価辺を保持し、両 coslice 比較の頂点同型を使う。
規約：指定余錐・全脚・比較代表を保持し、底の quasicategory 性は要求しない。
使われ方：実際の前層余極限の非空有限積保存の全脚比較。
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

/-- 元の全余錐脚の頂点評価は、実際の頂点関手による同じ脚の全一単体。 -/
lemma presheafCoconeImageLeg_apex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeApex q₀ q₁ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeImageLeg q c k).toTruncated).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeVertexFunctor q)
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift c)) k).edge :=
  congrArg (fun d => (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg d k).edge) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeImageCone_apex q c)

/-- 元の実際の頂点脚を同じ比較で標準評価余極限頂点間へ共役した辺。 -/
def presheafColimitLegConjugate :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardCoconeKanLegEdge (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x₀) (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x₁)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationCoconeIso r q hq x₀) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationCoconeIso r q hq x₁)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeImageLeg q c k).toTruncated

/-- 実際の同じ頂点脚の共役辺は、同じ元の評価脚の全空間 Kan 像と同じ Hom 類。 -/
lemma presheafColimitLegConjugate_homMk :
    homMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeEdge (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x₀) (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x₁)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTotalKanMap (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x₀) (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x₁)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeBottom q₀ q₁
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeImageLeg q c k).toTruncated)))).toTruncated =
      homMk (presheafColimitLegConjugate q hq c k).toTruncated :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardCoconeKanLeg_homMk (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x₀) (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x₁)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationCoconeIso r q hq x₀) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafEvaluationCoconeIso r q hq x₁)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafCoconeImageLeg q c k).toTruncated

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
