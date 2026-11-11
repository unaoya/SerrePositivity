module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaPresheafFamilyComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentInvertibleTotalKan

/-!
概要：元の P_Σ 評価錐の頂点と反復積関手の同型を、元の余極限 Kan 模型へ移す。
方針：既に構成した同じ頂点同型の可逆辺から、指定全空間作用とその Kan 像を取る。
規約：元の族・有限極限錐・余極限模型を保持し、底の quasicategory 性は要求しない。
使われ方：元の sifted 余極限の全積錐と元の評価全錐の像の比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)
  {J : Type u} [Finite J] [Nonempty J] {p : nerve (Discrete J) ⟶ C.op}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexEvaluation r (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift c))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFiniteEvaluationFamily r (p := p))

/-- 元の評価錐と積錐の頂点比較の、同じ可逆な coherent 変換。 -/
def sigmaPresheafApexComparisonTransformation :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace A P) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFiniteProductApexIso r c hc))

/-- 元の頂点比較の変換辺は可逆。 -/
lemma sigmaPresheafApexComparisonTransformation_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (sigmaPresheafApexComparisonTransformation r c hc)) := by
  rw [sigmaPresheafApexComparisonTransformation,
    show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFiniteProductApexIso r c hc))) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFiniteProductApexIso r c hc) from
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_isInvertible _

/-- 元の二つの頂点関手の余極限 Kan 模型を結ぶ、元の指定全空間作用の Kan 像。 -/
def sigmaPresheafApexTotalKanComparison :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan A ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan P :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTotalKanMap A P (sigmaPresheafApexComparisonTransformation r c hc)

/-- 同じ元の余極限 Kan 比較は、任意の底上で単体的ホモトピー同値。 -/
lemma sigmaPresheafApexTotalKanComparison_homotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (sigmaPresheafApexTotalKanComparison r c hc) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentInvertibleTotalKanMap_homotopyEquivalence A P _
    (sigmaPresheafApexComparisonTransformation_isInvertible r c hc)

/-- 同じ元の Kan 比較の余極限頂点間の native 辺は可逆。 -/
lemma sigmaPresheafApexTotalNativeEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeEdge A P (sigmaPresheafApexTotalKanComparison r c hc)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentInvertibleTotalKanNativeEdge_isInvertible A P _
    (sigmaPresheafApexComparisonTransformation_isInvertible r c hc)

/-- 元の比較辺の全余錐作用は、元の指定 Kan 比較と単位の表現の余錐に同型。 -/
def sigmaPresheafApexTotalNativeCoconeIso :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeCoconeIso A P (sigmaPresheafApexTotalKanComparison r c hc)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
