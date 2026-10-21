module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaPresheafFamilyComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentInvertibleTotalKan

/-!
概要：元の P_Σ 評価錐の頂点と反復積関手の同型を、元の余極限 Kan 模型へ移す。
方針：既に構成した同じ頂点同型の可逆辺から、指定全空間作用とその Kan 像を取る。
規約：元の族・有限極限錐・余極限模型を保持し、底の quasicategory 性は要求しない。
使われ方：元の sifted 余極限の全積錐と元の評価全錐の像の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)
  {J : Type u} [Finite J] [Nonempty J] {p : nerve (Discrete J) ⟶ C.op}
  (c : JoinCone p) (hc : IsLimitCone c)
local notation "A" => sigmaPresheafVertexEvaluation r (JoinCone.vertex (JoinCone.ulift c))
local notation "P" => finiteFamilyCoherentProduct
  (sigmaPresheafFiniteEvaluationFamily r (p := p))

/-- 元の評価錐と積錐の頂点比較の、同じ可逆な coherent 変換。 -/
def sigmaPresheafApexComparisonTransformation :
    (leftUnstraighteningTransformationSpace A P) _⦋0⦌ :=
  intervalMappingVertexOfEdge (FunctorIso.edge (sigmaPresheafFiniteProductApexIso r c hc))

/-- 元の頂点比較の変換辺は可逆。 -/
lemma sigmaPresheafApexComparisonTransformation_isInvertible :
    IsInvertibleEdge
      (intervalMappingEdgeOfVertex (sigmaPresheafApexComparisonTransformation r c hc)) := by
  rw [sigmaPresheafApexComparisonTransformation,
    show intervalMappingEdgeOfVertex (intervalMappingVertexOfEdge
      (FunctorIso.edge (sigmaPresheafFiniteProductApexIso r c hc))) =
        FunctorIso.edge (sigmaPresheafFiniteProductApexIso r c hc) from
      (intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _]
  exact FunctorIso.edge_isInvertible _

/-- 元の二つの頂点関手の余極限 Kan 模型を結ぶ、元の指定全空間作用の Kan 像。 -/
def sigmaPresheafApexTotalKanComparison :
    F2.coherentDiagramTotalKan A ⟶ F2.coherentDiagramTotalKan P :=
  coherentTransformationTotalKanMap A P (sigmaPresheafApexComparisonTransformation r c hc)

/-- 同じ元の余極限 Kan 比較は、任意の底上で単体的ホモトピー同値。 -/
lemma sigmaPresheafApexTotalKanComparison_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (sigmaPresheafApexTotalKanComparison r c hc) :=
  coherentInvertibleTotalKanMap_homotopyEquivalence A P _
    (sigmaPresheafApexComparisonTransformation_isInvertible r c hc)

/-- 同じ元の Kan 比較の余極限頂点間の native 辺は可逆。 -/
lemma sigmaPresheafApexTotalNativeEdge_isInvertible :
    IsInvertibleEdge (totalKanNativeEdge A P (sigmaPresheafApexTotalKanComparison r c hc)) :=
  coherentInvertibleTotalKanNativeEdge_isInvertible A P _
    (sigmaPresheafApexComparisonTransformation_isInvertible r c hc)

/-- 元の比較辺の全余錐作用は、元の指定 Kan 比較と単位の表現の余錐に同型。 -/
def sigmaPresheafApexTotalNativeCoconeIso :=
  totalKanNativeCoconeIso A P (sigmaPresheafApexTotalKanComparison r c hc)

end SerrePositivity.InfinityCategories.HomotopyLimits
