module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiniteFamilyConeLegTriangles
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentTriangleFromFunctorSimplex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentProjectionUnitComparison

/-!
概要：元の有限全錐の実際の各脚を、元の積脚と頂点比較の全空間作用へ照合する。
方針：同じ slice 比較の元の合成二単体を全変換三角形にし、指定単位の後で比較する。
規約：全脚・長辺・指定単位を保持。底の quasicategory 性は不要。
使われ方：P_Σ の元の全評価脚の余極限写像を、同じ反復積錐の全脚へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {B : SSet.{u}} {J : Type u} [Finite J] [Nonempty J]
  (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram G)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
  (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (hA : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex A)

/-- 元の同じ slice 比較の頂点辺を coherent 変換の指定頂点にする。 -/
def finiteFamilyConeApexTransformation :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyConeComparisonApexEdge G c hc A hA)

/-- 全脚と共有する同じ元の頂点比較変換は可逆。 -/
lemma finiteFamilyConeApexTransformation_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex
      (finiteFamilyConeApexTransformation G c hc A hA)) := by
  rw [finiteFamilyConeApexTransformation,
    show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyConeComparisonApexEdge G c hc A hA)) =
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyConeComparisonApexEdge G c hc A hA from
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyConeComparisonApexEdge_isInvertible G c hc A hA

/-- 元の評価全錐の実際の脚を、その全一単体のまま coherent 変換にする。 -/
def finiteFamilyOriginalLegTransformation (j : J) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalConeLeg G c A hA j)

/-- 元の積全錐の実際の脚を、その全一単体のまま coherent 変換にする。 -/
def finiteFamilyProductLegTransformation (j : J) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyProductConeLeg G j)

/-- 元の同じ頂点比較・積脚・評価脚からなる、長辺も元のままの全変換三角形。 -/
def finiteFamilyConeLegTransformationTriangle (j : J) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationVertexTriangle A (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G) (G j)
      (finiteFamilyConeApexTransformation G c hc A hA)
      (finiteFamilyProductLegTransformation G j) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTriangleOfFunctorSimplex
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyConeComparisonLegTriangle G c hc A hA j)

/-- 元の全変換三角形の長辺は、元の評価全錐の同じ実際の脚。 -/
lemma finiteFamilyConeLegTransformationTriangle_diagonal (j : J) :
    (finiteFamilyConeLegTransformationTriangle G c hc A hA j).diagonal =
      finiteFamilyOriginalLegTransformation G c A hA j := rfl

/-- 元の実際の評価脚の全空間作用は、指定単位の後で元の頂点比較・積脚と同型。 -/
def finiteFamilyOriginalLegUnitIso (j : J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap A (G j)
      (finiteFamilyOriginalLegTransformation G c A hA j) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalUnit (G j))
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap A (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G)
        (finiteFamilyConeApexTransformation G c hc A hA) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G) (G j)
        (finiteFamilyProductLegTransformation G j) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalUnit (G j)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTriangleUnitIso A (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G) (G j) _ _
    (finiteFamilyConeLegTransformationTriangle G c hc A hA j)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
