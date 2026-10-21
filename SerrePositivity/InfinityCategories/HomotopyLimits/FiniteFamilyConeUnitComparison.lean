module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteFamilyConeLegTriangles
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTriangleFromFunctorSimplex
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentProjectionUnitComparison

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}} {J : Type u} [Finite J] [Nonempty J]
  (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
  (c : JoinCone (finiteFamilyFunctorDiagram G)) (hc : IsLimitCone c)
  (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (hA : c.vertex = functorVertex A)

/-- 元の同じ slice 比較の頂点辺を coherent 変換の指定頂点にする。 -/
def finiteFamilyConeApexTransformation :=
  intervalMappingVertexOfEdge (finiteFamilyConeComparisonApexEdge G c hc A hA)

/-- 全脚と共有する同じ元の頂点比較変換は可逆。 -/
lemma finiteFamilyConeApexTransformation_isInvertible :
    IsInvertibleEdge (intervalMappingEdgeOfVertex
      (finiteFamilyConeApexTransformation G c hc A hA)) := by
  rw [finiteFamilyConeApexTransformation,
    show intervalMappingEdgeOfVertex (intervalMappingVertexOfEdge
      (finiteFamilyConeComparisonApexEdge G c hc A hA)) =
        finiteFamilyConeComparisonApexEdge G c hc A hA from
      (intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _]
  exact finiteFamilyConeComparisonApexEdge_isInvertible G c hc A hA

/-- 元の評価全錐の実際の脚を、その全一単体のまま coherent 変換にする。 -/
def finiteFamilyOriginalLegTransformation (j : J) :=
  intervalMappingVertexOfEdge (finiteFamilyOriginalConeLeg G c A hA j)

/-- 元の積全錐の実際の脚を、その全一単体のまま coherent 変換にする。 -/
def finiteFamilyProductLegTransformation (j : J) :=
  intervalMappingVertexOfEdge (finiteFamilyProductConeLeg G j)

/-- 元の同じ頂点比較・積脚・評価脚からなる、長辺も元のままの全変換三角形。 -/
def finiteFamilyConeLegTransformationTriangle (j : J) :
    F2.CoherentTransformationVertexTriangle A (finiteFamilyCoherentProduct G) (G j)
      (finiteFamilyConeApexTransformation G c hc A hA)
      (finiteFamilyProductLegTransformation G j) :=
  coherentTransformationTriangleOfFunctorSimplex
    (finiteFamilyConeComparisonLegTriangle G c hc A hA j)

/-- 元の全変換三角形の長辺は、元の評価全錐の同じ実際の脚。 -/
lemma finiteFamilyConeLegTransformationTriangle_diagonal (j : J) :
    (finiteFamilyConeLegTransformationTriangle G c hc A hA j).diagonal =
      finiteFamilyOriginalLegTransformation G c A hA j := rfl

/-- 元の実際の評価脚の全空間作用は、指定単位の後で元の頂点比較・積脚と同型。 -/
def finiteFamilyOriginalLegUnitIso (j : J) :
    FunctorIso (F2.coherentTransformationTotalMap A (G j)
      (finiteFamilyOriginalLegTransformation G c A hA j) ≫ F2.coherentDiagramTotalUnit (G j))
      (F2.coherentTransformationTotalMap A (finiteFamilyCoherentProduct G)
        (finiteFamilyConeApexTransformation G c hc A hA) ≫
      F2.coherentTransformationTotalMap (finiteFamilyCoherentProduct G) (G j)
        (finiteFamilyProductLegTransformation G j) ≫ F2.coherentDiagramTotalUnit (G j)) :=
  coherentTransformationTriangleUnitIso A (finiteFamilyCoherentProduct G) (G j) _ _
    (finiteFamilyConeLegTransformationTriangle G c hc A hA j)

end SerrePositivity.InfinityCategories.HomotopyLimits
