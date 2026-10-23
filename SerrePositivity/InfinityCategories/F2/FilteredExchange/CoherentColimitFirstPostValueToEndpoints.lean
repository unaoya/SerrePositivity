module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawUnitActionComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitConstantTriangleValueToEndpoint

/-!
概要：五因子式の最初辺後合成の二実端点を、同じ raw 二面比較の実後合成へ揃える。
方針：元の単位と三実作用の終点を全射から計算し、同じ指定値を等式で移す。
規約：HEq から端点を抽出しない。使われ方：元の最初因子を一点比較の交換式へ代入する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (a : SSet.Homotopy F G) (b : SSet.Homotopy G J)
local notation "p" => leftUnstraighteningProjection F
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "uF" => coconeTransformationHomotopy (coherentDiagramTotalCocone F)
local notation "uG" => coconeTransformationHomotopy (coherentDiagramTotalCocone G)
local notation "ca" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a)
local notation "cb" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b)
local notation "Q" => constantTargetValueProjectionTo p (coherentDiagramTotalCocone_vertex J)
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "f" => leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)
local notation "g₀" => Subtype.val (leftUnstraighteningMappingVertexMap
  (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone G)))
  (SSet.const (JoinCocone.vertex (coherentDiagramTotalCocone J)))
  (coherentVertexOfHomotopy cb)) ≫ constantUnstraighteningFiberProjection
    (CategoryTheory.Functor.obj SSet.uliftFunctor B)
    (JoinCocone.vertex (coherentDiagramTotalCocone J)) ≫ V

/-- 元の最初因子の実始点は、元の raw 下面作用と同じ定値最後辺の実後合成の頂点。 -/
lemma coherentColimitFirstPost_valueTo_source_vertex :
    NatTrans.app Q (Opposite.op ⦋0⦌)
      ((functorHomotopyRelativePost cb p).app (Opposite.op ⦋0⦌)
        ((functorHomotopyRelativePost ca p).app (Opposite.op ⦋0⦌)
          ((functorHomotopyRelativePost uF p).app (Opposite.op ⦋0⦌) x₀))) =
      functorVertex (coherentColimitRawLowerCompositeAction B a ≫ g₀) := by
  simpa only [coherentColimitRawLowerCompositeAction, coherentVertexOfHomotopy_cocone,
    Category.assoc] using
    (coherentColimitConstantTriangleValueTo_target_vertex B (a := a) (b := b))

/-- 元の最初因子の実終点は、元の raw 上面作用と同じ定値最後辺の実後合成の頂点。 -/
lemma coherentColimitFirstPost_valueTo_target_vertex :
    NatTrans.app Q (Opposite.op ⦋0⦌)
      ((functorHomotopyRelativePost cb p).app (Opposite.op ⦋0⦌)
        ((functorHomotopyRelativePost uG p).app (Opposite.op ⦋0⦌)
          ((functorHomotopyRelativePost a p).app (Opposite.op ⦋0⦌) x₀))) =
      functorVertex (coherentColimitRawUpperCompositeAction B a ≫ g₀) := by
  have hx : (functorHomotopyRelativePost a p).app (Opposite.op ⦋0⦌) x₀ =
      relativeFunctorVertex (leftUnstraighteningProjection G) p
        (Subtype.val f) (Subtype.property f) := by
    apply Subtype.ext
    rfl
  rw [constantTargetValueProjectionTo_eq_fiberValueTo, hx]
  have h := functorSequentialPost_fiberMap_vertex uG cb p (Subtype.val f) (Subtype.property f) V
  simpa only [coherentColimitRawUpperCompositeAction, Category.assoc] using h

/-- 実両端だけを揃えた元の最初因子は、同じ raw 二面比較の元の実後合成に等しい。 -/
lemma coherentColimitFirstPost_valueTo_eq_raw :
    vertexIsoOfEq
      (VertexIso.map (VertexIso.map (coherentColimitUnitValueComparison B a p x₀)
        (functorHomotopyRelativePost cb p)) Q)
      (coherentColimitFirstPost_valueTo_source_vertex B a b)
      (coherentColimitFirstPost_valueTo_target_vertex B a b) =
    (coherentColimitRawUnitActionComparison B a).postcomp g₀ := by
  exact eq_of_heq ((vertexIsoOfEq_heq _ _ _).trans
    (coherentColimitFirstEdgePost_valueTo_heq_raw B a b))

end SerrePositivity.InfinityCategories.F2
