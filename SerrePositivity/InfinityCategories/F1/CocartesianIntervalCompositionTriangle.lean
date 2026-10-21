module

public import SerrePositivity.InfinityCategories.F1.CocartesianIntervalHomSquareFaces
public import SerrePositivity.InfinityCategories.F1.CompositionTriangleFaces

/-!
概要：分類先の実際の固定成分 fiber から、同じ二辺の可縮な合成三角形空間へ写す。
方針：元の第一三角形の二面を計算し、その全パラメーターの族を curry する。
規約：取り出す三角形は元の正方形の制限そのもの。
使われ方：一次元の元の Hom 比較を、指定された合成三角形上の fiber に移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の始域の一次元図式の輸送射を、その同じ coherent な辺として読む。 -/
def cocartesianIntervalCompositionFirstEdge
    (F : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) :
    CatInfinity.{u}.Edge (coherentNerveVertex (cocartesianTransportDiagramValue F (ULift.up 0)))
      (coherentNerveVertex (cocartesianTransportDiagramValue F (ULift.up 1))) :=
  coherentNerveEdge (show cocartesianTransportDiagramValue F (ULift.up 0) ⟶
    cocartesianTransportDiagramValue F (ULift.up 1) from F.val.map strictIntervalIndexArrow)

/-- 元の始域図式の標準区間上の表示は、同じ輸送射の辺の Yoneda 表示。 -/
lemma cocartesianIntervalCompositionFirstEdge_map
    (F : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) :
    (localKanDiagramBaseIso 1).hom ≫
        qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor F) =
      SSet.yonedaEquiv.symm (cocartesianIntervalCompositionFirstEdge F).edge := by
  change (localKanDiagramBaseIso 1).hom ≫
      qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor F) =
    SSet.yonedaEquiv.symm (coherentNerveEdge
      ((cocartesianTransportDiagramValueFunctor F).map strictIntervalIndexArrow)).edge
  exact localQCatIntervalDiagram_edge (cocartesianTransportDiagramValueFunctor F)

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))
variable (v : (intervalMappingSpace (coherentNerveVertex (cocartesianTransportDiagramValue F c))
  (coherentNerveVertex (cocartesianTransportDiagramValue G c))) _⦋0⦌)
local notation "E" => (vertexFiber (cocartesianHomIntervalEvaluation F G c) v)

/-- 元の始域図式の辺と指定成分を、そのまま固定した合成三角形空間。 -/
def cocartesianIntervalCompositionSpace : SSet.{u + 1} :=
  compositionTriangleSpace (cocartesianIntervalCompositionFirstEdge F)
    (intervalMappingEdgeOfVertex v)

/-- 分類先の固定成分比較に使う、同じ合成三角形空間は可縮 Kan。 -/
lemma cocartesianIntervalCompositionSpace_isContractibleKan :
    IsContractibleKan (cocartesianIntervalCompositionSpace F G v) :=
  compositionTriangleSpace_isContractibleKan _ _

/-- 元の固定成分 fiber の族から、その同じ第一三角形を全パラメーターで取り出す。 -/
def cocartesianIntervalCompositionTriangleFamily {T : SSet.{u + 1}} (f : T ⟶ E) :
    T ⟶ cocartesianIntervalCompositionSpace F G v :=
  compositionTriangleFamilyCurry (cocartesianIntervalCompositionFirstEdge F)
    (intervalMappingEdgeOfVertex v) (cocartesianIntervalHomTriangle F G v 0 f)
    (by rw [cocartesianIntervalHomTriangle_first, cocartesianIntervalCompositionFirstEdge_map])
    (by rw [cocartesianIntervalHomTriangle_last, intervalMappingUncurry_const_vertex]; rfl)

/-- 同じ合成三角形空間の族を展開すると、元の正方形の第一三角形そのもの。 -/
lemma cocartesianIntervalCompositionTriangleFamily_uncurry {T : SSet.{u + 1}} (f : T ⟶ E) :
    innerTriangleExtensionUncurry (cocartesianIntervalCompositionTriangleFamily F G v f) =
      cocartesianIntervalHomTriangle F G v 0 f := by
  unfold cocartesianIntervalCompositionTriangleFamily compositionTriangleFamilyCurry
  exact innerTriangleExtensionUncurry_curry _ _ _

/-- 実際の固定成分 fiber から、同じ合成三角形の可縮な空間への元の制限写像。 -/
def cocartesianIntervalCompositionTriangleMap : E ⟶ cocartesianIntervalCompositionSpace F G v :=
  cocartesianIntervalCompositionTriangleFamily F G v (𝟙 E)

end SerrePositivity.InfinityCategories
