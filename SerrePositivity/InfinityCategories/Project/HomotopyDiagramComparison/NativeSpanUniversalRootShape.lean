module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NativeSpanUniversalHomDiagrams
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RootedHomRootCoordinates

/-!
概要：native span の左二単体と右退化四面体の根辺を、同じ join の脚へ同定する。
方針：辺の始点の join 面と元の右退化の辺03の式を使う。
規約：元の形状の厳密な一致。使われ方：同じ普遍全余錐族の根辺制限の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 合成二単体の根辺は、元の辺の始点と余錐頂点を join した同じ脚である。 -/
lemma coconeLegTriangleShape_root {K : SSet.{u}} {a b : K _⦋0⦌} (e : K.Edge a b) :
    stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape e =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 Δ[0]) := by
  have h : stdSimplex.δ (1 : Fin 3) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 1 0).inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 Δ[0]) := by
    simpa using _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinEdgePoint_face_inv.{u} (1 : Fin 2)
  change stdSimplex.δ (1 : Fin 3) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm e.edge) (𝟙 Δ[0])) = _
  rw [← Category.assoc, h, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp,
    e.δ_one_yonedaEquiv_symm]

/-- 左二単体の長辺と右退化四面体の辺03は、同じ形状の脚である。 -/
lemma nativeSpanUniversalRootShape_eq :
    stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanLeftTriangleShape.{u} =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanRightTetrahedronShape := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeSpanRightTetrahedronShape, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge_degeneracy]
  exact (coconeLegTriangleShape_root
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeShapeEdge (AsSmall.up.map WalkingSpan.Hom.fst))).trans
      (coconeLegTriangleShape_root
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeShapeEdge (AsSmall.up.map WalkingSpan.Hom.snd))).symm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
