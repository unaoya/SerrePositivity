module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationInitialSpan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceFiberVertices

/-!
概要：始点を固定した実際の辺を、left fibration の fiber と Hom の比較 span の点へ移す。
方針：辺を二点の join の coslice 単体とし、終点の基底での像を固定する。
規約：射影の充填性・始対象性は点の構成と評価には不要。
使われ方：部分余極限の比較辺と、固定終点余錐空間の Hom 表示の代表元の照合。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {E B : SSet.{u}} (p : E ⟶ B) {c d : E _⦋0⦌} (e : E.Edge c d)

/-- 全空間の辺の終点を、その基底の像上の fiber の点として表示する。 -/
def initialFiberEdgeEndpoint :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (p.app (Opposite.op ⦋0⦌) d)) _⦋0⦌ :=
  ⟨d, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _).symm⟩

/-- 実際の辺は、始点固定の比較 span の中間空間の零単体を与える。 -/
def initialFiberEdgeTotalVertex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialTotal p c (p.app (Opposite.op ⦋0⦌) d)) _⦋0⦌ := by
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeToCosliceFiberVertex e
  refine ⟨s.val, ?_⟩
  change p.app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c)).app (Opposite.op ⦋0⦌) s.val) = _
  rw [s.property, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]

/-- 中間空間の点を fiber 側へ評価すると、元の辺の終点そのものになる。 -/
lemma initialFiberEdgeTotalVertex_evaluation :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialEvaluation p c (p.app (Opposite.op ⦋0⦌) d)).app
        (Opposite.op ⦋0⦌) (initialFiberEdgeTotalVertex p e) = initialFiberEdgeEndpoint p := by
  apply Subtype.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeToCosliceFiberVertex e).property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero d)

/-- 比較 span の基底側の零単体を、標準の始点を持つ coslice fiber の点として表示する。 -/
def initialFiberEdgeBaseVertex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
      (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) c)))
        (p.app (Opposite.op ⦋0⦌) d)) _⦋0⦌ :=
  (eqToHom (congrArg (fun q ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q)
      (p.app (Opposite.op ⦋0⦌) d)) (SSet.yonedaEquiv_symm_comp c p))).app
    (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialProjection p c (p.app (Opposite.op ⦋0⦌) d)).app
        (Opposite.op ⦋0⦌) (initialFiberEdgeTotalVertex p e))

/-- 基底側の点が表す辺は、元の全空間の辺の射影と厳密に一致する。 -/
lemma initialFiberEdgeBaseVertex_edge :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberVertexToEdge (initialFiberEdgeBaseVertex p e) = e.map p := by
  have ht {f g : (Δ[0] : SSet.{u}) ⟶ B} (h : f = g) (y : B _⦋0⦌)
      (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection f) y) _⦋0⦌) :
      (((eqToHom (congrArg (fun q ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q) y) h)).app
        (Opposite.op ⦋0⦌) s).val.val) = s.val.val := by
    cases h
    rfl
  apply SSet.Edge.ext
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    (initialFiberEdgeBaseVertex p e).val.val) = _
  rw [initialFiberEdgeBaseVertex, ht (SSet.yonedaEquiv_symm_comp c p)]
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm e.edge) ≫ p)) =
      p.app (Opposite.op ⦋1⦌) e.edge
  rw [Category.assoc, Iso.inv_hom_id_assoc, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
