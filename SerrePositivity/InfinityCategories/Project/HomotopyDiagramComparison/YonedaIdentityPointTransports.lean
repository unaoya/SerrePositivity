module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationPointTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.TwistedArrowPointedEdgeProjections

/-!
概要：元の Yoneda 恒等点の二方向の輸送を、同じ実際の fiber 内で比較する。
方針：元の Tw の二辺の共通終点と、それぞれの標準輸送点を比較して合成する。
規約：元の二つの底辺と恒等点を保持し、別の点や辺の代表を選ばない。
使われ方：Yoneda の第一変数の評価自然性と、P_Σ 内の有限余積保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 二つの元の pointed 辺の共通終点を、同じ実際の fiber 内の点として保持する。 -/
def yonedaIdentityCommonFiberPoint {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowPointedEdgeVertex f))) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowPointedEdgeVertex f, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _).symm⟩

/-- 元の始点側の底辺を、元の Yoneda 恒等点の実際の fiber を始点として表示する。 -/
def yonedaIdentitySourceBaseEdge {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    SSet.Edge
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity
        (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))).app (Opposite.op ⦋0⦌)
          (ULift.up (SSet.opObjEquiv.symm
            (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowPointedEdgeVertex f)) := by
  let h := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowPointedSourceEdge f).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
  exact ⟨h.edge, h.src_eq.trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaPointedIdentity _).property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _)), h.tgt_eq⟩

/-- 元の終点側の底辺を、元の Yoneda 恒等点の実際の fiber を始点として表示する。 -/
def yonedaIdentityTargetBaseEdge {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    SSet.Edge
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity
        (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1))).app (Opposite.op ⦋0⦌)
          (ULift.up (SSet.opObjEquiv.symm
            (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowPointedEdgeVertex f)) := by
  let h := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowPointedTargetEdge f).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
  exact ⟨h.edge, h.src_eq.trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaPointedIdentity _).property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _)), h.tgt_eq⟩

/-- 元の共通終点は、始点側の同じ恒等点を元の底辺で標準輸送した点と同型。 -/
def yonedaIdentitySourceTransportIso {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (yonedaIdentityCommonFiberPoint f)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (yonedaIdentitySourceBaseEdge f)).app
        (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaPointedIdentity
          (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationEdge_pointVertexIso _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (yonedaIdentitySourceBaseEdge f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaPointedIdentity _) (yonedaIdentityCommonFiberPoint f)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowPointedSourceEdge f) rfl

/-- 元の共通終点は、終点側の同じ恒等点を元の反変辺で標準輸送した点と同型。 -/
def yonedaIdentityTargetTransportIso {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (yonedaIdentityCommonFiberPoint f)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (yonedaIdentityTargetBaseEdge f)).app
        (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaPointedIdentity
          (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationEdge_pointVertexIso _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (yonedaIdentityTargetBaseEdge f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaPointedIdentity _) (yonedaIdentityCommonFiberPoint f)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowPointedTargetEdge f) rfl

/-- 元の両恒等点の二方向の標準輸送点を、同じ実際の fiber 内で結ぶ。 -/
def yonedaIdentityPointTransportsIso {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (yonedaIdentitySourceBaseEdge f)).app
        (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaPointedIdentity
          (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (yonedaIdentityTargetBaseEdge f)).app
        (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaPointedIdentity
          (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)))) :=
  (yonedaIdentitySourceTransportIso f).symm ≪≫ yonedaIdentityTargetTransportIso f

/-- 始点側の標準輸送の底辺は、元の Yoneda の射を始点で評価した同じ一単体。 -/
lemma yonedaIdentitySourceBaseEdge_edge {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (yonedaIdentitySourceBaseEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up (SSet.opObjEquiv.symm
          (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))))).app
            (Opposite.op ⦋1⦌) (ULift.up (SSet.yonedaEquiv f)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowPointedSourceEdge_projection f

/-- 終点側の標準輸送の底辺は、元の表現可能前層の反転辺の同じ一単体。 -/
lemma yonedaIdentityTargetBaseEdge_edge {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (yonedaIdentityTargetBaseEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity
        (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1))).app (Opposite.op ⦋1⦌)
          (ULift.up (SSet.opObjEquiv.symm (SSet.yonedaEquiv f))) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedArrowPointedTargetEdge_projection f

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
