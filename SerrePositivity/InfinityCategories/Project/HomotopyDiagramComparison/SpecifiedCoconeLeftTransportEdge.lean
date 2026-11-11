module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PrismPointEdges
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRestrictionEdges

/-!
概要：指定した元の余錐の左制限へ、標準輸送 prism 自身から比較辺を取り出す。
方針：左制限の厳密な輸送像の式で、同じ標準 prism の点の辺の終点を表示し直す。
規約：裸の辺の存在命題から選ばない。元の prism と底の左脚を同時に保つ。
使われ方：元の native な左三角形に付加比較辺と左輸送辺を持ち上げる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
local notation "qB" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (i ≫ p)
local notation "eB" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "vB" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt qB dB (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex dB) rfl

/-- 左の標準 prism 自身の辺を、指定した元の余錐の左制限を終点として保持する。 -/
def specifiedCoconeLeftTransportEdge : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (i ≫ p)).Edge dB
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC).restrict i) := by
  let k := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardTransportPointEdge qB eB vB
  exact
    ⟨k.edge, k.src_eq, k.tgt_eq.trans
      ((congrArg Subtype.val (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedFiberVertex_left hp p c hc dB dC)).symm.trans
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRestrictionFiber_vertex_val i _
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedFiberVertex hp p c hc dB dC)))⟩

set_option maxHeartbeats 800000 in
-- 指定余錐の左制限と標準輸送像の大きい頂点表示を一単体の型で照合する。
/-- 終点の表示を変えても、一単体は元の標準輸送の点の辺そのもの。 -/
lemma specifiedCoconeLeftTransportEdge_raw :
    (specifiedCoconeLeftTransportEdge hp p c hc dB dC).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardTransportPointEdge qB eB vB).edge := rfl

/-- この辺の全単体表示は、元の標準輸送 prism の同じ点での評価そのもの。 -/
lemma specifiedCoconeLeftTransportEdge_diagram :
    SSet.yonedaEquiv.symm (specifiedCoconeLeftTransportEdge hp p c hc dB dC).edge =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism qB eB) vB :=
  (congrArg SSet.yonedaEquiv.symm
    (specifiedCoconeLeftTransportEdge_raw hp p c hc dB dC)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardTransportPointEdge_diagram qB eB vB)

/-- 左の実際の比較辺は、元の span の左脚を一単体のまま厳密に被覆する。 -/
lemma specifiedCoconeLeftTransportEdge_projection :
    (qB).app (Opposite.op ⦋1⦌) (specifiedCoconeLeftTransportEdge hp p c hc dB dC).edge =
      (eB).edge :=
  (congrArg (fun z ↦ (qB).app (Opposite.op ⦋1⦌) z)
    (specifiedCoconeLeftTransportEdge_raw hp p c hc dB dC)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardTransportPointEdge_projection qB eB vB)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
