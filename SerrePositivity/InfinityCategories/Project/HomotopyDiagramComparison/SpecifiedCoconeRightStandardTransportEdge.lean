module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PrismPointEdges
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRestrictionEdges

/-!
概要：指定右修正三角形の初辺を、標準輸送 prism 自身の辺として保持する。
方針：同じ標準 prism を、元の右余錐の fiber 頂点で評価する。
規約：裸の存在命題から辺を選び直さない。元の prism と底の右脚を同時に保つ。
使われ方：右修正辺と合成する前の標準輸送辺の厳密な照合。
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
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
local notation "qC" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (j ≫ p)
local notation "eC" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "vC" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt qC dC (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex dC) rfl

/-- 右修正を加える前の辺は、同じ標準 prism の点の辺そのもの。 -/
def specifiedCoconeRightStandardTransportEdge : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (j ≫ p)).Edge dC
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportedCoconeVertex dC eC).val := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardTransportPointEdge qC eC vC

/-- 第一辺の一単体は、標準 prism 自身から取った同じ一単体。 -/
lemma specifiedCoconeRightStandardTransportEdge_raw :
    (specifiedCoconeRightStandardTransportEdge hp p c hc dB dC).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardTransportPointEdge qC eC vC).edge := rfl

/-- 第一辺の全単体表示は、同じ標準 prism を元の fiber 頂点で評価したもの。 -/
lemma specifiedCoconeRightStandardTransportEdge_diagram :
    SSet.yonedaEquiv.symm (specifiedCoconeRightStandardTransportEdge hp p c hc dB dC).edge =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism qC eC) vC :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardTransportPointEdge_diagram qC eC vC

/-- 標準の右辺は、元の native span の右脚を一単体のまま被覆する。 -/
lemma specifiedCoconeRightStandardTransportEdge_projection :
    (qC).app (Opposite.op ⦋1⦌)
        (specifiedCoconeRightStandardTransportEdge hp p c hc dB dC).edge = (eC).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardTransportPointEdge_projection qC eC vC

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
