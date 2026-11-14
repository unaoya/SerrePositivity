module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeLeftTerminalPoint
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.MapTransportPrismComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeBoundaryTransportCylinder

/-!
概要：左三角形の全終端辺の輸送比較の二成分を、元の境界自然性と恒等射へ同定する。
方針：実際の二つの点 prism を回収し、同じ全族の同型の成分公式へ渡す。
規約：端点の表示変更は Arrow で明示する。使われ方：左終点比較の合成式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "qB" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (i ≫ p)
local notation "e" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "z" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)
local notation "H" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTerminalPrism hp p c hc dB dC
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftMiddleEvaluation hp p c hc dB dC
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTerminalEvaluation hp p c hc dB dC
local notation "x" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftActualTriangleExtensionVertex hp p c hc dB dC
local notation "y" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftStandardTriangleExtensionVertex hp p c hc dB dC
local notation "vB" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt qB dB (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex dB) rfl
local notation "r" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (i ≫ p) f rfl
local notation "hr" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection (i ≫ p) f rfl
local notation "he" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTerminalEdge_base hp p c hc dB dC

/-- 実際の三角形の点 prism は、同じ標準 prism の制限自然性に使う入力そのもの。 -/
lemma specifiedCoconeLeftTerminalPrism_actual_map :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp H (SSet.yonedaEquiv.symm x) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism qB r e) (SSet.yonedaEquiv.symm vB) := by
  refine (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTerminalPrism_actual_point hp p c hc dB dC).trans ?_
  refine Eq.trans ?_ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp_point (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism qB r e) vB).symm
  simp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction,
    eqToHom_refl, Category.comp_id, Category.assoc]

/-- 実際の三角形成分は、元の指定境界路の制限自然性同型を点評価した射。 -/
abbrev specifiedCoconeLeftTerminalTransport_actual_hom_arrow :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportComponent_map_pointIso_hom_arrow qB q r hr e F G H
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeSource_ι _ _ _ _ _ _ _ he).symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget_ι _ _ _ _ _ _ _ he).symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgePrism_projection _ _ _ _ _ _ _ he)
    x vB (specifiedCoconeLeftTerminalPrism_actual_map hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeBoundaryTransportPointIso f (i ≫ p) rfl dB e)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeBoundaryTransportPointIso_hom_arrow f (i ≫ p) rfl dB e)

local notation "v₀" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt q c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex c) rfl
local notation "e₀" => SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc f (i ≫ p) rfl dB)
local notation "v₁" => NatTrans.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q e₀) (Opposite.op ⦋0⦌) v₀

/-- 標準三角形の点 prism は、同じ第一輸送後の点を始点とする標準 prism。 -/
lemma specifiedCoconeLeftTerminalPrism_standard_map :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp H (SSet.yonedaEquiv.symm y) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard q e (SSet.yonedaEquiv.symm v₁) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTerminalPrism_standard_point hp p c hc dB dC).trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp_point (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism q e) v₁).symm

/-- 標準側の成分公式。同じ標準 prism の定値比較円柱から恒等射を得る。 -/
abbrev specifiedCoconeLeftTerminalTransport_standard_hom_arrow :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportComponent_standard_hom_arrow q e F G H
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeSource_ι _ _ _ _ _ _ _ he).symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget_ι _ _ _ _ _ _ _ he).symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgePrism_projection _ _ _ _ _ _ _ he)
    y (SSet.yonedaEquiv.symm v₁)
    (specifiedCoconeLeftTerminalPrism_standard_map hp p c hc dB dC)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
