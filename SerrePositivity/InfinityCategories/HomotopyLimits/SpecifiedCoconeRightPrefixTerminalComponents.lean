module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightPrefixTerminalPoint
public import SerrePositivity.InfinityCategories.HomotopyLimits.MapTransportPrismComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeBoundaryTransportCylinder

/-!
概要：右初面三角形の全終端辺の輸送比較の二成分を、元の境界自然性と恒等射へ同定する。
方針：実際の二つの点 prism を回収し、同じ全族の同型の成分公式へ渡す。
規約：端点の表示変更は Arrow で明示する。使われ方：右初面終点比較の合成式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "qC" => sliceUnderProjection (j ≫ p)
local notation "e" => partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "z" => JoinCocone.vertex
  (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
local notation "H" => specifiedCoconeRightPrefixTerminalPrism hp p c hc dB dC
local notation "F" => specifiedCoconeRightPrefixMiddleEvaluation hp p c hc dB dC
local notation "G" => specifiedCoconeRightPrefixTerminalEvaluation hp p c hc dB dC
local notation "x" => specifiedCoconeRightPrefixActualTriangleExtensionVertex hp p c hc dB dC
local notation "y" => specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC
local notation "vC" => initialFiberVertexAt qC dC (JoinCocone.vertex dC) rfl
local notation "r" => normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p)
local notation "hr" => normalizedCoconeRestriction_projection (j ≫ p) g (coconePushoutBoundary_eq
  hp p)
local notation "he" => specifiedCoconeRightPrefixTerminalEdge_base hp p c hc dB dC

/-- 実際の三角形の点 prism は、同じ標準 prism の制限自然性に使う入力そのもの。 -/
lemma specifiedCoconeRightPrefixTerminalPrism_actual_map :
    prismParameterPrecomp H (SSet.yonedaEquiv.symm x) =
      prismParameterPrecomp (mapTransportPrism qC r e) (SSet.yonedaEquiv.symm vC) := by
  refine (specifiedCoconeRightPrefixTerminalPrism_actual_point hp p c hc dB dC).trans ?_
  refine Eq.trans ?_ (prismParameterPrecomp_point (mapTransportPrism qC r e) vC).symm
  simp only [mapTransportPrism, prismVertexEvaluation, Category.assoc]

/-- 実際の三角形成分は、元の指定境界路の制限自然性同型を点評価した射。 -/
abbrev specifiedCoconeRightPrefixTerminalTransport_actual_hom_arrow :=
  prismTransportComponent_map_pointIso_hom_arrow qC q r hr e F G H
    (fixedExtensionEdgeSource_ι _ _ _ _ _ _ _ he).symm
    (fixedExtensionEdgeTarget_ι _ _ _ _ _ _ _ he).symm
    (fixedExtensionEdgePrism_projection _ _ _ _ _ _ _ he)
    x vC (specifiedCoconeRightPrefixTerminalPrism_actual_map hp p c hc dB dC)
    (coconeBoundaryTransportPointIso g (j ≫ p) (coconePushoutBoundary_eq hp p) dC e)
    (coconeBoundaryTransportPointIso_hom_arrow g (j ≫ p) (coconePushoutBoundary_eq hp p) dC e)

local notation "v₀" => initialFiberVertexAt q c (JoinCocone.vertex c) rfl
local notation "e₀" => SSet.Edge.ofTruncated (colimitAttachmentApexEdge c hc g (j ≫ p)
  (coconePushoutBoundary_eq hp p) dC)
local notation "v₁" => NatTrans.app (edgeTransport q e₀) (Opposite.op ⦋0⦌) v₀

/-- 標準三角形の点 prism は、同じ第一輸送後の点を始点とする標準 prism。 -/
lemma specifiedCoconeRightPrefixTerminalPrism_standard_map :
    prismParameterPrecomp H (SSet.yonedaEquiv.symm y) =
      prismTransportStandard q e (SSet.yonedaEquiv.symm v₁) := by
  exact (specifiedCoconeRightPrefixTerminalPrism_standard_point hp p c hc dB dC).trans
    (prismParameterPrecomp_point (transportEdgePrism q e) v₁).symm

/-- 標準側の成分公式。同じ標準 prism の定値比較円柱から恒等射を得る。 -/
abbrev specifiedCoconeRightPrefixTerminalTransport_standard_hom_arrow :=
  prismTransportComponent_standard_hom_arrow q e F G H
    (fixedExtensionEdgeSource_ι _ _ _ _ _ _ _ he).symm
    (fixedExtensionEdgeTarget_ι _ _ _ _ _ _ _ he).symm
    (fixedExtensionEdgePrism_projection _ _ _ _ _ _ _ he)
    y (SSet.yonedaEquiv.symm v₁)
    (specifiedCoconeRightPrefixTerminalPrism_standard_map hp p c hc dB dC)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
