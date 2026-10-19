module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftTerminalPoint
public import SerrePositivity.InfinityCategories.HomotopyLimits.MapTransportPrismComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeBoundaryTransportCylinder

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "qB" => sliceUnderProjection (i ≫ p)
local notation "e" => partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "z" => JoinCocone.vertex
  (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
local notation "H" => specifiedCoconeLeftTerminalPrism hp p c hc dB dC
local notation "F" => specifiedCoconeLeftMiddleEvaluation hp p c hc dB dC
local notation "G" => specifiedCoconeLeftTerminalEvaluation hp p c hc dB dC
local notation "x" => specifiedCoconeLeftActualTriangleExtensionVertex hp p c hc dB dC
local notation "y" => specifiedCoconeLeftStandardTriangleExtensionVertex hp p c hc dB dC
local notation "vB" => initialFiberVertexAt qB dB (JoinCocone.vertex dB) rfl
local notation "r" => normalizedCoconeRestriction (i ≫ p) f rfl
local notation "hr" => normalizedCoconeRestriction_projection (i ≫ p) f rfl
local notation "he" => specifiedCoconeLeftTerminalEdge_base hp p c hc dB dC

/-- 実際の三角形の点 prism は、同じ標準 prism の制限自然性に使う入力そのもの。 -/
lemma specifiedCoconeLeftTerminalPrism_actual_map :
    prismParameterPrecomp H (SSet.yonedaEquiv.symm x) =
      prismParameterPrecomp (mapTransportPrism qB r e) (SSet.yonedaEquiv.symm vB) := by
  refine (specifiedCoconeLeftTerminalPrism_actual_point hp p c hc dB dC).trans ?_
  refine Eq.trans ?_ (prismParameterPrecomp_point (mapTransportPrism qB r e) vB).symm
  simp only [mapTransportPrism, prismVertexEvaluation, normalizedCoconeRestriction,
    eqToHom_refl, Category.comp_id, Category.assoc]

/-- 実際の三角形成分は、元の指定境界路の制限自然性同型を点評価した射。 -/
abbrev specifiedCoconeLeftTerminalTransport_actual_hom_arrow :=
  prismTransportComponent_map_pointIso_hom_arrow qB q r hr e F G H
    (fixedExtensionEdgeSource_ι _ _ _ _ _ _ _ he).symm
    (fixedExtensionEdgeTarget_ι _ _ _ _ _ _ _ he).symm
    (fixedExtensionEdgePrism_projection _ _ _ _ _ _ _ he)
    x vB (specifiedCoconeLeftTerminalPrism_actual_map hp p c hc dB dC)
    (coconeBoundaryTransportPointIso f (i ≫ p) rfl dB e)
    (coconeBoundaryTransportPointIso_hom_arrow f (i ≫ p) rfl dB e)

local notation "v₀" => initialFiberVertexAt q c (JoinCocone.vertex c) rfl
local notation "e₀" => SSet.Edge.ofTruncated (colimitAttachmentApexEdge c hc f (i ≫ p) rfl dB)
local notation "v₁" => NatTrans.app (edgeTransport q e₀) (Opposite.op ⦋0⦌) v₀

/-- 標準三角形の点 prism は、同じ第一輸送後の点を始点とする標準 prism。 -/
lemma specifiedCoconeLeftTerminalPrism_standard_map :
    prismParameterPrecomp H (SSet.yonedaEquiv.symm y) =
      prismTransportStandard q e (SSet.yonedaEquiv.symm v₁) := by
  exact (specifiedCoconeLeftTerminalPrism_standard_point hp p c hc dB dC).trans
    (prismParameterPrecomp_point (transportEdgePrism q e) v₁).symm

/-- 標準側の成分公式。同じ標準 prism の定値比較円柱から恒等射を得る。 -/
abbrev specifiedCoconeLeftTerminalTransport_standard_hom_arrow :=
  prismTransportComponent_standard_hom_arrow q e F G H
    (fixedExtensionEdgeSource_ι _ _ _ _ _ _ _ he).symm
    (fixedExtensionEdgeTarget_ι _ _ _ _ _ _ _ he).symm
    (fixedExtensionEdgePrism_projection _ _ _ _ _ _ _ he)
    y (SSet.yonedaEquiv.symm v₁)
    (specifiedCoconeLeftTerminalPrism_standard_map hp p c hc dB dC)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
