module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightPrefixTerminalTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedExtensionEdgePoint

/-!
概要：右初面三角形の全終端辺の prism を、実際の三角形と標準三角形で計算する。
方針：同じ固定延長の頂点の点評価を、保持している二面の raw な式へつなぐ。
規約：二つの三角形も元の標準辺も選び直さない。使われ方：終点比較の二成分の同定。
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
local notation "σ" => partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "β" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex σ)
local notation "i₀" => stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3)
local notation "v" => SSet.yonedaEquiv.symm c
local notation "hv" => specifiedCoconeRightPrefixTriangleExtension_initial_base hp p c hc dB dC
local notation "L" => specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC
local notation "e" => partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "vC" => initialFiberVertexAt qC dC (JoinCocone.vertex dC) rfl
local notation "v₀" => initialFiberVertexAt q c (JoinCocone.vertex c) rfl
local notation "e₀" => SSet.Edge.ofTruncated
  (colimitAttachmentApexEdge c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
local notation "x" => specifiedCoconeRightPrefixActualTriangleExtensionVertex hp p c hc dB dC
local notation "y" => specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC

/-- 実際の右初面三角形での全終端辺の点評価は、同じ標準右初面辺を制限した prism。 -/
lemma specifiedCoconeRightPrefixTerminalPrism_actual_point :
    prismParameterPrecomp (specifiedCoconeRightPrefixTerminalPrism hp p c hc dB dC)
      (SSet.yonedaEquiv.symm x) =
      fst (Δ[1] : SSet.{u + 1}) (Δ[0] : SSet.{u + 1}) ≫
        prismVertexEvaluation (transportEdgePrism qC e) vC ≫ normalizedCoconeRestriction (j ≫ p) g
          (coconePushoutBoundary_eq hp p) := by
  have h := fixedExtensionEdgePrism_point q β i₀ v hv (stdSimplex.δ (0 : Fin 3)) L
    (specifiedCoconeRightPrefixRootedTriangle_projection hp p c hc dB dC)
    (specifiedCoconeRightPrefixTriangleExtension_initial hp p c hc dB dC)
  refine h.trans ?_
  exact congrArg (fun z ↦ fst (Δ[1] : SSet.{u + 1}) (Δ[0] : SSet.{u + 1}) ≫ z)
    ((specifiedCoconeRightPrefixRootedTriangle_second hp p c hc dB dC).trans
      (congrArg (fun z ↦ z ≫ normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p))
        (specifiedCoconeRightStandardTransportEdge_diagram hp p c hc dB dC)))

/-- 標準三角形での点評価は、同じ第一輸送の像を始点とする標準終端辺。 -/
lemma specifiedCoconeRightPrefixTerminalPrism_standard_point :
    prismParameterPrecomp (specifiedCoconeRightPrefixTerminalPrism hp p c hc dB dC)
      (SSet.yonedaEquiv.symm y) =
      fst (Δ[1] : SSet.{u + 1}) (Δ[0] : SSet.{u + 1}) ≫
        prismVertexEvaluation (transportEdgePrism q e)
          ((edgeTransport q e₀).app (Opposite.op ⦋0⦌) v₀) := by
  have h := fixedExtensionEdgePrism_point q β i₀ v hv (stdSimplex.δ (0 : Fin 3))
    (coherentTransportTriangleVertex q σ v₀)
    (coherentTransportTriangleVertex_projection q σ v₀)
    (specifiedCoconeRightPrefixStandardTriangleExtension_initial hp p c hc dB dC)
  refine h.trans ?_
  exact congrArg (fun z ↦ fst (Δ[1] : SSet.{u + 1}) (Δ[0] : SSet.{u + 1}) ≫ z)
    ((coherentTransportTriangleVertex_second q σ v₀).trans
      (standardTransportPointEdge_diagram q e _))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
