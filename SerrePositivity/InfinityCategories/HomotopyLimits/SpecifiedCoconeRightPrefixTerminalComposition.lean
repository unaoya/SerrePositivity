module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightPrefixMiddleComparison
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightPrefixTerminalComponents
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointTransportNaturalityComposition

/-!
概要：右初面三角形の同じ比較辺の終点の類を、境界自然性と付加辺輸送の合成として計算する。
方針：全終端辺の輸送自然性に、二成分と中間評価の三つの既存の同定を代入する。
規約：元の比較辺と指定境界経路の同型を保持する。使われ方：共通長辺空間の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

-- 同じ頂点と脚の照合では、選択した余極限候補の内部の構成を展開しない。
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "e" => partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "z" => JoinCocone.vertex
  (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
local notation "F" => specifiedCoconeRightPrefixMiddleEvaluation hp p c hc dB dC
local notation "G" => specifiedCoconeRightPrefixTerminalEvaluation hp p c hc dB dC
local notation "s" => specifiedCoconeRightPrefixTriangleComparisonExtensionEdge hp p c hc dB dC

/-- 同じ実際の比較辺の終点の像は、元の境界自然性と付加辺輸送の合成の点評価である。 -/
abbrev specifiedCoconeRightPrefixTerminalComparison_hom_arrow :=
  functorIso_naturality_pointComposition
    (show _ ⟶ vertexFiber q dC.vertex from F)
    (show _ ⟶ vertexFiber q z from G) (edgeTransport q e)
    (specifiedCoconeRightPrefixTerminalTransportIso hp p c hc dB dC)
    (x := specifiedCoconeRightPrefixActualTriangleExtensionVertex hp p c hc dB dC)
    (y := specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC) s
    (f₀ := SSet.yonedaEquiv.symm (colimitAttachmentFiberVertex g (j ≫ p) (coconePushoutBoundary_eq
      hp p) dC))
    (f₁ := SSet.yonedaEquiv.symm (initialFiberVertexAt q c c.vertex rfl) ≫
      edgeTransport q (colimitAttachmentApexEdge c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
    (colimitAttachmentTransportPointIso c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
    (g₀ := SSet.yonedaEquiv.symm (transportedCoconeVertex dC e) ≫
      normalizedCoconeRestrictionFiber (j ≫ p) g (coconePushoutBoundary_eq hp p) z)
    (coconeBoundaryTransportPointIso g (j ≫ p) (coconePushoutBoundary_eq hp p) dC e)
    (specifiedCoconeRightPrefixMiddleComparison_hom_arrow hp p c hc dB dC)
    (specifiedCoconeRightPrefixTerminalTransport_actual_hom_arrow hp p c hc dB dC) _
    (specifiedCoconeRightPrefixTerminalTransport_standard_hom_arrow hp p c hc dB dC)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
