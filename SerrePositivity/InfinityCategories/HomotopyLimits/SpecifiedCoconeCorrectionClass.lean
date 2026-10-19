module

public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyPathPointEvaluation
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightCorrectionEndpoint

/-!
概要：同じ修正円柱の終点の類を、元の指定境界同型の一点評価へ接続する。
方針：元の境界 path の一単体との厳密な一致を、同じ円柱の類の評価へ移す。
規約：修正辺の選び直しはしない。使われ方：共通根辺での四因子の相殺。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "z" => JoinCocone.vertex
  (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
local notation "s" => specifiedCoconeRightCorrectionExtensionEdge hp p c hc dB dC
local notation "F" => specifiedCoconeRightRootEndpoint hp p c hc dB dC
local notation "I" => partialColimitSpanBoundaryIso c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC

/-- 同じ指定修正辺の終点の類は、元の境界同型の同じ一点評価である。 -/
lemma specifiedCoconeCorrectionEndpoint_boundary_hom_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk ((s).map F).toTruncated) =
      Arrow.mk (VertexIso.map I (pointFunctorEvaluationIso (vertexFiber q z)).hom).hom := by
  apply homotopyEquivalencePath_point_hom_arrow (I).simplicialHomotopy I
    (kanFunctorIso_simplicialHomotopy_hom I) ((s).map F)
  exact specifiedCoconeRightCorrectionExtensionEdge_boundary_edge hp p c hc dB dC

/-- 根辺の正準比較も、元の指定境界同型の同じ一点評価を保つ。 -/
abbrev specifiedCoconeCorrectionCanonical_boundary_hom_arrow :=
  contractibleEdgeEvaluation_hom_arrow
    (specifiedCoconeRightRootExtensionSpace_isContractibleKan hp p c hc dB dC) F s
    (VertexIso.map I (pointFunctorEvaluationIso (vertexFiber q z)).hom).hom
    (specifiedCoconeCorrectionEndpoint_boundary_hom_arrow hp p c hc dB dC)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
