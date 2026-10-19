module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeCommonRootRestriction
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.FixedExtensionEdgeEvaluationNaturality
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightCorrectionEndpoint
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftTerminalComposition
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightPrefixTerminalComposition

/-!
概要：共通長辺へ移した左右の比較を、元の三角形と同じ終点で評価する。
方針：底の移送・長辺制限・終端辺の終点の厳密な一致を合成する。
規約：実際の比較辺の一単体を保持する。使われ方：元の境界自然性の共通空間への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
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
local notation "β" => specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "v" => SSet.yonedaEquiv.symm c
local notation "k" => stdSimplex.δ (1 : Fin 3)
local notation "a" => stdSimplex.δ (1 : Fin 2)
local notation "σL" => partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "σR" => partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "βL" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex σL)
local notation "βR" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex σR)
local notation "hvL" => specifiedCoconeLeftTriangleExtension_initial_base hp p c hc dB dC
local notation "hvR" => specifiedCoconeRightPrefixTriangleExtension_initial_base hp p c hc dB dC
local notation "hv" => specifiedCoconeRightRootExtension_initial_base hp p c hc dB dC
local notation "L" => specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "R" => specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC
local notation "S" => specifiedCoconeRightRootExtensionSpace hp p c hc dB dC

local notation "e" => partialColimitSpanRootLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "eL" => partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "eR" => partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "k₀" => stdSimplex.δ (0 : Fin 3)
local notation "F" => specifiedCoconeRightRootEndpoint hp p c hc dB dC

/-- 共通根辺へ移してからの終点評価は、元の左三角形の終点評価そのもの。 -/
lemma specifiedCoconeLeftCommonRootRestriction_endpoint :
    specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC ≫ F =
      specifiedCoconeLeftTerminalEvaluation hp p c hc dB dC := by
  dsimp only [specifiedCoconeLeftCommonRootRestriction, specifiedCoconeRightRootEndpoint]
  rw [Category.assoc, fixedExtensionBaseIso_edgeTarget q
    (specifiedCoconeLeftTriangleLongBase hp p c hc dB dC) a v
    ((hvL).trans (Category.assoc _ _ _)) hv (𝟙 Δ[1]) e
    ((Category.id_comp _).trans
      (specifiedCoconeLeftTriangleLongBase hp p c hc dB dC)) (Category.id_comp β)]
  dsimp only [specifiedCoconeLeftTriangleLongRestriction]
  rw [fixedExtensionRestriction_edgeTarget]
  exact fixedExtensionEdgeTarget_eq_of_vertex q βL (a ≫ k) v hvL
    ((𝟙 Δ[1]) ≫ k) k₀ e eL _
    (specifiedCoconeLeftTerminalEdge_base hp p c hc dB dC) (by decide)

/-- 元の実際の比較辺を共通根辺へ移しても、終点の同じ一単体を回収する。 -/
lemma specifiedCoconeLeftCommonRootRestriction_endpoint_edge
    {x y : (specifiedCoconeLeftTriangleExtensionSpace hp p c hc dB dC) _⦋0⦌}
    (s : (specifiedCoconeLeftTriangleExtensionSpace hp p c hc dB dC).Edge x y) :
    ((s.map (specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC)).map F).edge =
      (s.map (specifiedCoconeLeftTerminalEvaluation hp p c hc dB dC)).edge :=
  congrArg (fun z ↦ z.app _ s.edge)
    (specifiedCoconeLeftCommonRootRestriction_endpoint hp p c hc dB dC)

/-- 共通根辺へ移してからの終点評価は、元の右初面三角形の終点評価そのもの。 -/
lemma specifiedCoconeRightPrefixCommonRootRestriction_endpoint :
    specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC ≫ F =
      specifiedCoconeRightPrefixTerminalEvaluation hp p c hc dB dC := by
  dsimp only [specifiedCoconeRightPrefixCommonRootRestriction, specifiedCoconeRightRootEndpoint]
  rw [Category.assoc, fixedExtensionBaseIso_edgeTarget q
    (specifiedCoconeRightPrefixTriangleLongBase hp p c hc dB dC) a v
    ((hvR).trans (Category.assoc _ _ _)) hv (𝟙 Δ[1]) e
    ((Category.id_comp _).trans
      (specifiedCoconeRightPrefixTriangleLongBase hp p c hc dB dC)) (Category.id_comp β)]
  dsimp only [specifiedCoconeRightPrefixTriangleLongRestriction]
  rw [fixedExtensionRestriction_edgeTarget]
  exact fixedExtensionEdgeTarget_eq_of_vertex q βR (a ≫ k) v hvR
    ((𝟙 Δ[1]) ≫ k) k₀ e eR _
    (specifiedCoconeRightPrefixTerminalEdge_base hp p c hc dB dC) (by decide)

/-- 元の実際の比較辺を共通根辺へ移しても、終点の同じ一単体を回収する。 -/
lemma specifiedCoconeRightPrefixCommonRootRestriction_endpoint_edge
    {x y : (specifiedCoconeRightPrefixTriangleExtensionSpace hp p c hc dB dC) _⦋0⦌}
    (s : (specifiedCoconeRightPrefixTriangleExtensionSpace hp p c hc dB dC).Edge x y) :
    ((s.map (specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC)).map F).edge =
      (s.map (specifiedCoconeRightPrefixTerminalEvaluation hp p c hc dB dC)).edge :=
  congrArg (fun z ↦ z.app _ s.edge)
    (specifiedCoconeRightPrefixCommonRootRestriction_endpoint hp p c hc dB dC)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
