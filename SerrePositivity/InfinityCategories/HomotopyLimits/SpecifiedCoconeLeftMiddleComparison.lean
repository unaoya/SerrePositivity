module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftFirstCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftTerminalTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedExtensionVertexEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomotopyEvaluation

/-!
概要：同じ左三角形比較辺の中間評価を、既存の付加辺輸送同型の点評価と照合する。
方針：元の比較円柱の中間頂点制限を、初辺の終点の一点円柱の raw な射と同定する。
規約：同じ比較辺と実際の初辺を使う。使われ方：終端辺の自然性からの合成公式。
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
local notation "σ" => partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "β" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex σ)
local notation "i₀" => stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3)
local notation "v" => SSet.yonedaEquiv.symm c
local notation "hv" => specifiedCoconeLeftTriangleExtension_initial_base hp p c hc dB dC
local notation "e" => partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "he" => specifiedCoconeLeftTerminalEdge_base hp p c hc dB dC
local notation "T" => specifiedCoconeLeftTriangleComparison hp p c hc dB dC
local notation "s" => specifiedCoconeLeftTriangleComparisonExtensionEdge hp p c hc dB dC
local notation "F" => specifiedCoconeLeftMiddleEvaluation hp p c hc dB dC
local notation "H" => specifiedCoconeLeftFirstEndpointHomotopy hp p c hc dB dC

/-- 中間評価の実際の辺は、同じ初辺終点の一点円柱を評価した raw な辺である。 -/
lemma specifiedCoconeLeftMiddleComparison_point_diagram :
    SSet.yonedaEquiv.symm ((s).map F).edge =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 (Δ[1] : SSet.{u + 1})) ≫ (H).h := by
  apply vertexFiber_hom_ext q dB.vertex
  have ht := fixedExtensionEdgeSource_map_homotopy_raw q β i₀ v hv
    (stdSimplex.δ (0 : Fin 3)) e he
    (specifiedCoconeLeftRootedTriangle_projection hp p c hc dB dC)
    (coherentTransportTriangleVertex_projection q σ _)
    (specifiedCoconeLeftTriangleExtension_initial hp p c hc dB dC)
    (specifiedCoconeLeftStandardTriangleExtension_initial hp p c hc dB dC)
    (T).homotopy (T).projection (T).initial
  refine ht.trans ?_
  rw [Category.assoc, pointEdgeTransportEndpointHomotopy_projection,
    specifiedCoconeLeftFirstHomotopy_raw]
  simp only [← Category.assoc, lift_whiskerRight, SSet.const_comp]
  apply congrArg (fun z ↦ lift (SSet.const z) (𝟙 (Δ[1] : SSet.{u + 1})) ≫ (T).homotopy.h)
  decide

/-- 同じ比較辺の中間評価の類は、元の付加辺輸送同型の同じ点評価である。 -/
abbrev specifiedCoconeLeftMiddleComparison_hom_arrow :=
  pointHomotopy_evaluation_hom_arrow H
    (colimitAttachmentTransportPointIso c hc f (i ≫ p) rfl dB)
    (specifiedCoconeLeftFirstEndpointHomotopy_hom hp p c hc dB dC)
    ((s).map F) (specifiedCoconeLeftMiddleComparison_point_diagram hp p c hc dB dC)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
