module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeNativeBaseDiagrams
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftAttachmentNativeEdges
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightAttachmentNativeEdges
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftRootNativeCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootNativeCylinder

/-!
概要：付加辺面と根辺の元の比較円柱を、同じ native 全図式族の二面として表示する。
方針：両辺の全族の厳密な一致を、元の切断比較の同じ選択へ代入する。
規約：円柱の代表を選び直さない。使われ方：元の native 二単体の指定経路の照合。
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
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "P" => Iso.hom (leftFibrationInitialBaseIso q c y)
local notation "root" => specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "rs" => specifiedCoconeNativeRootEdge_source hp p c hc dB dC
local notation "rt" => specifiedCoconeNativeRootEdge_target hp p c hc dB dC
local notation "d" => partialColimitSpecifiedPathCocone hp p c hc dB dC

section
local notation "σ" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
local notation "N" => specifiedCoconeLeftNativeBaseDiagramFamily hp p c hc dB dC y
local notation "e" => colimitAttachmentRestrictionEdge c hc f (i ≫ p) rfl dB
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "face" => stdSimplex.δ (2 : Fin 3)
local notation "af" => specifiedCoconeLeftNativeBaseDiagram_attachment hp p c hc dB dC
local notation "rf" => specifiedCoconeLeftNativeBaseDiagram_root hp p c hc dB dC
local notation "A" => N ≫ normalizedCoconeRestrictionFiber σ face af y
local notation "R" => N ≫ normalizedCoconeRestrictionFiber σ (stdSimplex.δ (1 : Fin 3)) rf y

/-- 左の付加辺面の元の円柱は、同じ native 全図式族の辺01の切断比較そのもの。 -/
lemma specifiedCoconeLeftAttachmentHomotopy_native_face_raw :
    (specifiedCoconeLeftAttachmentHomotopy hp p c hc dB dC y).h =
      (cosliceEdgeFamilyPrecompositionCylinder (t ≫ q) y A
        (SSet.yonedaEquiv.symm c ≫ q) (stdSimplex.δ (0 : Fin 2) ≫ (t ≫ q))
        (initialTotalEdgeBase_source q e) rfl).h ≫ P := by
  rw [specifiedCoconeLeftAttachmentHomotopy_raw,
    ← Category.assoc (specifiedCoconeLeftAttachmentInitialHomotopy hp p c hc dB dC y).h,
    specifiedCoconeLeftAttachmentInitialHomotopy_projection]
  exact congrArg (fun F ↦ (cosliceEdgeFamilyPrecompositionCylinder (t ≫ q) y F
    (SSet.yonedaEquiv.symm c ≫ q) (stdSimplex.δ (0 : Fin 2) ≫ (t ≫ q))
    (initialTotalEdgeBase_source q e) rfl).h ≫ P)
    (specifiedCoconeLeftNativeBaseDiagramFamily_attachment hp p c hc dB dC y).symm

/-- 左の元の根辺円柱も、同じ native 全図式族の根辺の切断比較そのもの。 -/
lemma specifiedCoconeLeftRootNativeCylinder_native_face_raw :
    (specifiedCoconeLeftRootNativeCylinder hp p c hc dB dC y).h =
      (cosliceEdgeFamilyPrecompositionCylinder root y R
        (coconeVertexDiagram c) (coconeVertexDiagram d) rs rt).h ≫ P := by
  change (cosliceEdgeFamilyPrecompositionCylinder root y
      (specifiedCoconeLeftRootBaseEdgeFiberFamily hp p c hc dB dC y)
      (coconeVertexDiagram c) (coconeVertexDiagram d) rs rt).h ≫ P = _
  exact congrArg (fun F ↦ (cosliceEdgeFamilyPrecompositionCylinder root y F
    (coconeVertexDiagram c) (coconeVertexDiagram d) rs rt).h ≫ P)
    (specifiedCoconeLeftNativeBaseDiagramFamily_root hp p c hc dB dC y).symm
end

section
local notation "σ" => stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
local notation "N" => specifiedCoconeRightNativeBaseDiagramFamily hp p c hc dB dC y
local notation "e" => colimitAttachmentRestrictionEdge c hc g (j ≫ p)
    (coconePushoutBoundary_eq hp p) dC
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "face" => stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)
local notation "af" => specifiedCoconeRightNativeBaseDiagram_attachment hp p c hc dB dC
local notation "rf" => specifiedCoconeRightNativeBaseDiagram_root hp p c hc dB dC
local notation "A" => N ≫ normalizedCoconeRestrictionFiber σ face af y
local notation "R" => N ≫ normalizedCoconeRestrictionFiber σ (tetrahedronRootEdge) rf y

/-- 右の付加辺面の元の円柱は、同じ native 全図式族の辺01の切断比較そのもの。 -/
lemma specifiedCoconeRightAttachmentHomotopy_native_face_raw :
    (specifiedCoconeRightAttachmentHomotopy hp p c hc dB dC y).h =
      (cosliceEdgeFamilyPrecompositionCylinder (t ≫ q) y A
        (SSet.yonedaEquiv.symm c ≫ q) (stdSimplex.δ (0 : Fin 2) ≫ (t ≫ q))
        (initialTotalEdgeBase_source q e) rfl).h ≫ P := by
  rw [specifiedCoconeRightAttachmentHomotopy_raw,
    ← Category.assoc (specifiedCoconeRightAttachmentInitialHomotopy hp p c hc dB dC y).h,
    specifiedCoconeRightAttachmentInitialHomotopy_projection]
  exact congrArg (fun F ↦ (cosliceEdgeFamilyPrecompositionCylinder (t ≫ q) y F
    (SSet.yonedaEquiv.symm c ≫ q) (stdSimplex.δ (0 : Fin 2) ≫ (t ≫ q))
    (initialTotalEdgeBase_source q e) rfl).h ≫ P)
    (specifiedCoconeRightNativeBaseDiagramFamily_attachment hp p c hc dB dC y).symm

/-- 右の元の根辺円柱も、同じ native 全図式族の根辺の切断比較そのもの。 -/
lemma specifiedCoconeRightRootNativeCylinder_native_face_raw :
    (specifiedCoconeRootNativeCylinder hp p c hc dB dC y).h =
      (cosliceEdgeFamilyPrecompositionCylinder root y R
        (coconeVertexDiagram c) (coconeVertexDiagram d) rs rt).h ≫ P := by
  change (cosliceEdgeFamilyPrecompositionCylinder root y
      (specifiedCoconeRootBaseEdgeFiberFamily hp p c hc dB dC y)
      (coconeVertexDiagram c) (coconeVertexDiagram d) rs rt).h ≫ P = _
  exact congrArg (fun F ↦ (cosliceEdgeFamilyPrecompositionCylinder root y F
    (coconeVertexDiagram c) (coconeVertexDiagram d) rs rt).h ≫ P)
    (specifiedCoconeRightNativeBaseDiagramFamily_root hp p c hc dB dC y).symm
end

end
end SerrePositivity.InfinityCategories.HomotopyLimits
