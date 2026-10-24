module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowTerminalNativeAllBoundary
public import SerrePositivity.InfinityCategories.Core.EquivalenceIntervalVertexIso
/-!
概要：元の両全余錐を、三条件を保つ可逆区間上の一つの全族へ延長する。
方針：元の可縮 Kan 持ち上げ空間で比較を表示し、三条件固定の全写像で写す。
規約：標的の固定 fiber の充填性を追加仮定にしない。
使われ方：評価後に定値となる実可逆円柱の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {H : T ⟶ pullback (indYoneda κ C) (sliceOverProjection D)}
  (W : IndArrowSlicePrism κ D q H)
local notation "p" => SSet.yonedaEquiv.symm (functorVertex (liftedIntervalToSmall ≫ D))
local notation "b" => curry (CategoryTheory.Iso.hom (β_ (Δ[1]) T) ≫
  indArrowOriginalFamily κ D q ≫ indYoneda κ C)
local notation "s" => SSet.ι₀ ≫ indArrowNormalizedPrism κ D q
local notation "h" => arrowDiagramUniverseRestriction (IndInfinity κ C)
local notation "e'" => evaluateFunctorAt (Y := IndInfinity κ C)
  (ULift.up (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
/-- 概要：三条件固定の元の両余錐を結ぶ実可逆区間上の族。
方針：元の Kan 空間で選んだ族を写す。規約：全境界を保持。使われ方：相対円柱。 -/
lemma exists_indArrowNativeAllBoundaryInterval :
    ∃ G : equivalenceInterval ⟶ fixedCoconeBoundaryUnder (p ≫ h) (b ≫ h) e' s,
    G.app (Opposite.op ⦋0⦌) (nerveEquiv.symm (Codiscrete.mk (ULift.up false))) =
      indArrowPrismNativeAllBoundaryReconstructedVertex W ∧
    G.app (Opposite.op ⦋0⦌) (nerveEquiv.symm (Codiscrete.mk (ULift.up true))) =
      indArrowPrismNativeAllBoundaryOriginalVertex W := by
  have : KanComplex (indArrowTerminalLiftFamily W) :=
    (indArrowTerminalLiftFamily_isContractibleKan W).kanComplex
  obtain ⟨G, h₀, h₁⟩ :=
    exists_equivalenceInterval_map_of_vertexIso (indArrowTerminalPrismVertexIso W)
  refine ⟨G ≫ indArrowTerminalNativeAllBoundaryMap W, ?_, ?_⟩
  · change (indArrowTerminalNativeAllBoundaryMap W).app _ (G.app _ _) = _
    rw [h₀]
    exact indArrowTerminalNativeAllBoundaryMap_reconstructed W
  · change (indArrowTerminalNativeAllBoundaryMap W).app _ (G.app _ _) = _
    rw [h₁]
    exact indArrowTerminalNativeAllBoundaryMap_original W
end SerrePositivity.InfinityCategories.F2.Ind
