module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowPrismNativeAllBoundary
public import SerrePositivity.InfinityCategories.F2.Ind.FixedCoconeBoundaryUnderInclusion
/-!
概要：元の可縮持ち上げ空間の全体を、三条件固定の元の宇宙の余錐へ写す。
方針：同じ全境界比較の curry と宇宙比較を合成する。
規約：全底・全終点・始点評価の全余錐を保持する。
使われ方：三条件を全時刻で保つ比較円柱の構成。
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
local notation "e" => evaluateFunctorAt (Y := IndInfinity κ C)
  (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
local notation "e'" => evaluateFunctorAt (Y := IndInfinity κ C)
  (ULift.up (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
/-- 概要：元の全持ち上げ空間からの三固定条件を保つ全写像。
方針：元の三つの写像を合成する。規約：全係数を保持。使われ方：実円柱の指定。 -/
def indArrowTerminalNativeAllBoundaryMap : indArrowTerminalLiftFamily W ⟶
    fixedCoconeBoundaryUnder (p ≫ h) (b ≫ h) e' s :=
  indArrowTerminalPrismAllBoundaryMap W ≫ fixedArrowPrismAllBoundaryCurry
    (indArrowOriginalFamily κ D q ≫ indYoneda κ C) (liftedIntervalToSmall ≫ D) s ≫
      fixedCoconeBoundaryUnderPost p b e s h e'
        (arrowDiagramUniverseRestriction_evaluate_zero (IndInfinity κ C))
/-- 概要：再構成側の元の頂点像を厳密に回収。方針：元の合成を計算。
規約：元の頂点を保持。使われ方：円柱の始点。 -/
lemma indArrowTerminalNativeAllBoundaryMap_reconstructed :
    (indArrowTerminalNativeAllBoundaryMap W).app (Opposite.op ⦋0⦌)
    (indArrowTerminalReconstructedVertex W) =
      indArrowPrismNativeAllBoundaryReconstructedVertex W := rfl
/-- 概要：元の側の頂点像を厳密に回収。方針：元の合成を計算。
規約：元の頂点を保持。使われ方：円柱の終点。 -/
lemma indArrowTerminalNativeAllBoundaryMap_original :
    (indArrowTerminalNativeAllBoundaryMap W).app (Opposite.op ⦋0⦌)
    (indArrowTerminalOriginalVertex W) =
      indArrowPrismNativeAllBoundaryOriginalVertex W := rfl
end SerrePositivity.InfinityCategories.F2.Ind
