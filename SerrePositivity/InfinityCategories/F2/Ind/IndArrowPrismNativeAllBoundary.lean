module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowPrismCurriedAllBoundary
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowPrismNativeCoconeComparison
/-!
概要：三境界固定比較を、指定始点の全余錐を保持して元の区間の宇宙へ戻す。
方針：同じ全 curry の比較を、始点評価と可換する宇宙比較で写す。
規約：元の全 C 図式・D・始点全余錐と指定同型を保持する。
使われ方：指定始点評価の下での全 comma 族の相対反映。
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
local notation "m" => fixedCoconeBoundaryUnderPost p b e s h e'
  (arrowDiagramUniverseRestriction_evaluate_zero (IndInfinity κ C))
local notation "r" => Iso.inv (arrowInterpolationCoconeIso T) ≫
  sliceOverUncurry (arrowInterpolationCornerInclusion T ≫ W.val)
/-- 概要：元の宇宙の三固定条件下の再構成余錐。方針：同じ後合成の像。
規約：全係数を保持。使われ方：相対比較の始点。 -/
def indArrowPrismNativeAllBoundaryReconstructedVertex :=
  NatTrans.app m (Opposite.op ⦋0⦌) (indArrowPrismCurriedAllBoundaryReconstructedVertex W)
/-- 概要：元の宇宙の三固定条件下の元の余錐。方針：同じ後合成の像。
規約：元の q を保持。使われ方：相対比較の終点。 -/
def indArrowPrismNativeAllBoundaryOriginalVertex :=
  NatTrans.app m (Opposite.op ⦋0⦌) (indArrowPrismCurriedAllBoundaryOriginalVertex W)
/-- 概要：元の始点評価と両境界を固定した同じ両全余錐の比較。
方針：元の同型を宇宙比較で写す。規約：指定値を保持。使われ方：相対反映。 -/
def indArrowPrismNativeAllBoundaryIso :
    VertexIso (indArrowPrismNativeAllBoundaryReconstructedVertex W)
      (indArrowPrismNativeAllBoundaryOriginalVertex W) :=
  VertexIso.map (indArrowPrismCurriedAllBoundaryIso W) m
/-- 概要：同じ再構成全余錐の厳密な回収。方針：元の宇宙比較の頂点の式。
規約：全射を保持。使われ方：相対反映の端点照合。 -/
lemma indArrowPrismNativeAllBoundaryReconstructedVertex_val :
    (indArrowPrismNativeAllBoundaryReconstructedVertex W).val.val =
    functorVertex (curry ((β_ (Δ[1] : SSet.{u + 1}) (join T Δ[0])).hom ≫ r) ≫ h) := by
  change (indArrowPrismNativeReconstructedVertex W).val = _
  exact indArrowPrismNativeReconstructedVertex_val W
/-- 概要：同じ元の q の全余錐の厳密な回収。方針：元の余錐の頂点の式。
規約：全射を保持。使われ方：相対反映の端点照合。 -/
lemma indArrowPrismNativeAllBoundaryOriginalVertex_val :
    (indArrowPrismNativeAllBoundaryOriginalVertex W).val.val =
    functorVertex (joinMap q (𝟙 Δ[0]) ≫ (diagramCommaCocone κ D).val) := by
  change (indArrowPrismNativeOriginalVertex W).val = _
  exact indArrowPrismNativeOriginalVertex_val W
end SerrePositivity.InfinityCategories.F2.Ind
