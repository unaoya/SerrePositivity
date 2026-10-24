module

public import SerrePositivity.InfinityCategories.F2.Ind.FixedArrowPrismAllBoundaryCurry
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowPrismCurryComparison
/-!
概要：元の三境界固定比較を、指定始点の全余錐の下で curry して保持する。
方針：同じ実 fiber の全 curry で元の指定同型を写す。
規約：元の C 全図式・D・始点全余錐を同時に固定する。
使われ方：始点評価の下での補間比較の相対反映。
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
local notation "a" => indArrowOriginalFamily κ D q ≫ indYoneda κ C
local notation "d" => liftedIntervalToSmall ≫ D
local notation "s" => SSet.ι₀ ≫ indArrowNormalizedPrism κ D q
local notation "r" => Iso.inv (arrowInterpolationCoconeIso T) ≫
  sliceOverUncurry (arrowInterpolationCornerInclusion T ≫ W.val)
/-- 概要：三固定条件の下の再構成余錐。方針：同じ curry の像。
規約：全係数を保持。使われ方：相対比較の始点。 -/
def indArrowPrismCurriedAllBoundaryReconstructedVertex :=
  (fixedArrowPrismAllBoundaryCurry a d s).app (Opposite.op ⦋0⦌)
    (indArrowPrismAllBoundaryReconstructedVertex W)
/-- 概要：三固定条件の下の元の全余錐。方針：同じ curry の像。
規約：元の q を保持。使われ方：相対比較の終点。 -/
def indArrowPrismCurriedAllBoundaryOriginalVertex :=
  (fixedArrowPrismAllBoundaryCurry a d s).app (Opposite.op ⦋0⦌)
    (indArrowPrismAllBoundaryOriginalVertex W)
/-- 概要：指定始点評価を固定した同じ両全余錐の比較。方針：元の同型を写す。
規約：三つの全境界を保持。使われ方：宇宙比較と相対反映。 -/
def indArrowPrismCurriedAllBoundaryIso :
    VertexIso (indArrowPrismCurriedAllBoundaryReconstructedVertex W)
      (indArrowPrismCurriedAllBoundaryOriginalVertex W) :=
  VertexIso.map (indArrowPrismAllBoundaryIso W) (fixedArrowPrismAllBoundaryCurry a d s)
/-- 概要：再構成全余錐を厳密に回収。方針：元の curry の式。
規約：全射を保持。使われ方：相対反映の端点照合。 -/
lemma indArrowPrismCurriedAllBoundaryReconstructedVertex_val :
    (indArrowPrismCurriedAllBoundaryReconstructedVertex W).val.val =
    functorVertex (curry ((β_ (Δ[1] : SSet.{u + 1}) (join T Δ[0])).hom ≫ r)) := by
  change (indArrowPrismCurriedReconstructedVertex W).val = _
  exact indArrowPrismCurriedReconstructedVertex_val W
/-- 概要：元の全余錐を厳密に回収。方針：元の curry の式。
規約：全射を保持。使われ方：相対反映の端点照合。 -/
lemma indArrowPrismCurriedAllBoundaryOriginalVertex_val :
    (indArrowPrismCurriedAllBoundaryOriginalVertex W).val.val =
    functorVertex (curry ((β_ (Δ[1] : SSet.{u + 1}) (join T Δ[0])).hom ≫
      indArrowNormalizedPrism κ D q)) := by
  change (indArrowPrismCurriedOriginalVertex W).val = _
  exact indArrowPrismCurriedOriginalVertex_val W
end SerrePositivity.InfinityCategories.F2.Ind
