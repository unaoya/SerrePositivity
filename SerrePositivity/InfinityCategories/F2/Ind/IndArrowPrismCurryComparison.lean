module

public import SerrePositivity.InfinityCategories.F2.Ind.FixedArrowPrismBoundaryCurry
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowTerminalPrismComparison

/-!
概要：元の両全円柱の比較を、両固定境界を持つ全図式の余錐の比較へ移す。
方針：実円柱 fiber の同型を同じ全 curry 射で写し、両端の元の全射を回収する。
規約：元の C 全図式と全 D を同時に固定。使われ方：元の comma 族への帰還。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {H : T ⟶ CategoryTheory.Limits.pullback (indYoneda κ C) (sliceOverProjection D)}
  (W : IndArrowSlicePrism κ D q H)
local notation "a" => indArrowOriginalFamily κ D q ≫ indYoneda κ C
local notation "d" => liftedIntervalToSmall ≫ D
local notation "r" => Iso.inv (arrowInterpolationCoconeIso T) ≫
  sliceOverUncurry (arrowInterpolationCornerInclusion T ≫ W.val)

/-- 同じ元の全図式と全区間を固定した、再構成余錐の頂点。 -/
def indArrowPrismCurriedReconstructedVertex :=
  (fixedArrowPrismBoundaryCurry a d).app (Opposite.op ⦋0⦌)
    (indArrowPrismReconstructedBoundaryVertex W)

/-- 同じ元の全図式と全区間を固定した、元の余錐の頂点。 -/
def indArrowPrismCurriedOriginalVertex :=
  (fixedArrowPrismBoundaryCurry a d).app (Opposite.op ⦋0⦌)
    (indArrowPrismOriginalBoundaryVertex W)

/-- 元の C 全図式と全 D を固定したままの、全図式の両余錐の比較同型。 -/
def indArrowPrismCurriedBoundaryIso :
    VertexIso (indArrowPrismCurriedReconstructedVertex W)
      (indArrowPrismCurriedOriginalVertex W) :=
  VertexIso.map (indArrowPrismBoundaryIso W) (fixedArrowPrismBoundaryCurry a d)

/-- 再構成余錐の元の全射は、同じ再構成円柱の区間 curry そのもの。 -/
lemma indArrowPrismCurriedReconstructedVertex_val :
    (indArrowPrismCurriedReconstructedVertex W).val =
      functorVertex (curry ((β_ (Δ[1] : SSet.{u + 1}) (join T Δ[0])).hom ≫ r)) := by
  change (rightTensorCurryMap (join T Δ[0]) Δ[1] (IndInfinity κ C)).app _
    (indArrowPrismReconstructedBoundaryVertex W).val = _
  rw [indArrowPrismReconstructedBoundaryVertex_val, rightTensorCurryMap_vertex]

/-- 元の余錐の全射は、元の q の同じ全円柱の区間 curry そのもの。 -/
lemma indArrowPrismCurriedOriginalVertex_val :
    (indArrowPrismCurriedOriginalVertex W).val =
      functorVertex (curry ((β_ (Δ[1] : SSet.{u + 1}) (join T Δ[0])).hom ≫
        indArrowNormalizedPrism κ D q)) := by
  change (rightTensorCurryMap (join T Δ[0]) Δ[1] (IndInfinity κ C)).app _
    (indArrowPrismOriginalBoundaryVertex W).val = _
  rw [indArrowPrismOriginalBoundaryVertex_val, rightTensorCurryMap_vertex]

end SerrePositivity.InfinityCategories.F2.Ind
