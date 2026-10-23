module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowPrismCurryComparison
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowNormalizedPrismCurry
public import SerrePositivity.InfinityCategories.F2.Ind.FixedCoconeBoundaryPost

/-!
概要：元の C 全図式と全 D を固定した比較を、元の宇宙の全図式余錐へ戻す。
方針：同じ区間の宇宙同型を両固定境界の fiber で後合成する。
規約：元の q の全余錐を厳密に回収。使われ方：同じ元の comma 族への相対帰還。
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
local notation "p" => SSet.yonedaEquiv.symm (functorVertex (liftedIntervalToSmall ≫ D))
local notation "b" => curry (Iso.hom (β_ (Δ[1]) T) ≫
  indArrowOriginalFamily κ D q ≫ indYoneda κ C)
local notation "h" => arrowDiagramUniverseRestriction (IndInfinity κ C)
local notation "r" => Iso.inv (arrowInterpolationCoconeIso T) ≫
  sliceOverUncurry (arrowInterpolationCornerInclusion T ≫ W.val)

/-- 元の宇宙で、同じ両全境界を固定した再構成余錐の頂点。 -/
def indArrowPrismNativeReconstructedVertex :=
  (fixedCoconeBoundaryPost p b h).app (Opposite.op ⦋0⦌)
    (indArrowPrismCurriedReconstructedVertex W)

/-- 元の宇宙で、同じ両全境界を固定した元の余錐の頂点。 -/
def indArrowPrismNativeOriginalVertex :=
  (fixedCoconeBoundaryPost p b h).app (Opposite.op ⦋0⦌)
    (indArrowPrismCurriedOriginalVertex W)

/-- 元の全図式の余錐の実 fiber 内で、同じ両全境界を保つ比較同型。 -/
def indArrowPrismNativeBoundaryIso :
    VertexIso (indArrowPrismNativeReconstructedVertex W)
      (indArrowPrismNativeOriginalVertex W) :=
  VertexIso.map (indArrowPrismCurriedBoundaryIso W) (fixedCoconeBoundaryPost p b h)

/-- 再構成側も、元の全円柱を同じ宇宙へ移した全余錐を回収する。 -/
lemma indArrowPrismNativeReconstructedVertex_val :
    (indArrowPrismNativeReconstructedVertex W).val =
      functorVertex (curry ((β_ (Δ[1] : SSet.{u + 1}) (join T Δ[0])).hom ≫ r) ≫ h) :=
  fixedCoconeBoundaryPost_vertex_val p b h _ _
    (indArrowPrismCurriedReconstructedVertex_val W)

/-- 元の側の全射は、同じ元の q の指定全余錐そのもの。 -/
lemma indArrowPrismNativeOriginalVertex_val :
    (indArrowPrismNativeOriginalVertex W).val =
      functorVertex (joinMap q (𝟙 Δ[0]) ≫ (diagramCommaCocone κ D).val) := by
  have e := fixedCoconeBoundaryPost_vertex_val p b h _ _
    (indArrowPrismCurriedOriginalVertex_val W)
  simpa only [indArrowPrismNativeOriginalVertex, arrowDiagramUniverseRestriction,
    indArrowNormalizedPrism_curry_original] using e

end SerrePositivity.InfinityCategories.F2.Ind
