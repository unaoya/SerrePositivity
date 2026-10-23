module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowTerminalPrismSourceIso
public import SerrePositivity.InfinityCategories.F2.Ind.FixedArrowPrismBoundaryCurry

/-!
概要：C 全図式・全 D・元の始点全余錐を同時に固定した実円柱比較。
方針：両側面固定 fiber を始点の全制限でさらに fiber 化し、同じ普遍族を持ち上げる。
規約：固定条件を途中で忘れない。使われ方：指定始点評価の下での同型の相対反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 両側面を固定した元の全円柱から、始点全余錐への制限。 -/
def fixedArrowPrismSourceRestriction {T X : SSet.{u}}
    (a : T ⊗ (Δ[1] : SSet.{u}) ⟶ X) (d : (Δ[1] : SSet.{u}) ⟶ X) :
    fixedArrowPrismBoundary a d ⟶ (ihom (join T (Δ[0] : SSet.{u}))).obj X :=
  fixedArrowPrismBoundaryInclusion a d ≫ (pre SSet.ι₀).app X

/-- 両側面と始点全余錐を共に固定した、元の全円柱の実 fiber。 -/
def fixedArrowPrismAllBoundary {T X : SSet.{u}}
    (a : T ⊗ (Δ[1] : SSet.{u}) ⟶ X) (d : (Δ[1] : SSet.{u}) ⟶ X)
    (s : join T (Δ[0] : SSet.{u}) ⟶ X) : SSet.{u} :=
  vertexFiber (fixedArrowPrismSourceRestriction a d) (functorVertex s)

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

/-- 同じ普遍比較族は、元の三つの全固定境界の実 fiber へ写る。 -/
def indArrowTerminalPrismAllBoundaryMap : indArrowTerminalLiftFamily W ⟶
    fixedArrowPrismAllBoundary a d s :=
  vertexFiberLift _ _ (indArrowTerminalPrismBoundaryMap W) (by
    change curry (indArrowTerminalPrismFamily W) ≫ (pre SSet.ι₀).app (IndInfinity κ C) = _
    exact indArrowTerminalPrismCurry_source W)

/-- 同じ全固定条件を保った再構成端点。 -/
def indArrowPrismAllBoundaryReconstructedVertex :=
  (indArrowTerminalPrismAllBoundaryMap W).app (Opposite.op ⦋0⦌)
    (indArrowTerminalReconstructedVertex W)

/-- 同じ全固定条件を保った元の端点。 -/
def indArrowPrismAllBoundaryOriginalVertex :=
  (indArrowTerminalPrismAllBoundaryMap W).app (Opposite.op ⦋0⦌)
    (indArrowTerminalOriginalVertex W)

/-- 三つの元の全境界を同時に固定した実 fiber 内での、同じ両全円柱の同型。 -/
def indArrowPrismAllBoundaryIso :
    VertexIso (indArrowPrismAllBoundaryReconstructedVertex W)
      (indArrowPrismAllBoundaryOriginalVertex W) :=
  VertexIso.map (indArrowTerminalPrismVertexIso W) (indArrowTerminalPrismAllBoundaryMap W)

/-- 全固定条件の包含後も、同じ再構成全円柱を厳密に回収する。 -/
lemma indArrowPrismAllBoundaryReconstructedVertex_val :
    (indArrowPrismAllBoundaryReconstructedVertex W).val.val = functorVertex r := by
  change (indArrowPrismReconstructedBoundaryVertex W).val = _
  exact indArrowPrismReconstructedBoundaryVertex_val W

/-- 全固定条件の包含後も、同じ元の q の全円柱を厳密に回収する。 -/
lemma indArrowPrismAllBoundaryOriginalVertex_val :
    (indArrowPrismAllBoundaryOriginalVertex W).val.val =
      functorVertex (indArrowNormalizedPrism κ D q) := by
  change (indArrowPrismOriginalBoundaryVertex W).val = _
  exact indArrowPrismOriginalBoundaryVertex_val W

end SerrePositivity.InfinityCategories.F2.Ind
