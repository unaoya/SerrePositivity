module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowTerminalPrismEndpoints
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowTerminalPrismBoundaryMap

/-!
概要：再構成した円柱と元の円柱を、元の C 図式と全区間 D を固定した fiber 内で比較する。
方針：実普遍族の両指定頂点と、同じ固定境界 fiber への全射で同型を移す。
規約：境界条件を忘れず元の全円柱を回収。使われ方：元の q の全変換の同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {H : T ⟶ pullback (indYoneda κ C) (sliceOverProjection D)}
  (W : IndArrowSlicePrism κ D q H)
local notation "R" => join T Δ[0] ⊗ Δ[1]
local notation "a" => indArrowOriginalFamily κ D q ≫ indYoneda κ C
local notation "d" => liftedIntervalToSmall ≫ D
local notation "r" => Iso.inv (arrowInterpolationCoconeIso T) ≫
  sliceOverUncurry (arrowInterpolationCornerInclusion T ≫ W.val)

/-- 普遍円柱の頂点での全射の回収は、固定境界 fiber の包含後にも同じ頂点を与える。 -/
lemma indArrowTerminalPrismBoundaryMap_vertex_val
    (v : (indArrowTerminalLiftFamily W) _⦋0⦌) (c : R ⟶ IndInfinity κ C)
    (hv : (R ◁ SSet.yonedaEquiv.symm v) ≫ indArrowTerminalPrismFamily W = fst R Δ[0] ≫ c) :
    ((indArrowTerminalPrismBoundaryMap W).app (Opposite.op ⦋0⦌) v).val = functorVertex c := by
  change (curry (indArrowTerminalPrismFamily W)).app (Opposite.op ⦋0⦌) v = functorVertex c
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_comp]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, hv, SSet.yonedaEquiv_symm_zero,
    uncurry_const_functorVertex]

/-- 元の C 全図式と全 D を固定した、再構成円柱の頂点。 -/
def indArrowPrismReconstructedBoundaryVertex : (fixedArrowPrismBoundary a d) _⦋0⦌ :=
  (indArrowTerminalPrismBoundaryMap W).app (Opposite.op ⦋0⦌) (indArrowTerminalReconstructedVertex W)

/-- 元の C 全図式と全 D を固定した、元の円柱の頂点。 -/
def indArrowPrismOriginalBoundaryVertex : (fixedArrowPrismBoundary a d) _⦋0⦌ :=
  (indArrowTerminalPrismBoundaryMap W).app (Opposite.op ⦋0⦌) (indArrowTerminalOriginalVertex W)

/-- 両指定全境界を固定した同じ実 fiber 内で、元の全円柱を比較する同型。 -/
def indArrowPrismBoundaryIso :
    VertexIso (indArrowPrismReconstructedBoundaryVertex W)
      (indArrowPrismOriginalBoundaryVertex W) :=
  VertexIso.map (indArrowTerminalPrismVertexIso W) (indArrowTerminalPrismBoundaryMap W)

/-- 最初の頂点の元の全写像は、同じ実 slice 円柱から再構成した円柱そのもの。 -/
lemma indArrowPrismReconstructedBoundaryVertex_val :
    (indArrowPrismReconstructedBoundaryVertex W).val = functorVertex r :=
  indArrowTerminalPrismBoundaryMap_vertex_val W _ _ (indArrowTerminalPrismFamily_reconstructed W)

/-- 次の頂点の元の全写像は、同じ元の q の全円柱そのもの。 -/
lemma indArrowPrismOriginalBoundaryVertex_val :
    (indArrowPrismOriginalBoundaryVertex W).val = functorVertex (indArrowNormalizedPrism κ D q) :=
  indArrowTerminalPrismBoundaryMap_vertex_val W _ _ (indArrowTerminalPrismFamily_original W)

/-- 固定境界の比較は、同じ元の全円柱の通常の関手同型としても読める。 -/
def indArrowReconstructionPrismIso : FunctorIso r (indArrowNormalizedPrism κ D q) := by
  have e := VertexIso.map (indArrowPrismBoundaryIso W)
    (vertexFiberι (arrowPrismBoundaryRestriction T (IndInfinity κ C))
      (functorVertex a, functorVertex (snd (Δ[0] : SSet.{u + 1}) Δ[1] ≫ d)))
  change VertexIso (indArrowPrismReconstructedBoundaryVertex W).val
    (indArrowPrismOriginalBoundaryVertex W).val at e
  simpa only [indArrowPrismReconstructedBoundaryVertex_val,
    indArrowPrismOriginalBoundaryVertex_val] using e

end SerrePositivity.InfinityCategories.F2.Ind
