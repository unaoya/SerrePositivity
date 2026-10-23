module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowTerminalPrismSource
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowTerminalPrismComparison

/-!
概要：再構成円柱と元の円柱を、元の始点全余錐を固定した実 fiber 内で比較する。
方針：始点で定値な同じ普遍族を実 fiber に持ち上げ、元の比較同型を写す。
規約：同じ指定始点全変換を固定。使われ方：始点評価の下での比較の相対反映。
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
local notation "R" => join T Δ[0] ⊗ Δ[1]
local notation "r" => Iso.inv (arrowInterpolationCoconeIso T) ≫
  sliceOverUncurry (arrowInterpolationCornerInclusion T ≫ W.val)

/-- 同じ元の始点全余錐を固定した実円柱 fiber への普遍族の射。 -/
def indArrowTerminalPrismSourceMap : indArrowTerminalLiftFamily W ⟶
    vertexFiber ((pre (SSet.ι₀ : join T (Δ[0] : SSet.{u + 1}) ⟶ R)).app (IndInfinity κ C))
      (functorVertex (SSet.ι₀ ≫ indArrowNormalizedPrism κ D q)) :=
  vertexFiberLift _ _ (curry (indArrowTerminalPrismFamily W))
    (indArrowTerminalPrismCurry_source W)

/-- 始点全余錐を固定した、同じ再構成円柱の頂点。 -/
def indArrowPrismSourceReconstructedVertex :=
  (indArrowTerminalPrismSourceMap W).app (Opposite.op ⦋0⦌)
    (indArrowTerminalReconstructedVertex W)

/-- 始点全余錐を固定した、同じ元の円柱の頂点。 -/
def indArrowPrismSourceOriginalVertex :=
  (indArrowTerminalPrismSourceMap W).app (Opposite.op ⦋0⦌)
    (indArrowTerminalOriginalVertex W)

/-- 元の始点全余錐を固定した同じ実 fiber 内での、両全円柱の比較同型。 -/
def indArrowPrismSourceFixedIso :
    VertexIso (indArrowPrismSourceReconstructedVertex W) (indArrowPrismSourceOriginalVertex W) :=
  VertexIso.map (indArrowTerminalPrismVertexIso W) (indArrowTerminalPrismSourceMap W)

/-- 同じ再構成端点は、元の全円柱の頂点を厳密に回収する。 -/
lemma indArrowPrismSourceReconstructedVertex_val :
    (indArrowPrismSourceReconstructedVertex W).val = functorVertex r := by
  change (curry (indArrowTerminalPrismFamily W)).app (Opposite.op ⦋0⦌)
    (indArrowTerminalReconstructedVertex W) = _
  exact indArrowTerminalPrismBoundaryMap_vertex_val W _ _
    (indArrowTerminalPrismFamily_reconstructed W)

/-- 同じ元の端点も、元の q の全円柱の頂点そのものを回収する。 -/
lemma indArrowPrismSourceOriginalVertex_val :
    (indArrowPrismSourceOriginalVertex W).val =
      functorVertex (indArrowNormalizedPrism κ D q) := by
  change (curry (indArrowTerminalPrismFamily W)).app (Opposite.op ⦋0⦌)
    (indArrowTerminalOriginalVertex W) = _
  exact indArrowTerminalPrismBoundaryMap_vertex_val W _ _
    (indArrowTerminalPrismFamily_original W)

end SerrePositivity.InfinityCategories.F2.Ind
