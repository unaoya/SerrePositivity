module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowTerminalFamilyVertices

/-!
概要：終端辺固定の普遍円柱の両指定頂点で、元の円柱と再構成円柱を厳密に回収する。
方針：全族の頂点公式と標準持ち上げの制限の往復則を使う。
規約：同じ固定 fiber 内の元の頂点同型を保持。使われ方：元の q の全変換の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {H : T ⟶ pullback (indYoneda κ C) (sliceOverProjection D)}
  (W : IndArrowSlicePrism κ D q H)
local notation "S" => indArrowTerminalLiftFamily W
local notation "p" => stdSimplex.δ 0 ≫ (liftedIntervalToSmall ≫ D)
local notation "b" => indArrowSlicePrismBaseCone (q := q)
local notation "i" => joinMap (arrowInterpolationSourceTip T) (𝟙 Δ[0])
local notation "f" => indArrowSlicePrismCone W

/-- 元の実持ち上げ自身を表す、同じ終端辺固定 fiber の頂点。 -/
def indArrowTerminalReconstructedVertex : S _⦋0⦌ :=
  relativeLiftFixedBoundaryVertex (sliceOverProjection p) b i f
    (indArrowSlicePrismCone_projection W) f (indArrowSlicePrismCone_projection W) rfl

/-- 元の全底円柱の標準持ち上げを表す、同じ終端辺固定 fiber の頂点。 -/
def indArrowTerminalOriginalVertex : S _⦋0⦌ :=
  relativeLiftFixedBoundaryVertex (sliceOverProjection p) b i f
    (indArrowSlicePrismCone_projection W)
    (conePointSliceLift p b (indArrowSlicePrismBaseCone_fixed W))
    (conePointSliceLift_projection p b _) (indArrowSlicePrismTerminalEdge_agreement W)

/-- 元の全底と終端辺を固定した fiber 内で、両指定頂点を結ぶ同じ比較。 -/
def indArrowTerminalPrismVertexIso :
    VertexIso (indArrowTerminalReconstructedVertex W) (indArrowTerminalOriginalVertex W) :=
  indArrowSlicePrismTerminalRelativeIso W

/-- 実持ち上げの頂点では、元の領域から再構成した同じ全円柱を回収する。 -/
lemma indArrowTerminalPrismFamily_reconstructed :
    ((join T (Δ[0] : SSet.{u + 1}) ⊗ Δ[1]) ◁
      SSet.yonedaEquiv.symm (indArrowTerminalReconstructedVertex W)) ≫
        indArrowTerminalPrismFamily W = fst (join T Δ[0] ⊗ Δ[1]) Δ[0] ≫
          (arrowInterpolationCoconeIso T).inv ≫
            sliceOverUncurry (arrowInterpolationCornerInclusion T ≫ W.val) := by
  simpa only [indArrowTerminalReconstructedVertex, indArrowSlicePrismCone_old] using
    indArrowTerminalPrismFamily_vertex W f (indArrowSlicePrismCone_projection W) rfl

/-- 標準持ち上げの頂点では、元の同じ全底円柱そのものを回収する。 -/
lemma indArrowTerminalPrismFamily_original :
    ((join T (Δ[0] : SSet.{u + 1}) ⊗ Δ[1]) ◁
      SSet.yonedaEquiv.symm (indArrowTerminalOriginalVertex W)) ≫ indArrowTerminalPrismFamily W =
        fst (join T Δ[0] ⊗ Δ[1]) Δ[0] ≫ indArrowNormalizedPrism κ D q := by
  have hb : (arrowInterpolationCoconeIso T).inv ≫ b = indArrowNormalizedPrism κ D q := by
    change (arrowInterpolationCoconeIso T).inv ≫ (arrowInterpolationCoconeIso T).hom ≫ _ = _
    rw [Iso.inv_hom_id_assoc]
  simpa only [indArrowTerminalOriginalVertex, conePointSliceLift_old,
    sliceOverUncurry_curry, hb] using
    indArrowTerminalPrismFamily_vertex W
      (conePointSliceLift p b (indArrowSlicePrismBaseCone_fixed W))
      (conePointSliceLift_projection p b _) (indArrowSlicePrismTerminalEdge_agreement W)

end SerrePositivity.InfinityCategories.F2.Ind
