module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowSlicePrismTerminalEdge
public import SerrePositivity.InfinityCategories.F2.Ind.FixedRelativeLiftBoundary

/-!
概要：元の実 slice 円柱と標準持ち上げを、同じ全終端辺を固定した fiber 内で比較する。
方針：全終端辺での厳密一致と、その包含の right anodyne 性を使う。
規約：元の底円柱と全区間 D を同型の全過程で固定。使われ方：元の q の全変換の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {H : T ⟶ pullback (indYoneda κ C) (sliceOverProjection D)}
  (W : IndArrowSlicePrism κ D q H)
local notation "p" => stdSimplex.δ 0 ≫ (liftedIntervalToSmall ≫ D)
local notation "b" => indArrowSlicePrismBaseCone (q := q)
local notation "i" => joinMap (arrowInterpolationSourceTip T) (𝟙 Δ[0])
local notation "f" => indArrowSlicePrismCone W
local notation "g" => conePointSliceLift p b (indArrowSlicePrismBaseCone_fixed W)

/-- 元の実持ち上げと標準持ち上げは、同じ指定全終端辺で厳密に一致する。 -/
lemma indArrowSlicePrismTerminalEdge_agreement : i ≫ g = i ≫ f :=
  (indArrowSlicePrismStandard_terminalEdge W).trans (indArrowSlicePrismCone_terminalEdge W).symm

/-- 元の全底と全終端辺を固定した実 fiber 内で、二つの持ち上げを結ぶ同型。 -/
def indArrowSlicePrismTerminalRelativeIso :
    VertexIso
      (relativeLiftFixedBoundaryVertex (sliceOverProjection p) b i f
        (indArrowSlicePrismCone_projection W) f (indArrowSlicePrismCone_projection W) rfl)
      (relativeLiftFixedBoundaryVertex (sliceOverProjection p) b i f
        (indArrowSlicePrismCone_projection W) g (conePointSliceLift_projection p b _)
        (indArrowSlicePrismTerminalEdge_agreement W)) :=
  rightAnodyneFixedRelativeLiftIso (sliceOverProjection p) b i
    (arrowInterpolationTerminalEdge_rightAnodyne T) f (indArrowSlicePrismCone_projection W)
    g (conePointSliceLift_projection p b _) (indArrowSlicePrismTerminalEdge_agreement W)

end SerrePositivity.InfinityCategories.F2.Ind
