module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowSlicePrismCone
public import SerrePositivity.InfinityCategories.F2.Ind.ConePointSliceComparison

/-!
概要：元の実 slice 円柱を、元の全底円柱の標準 slice 表示と底を固定して比較する。
方針：元の持ち上げから回収した恒等終点条件を、証明済みの一般比較へ渡す。
規約：追加の持ち上げ一意性を仮定しない。使われ方：元の q の全変換への帰還。
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

/-- 元の実円柱の領域側を、元の全底余錐の curry と底上で比較する指定同型。 -/
def indArrowSlicePrismConeBoundaryRelativeIso :
    VertexIso
      (relativeFunctorVertex
        (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)))
        (joinInl (arrowInterpolationCorner T) Δ[0] ≫ indArrowSlicePrismBaseCone (q := q))
        (joinInl (arrowInterpolationCorner T) Δ[0] ≫ indArrowSlicePrismCone W)
        (by rw [Category.assoc, indArrowSlicePrismCone_projection]))
      (relativeFunctorVertex
        (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)))
        (joinInl (arrowInterpolationCorner T) Δ[0] ≫ indArrowSlicePrismBaseCone (q := q))
        (sliceOverCurry (indArrowSlicePrismBaseCone (q := q)) (indArrowSlicePrismBaseCone_fixed W))
        (sliceOverCurry_projection _ _)) :=
  conePointSliceBoundaryRelativeIso _ _ (indArrowSlicePrismBaseCone_fixed W)
    (indArrowSlicePrismCone W) (indArrowSlicePrismCone_projection W)
    (indArrowSlicePrismCone_tip_uncurry W)

end SerrePositivity.InfinityCategories.F2.Ind
