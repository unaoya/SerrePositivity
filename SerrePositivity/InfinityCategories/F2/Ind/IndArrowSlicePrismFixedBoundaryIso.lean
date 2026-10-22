module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeSliceCoconeBoundaryVertex
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowSlicePrismConeComparison

/-!
概要：実補間円柱の相対同型を、底と指定終点を固定した元の全余錐の同型へ戻す。
方針：普遍相対 uncurry の固定境界 fiber への作用で同型を移す。
規約：元の全底円柱そのものと比較。使われ方：元の q の全変換の回収。
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
local notation "i" => joinInl (arrowInterpolationCorner T) Δ[0]

/-- 同じ全境界と終点を固定し、再構成した全余錐を元の全底余錐へ戻す実同型。 -/
def indArrowSlicePrismFixedBoundaryIso :
    VertexIso
      (fixedCoconeBoundaryVertex p (i ≫ b)
        (sliceOverUncurry (i ≫ indArrowSlicePrismCone W))
        (by rw [sliceOverUncurry_projection, Category.assoc, indArrowSlicePrismCone_projection])
        (sliceOverUncurry_fixed _))
      (fixedCoconeBoundaryVertex p (i ≫ b) b rfl (indArrowSlicePrismBaseCone_fixed W)) := by
  have e := relativeSliceFixedBoundaryIso p (i ≫ b) (i ≫ indArrowSlicePrismCone W)
    (sliceOverCurry b (indArrowSlicePrismBaseCone_fixed W))
    (by rw [Category.assoc, indArrowSlicePrismCone_projection])
    (sliceOverCurry_projection _ _) (indArrowSlicePrismConeBoundaryRelativeIso W)
  simpa only [sliceOverUncurry_curry] using e

end SerrePositivity.InfinityCategories.F2.Ind
