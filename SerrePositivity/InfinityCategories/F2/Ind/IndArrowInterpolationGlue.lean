module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationSlice

/-!
概要：元の全円柱と始点全錐を、同じ終点 slice 内の全補間図式へ貼り合わせる。
方針：実際の零端点の一致を用い、元の pushout の普遍性で貼る。
規約：元の両全図式を厳密に保持。使われ方：元の全変換への帰還の uncurry。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)

/-- 元の円柱と始点全錐を同じ終点 slice 内で厳密に貼った全図式。 -/
def indArrowInterpolationGlue :
    arrowInterpolationCorner ((SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))) ⟶
      sliceOver (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)) :=
  arrowInterpolationGlue (indArrowInterpolationSliceCylinder V)
    (indArrowSourceSliceLift κ D V.sourceCone) (indArrowInterpolationSliceCylinder_source V)

/-- 貼り合わせた全図式の元の円柱側は、同じ全 slice 円柱そのもの。 -/
lemma indArrowInterpolationGlue_old :
    pushout.inl SSet.ι₀
      (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))) Δ[0]) ≫
        indArrowInterpolationGlue V = indArrowInterpolationSliceCylinder V :=
  arrowInterpolationGlue_old _ _ _

/-- 貼り合わせた全図式の始点余錐側も、同じ元の全錐の組み替えそのもの。 -/
lemma indArrowInterpolationGlue_source :
    pushout.inr SSet.ι₀
      (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))) Δ[0]) ≫
        indArrowInterpolationGlue V = indArrowSourceSliceLift κ D V.sourceCone :=
  arrowInterpolationGlue_source _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
