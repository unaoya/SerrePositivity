module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationGlue
public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationInverseBoundary

/-!
概要：貼り合わせた終点 slice の全図式から、元の Ind 内の全変換を作る。
方針：全錐の uncurry と全円柱同型の逆を使い、元の C 図式と始点全錐を回収する。
規約：全パラメーターの図式を保持。使われ方：元の射図式 comma の余錐への帰還。
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

/-- 元の全円柱延長と始点全錐を含む、Ind 内の実際の全変換。 -/
def indArrowInterpolationSquare :
    join ((SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))) Δ[0] ⊗ Δ[1] ⟶
      IndInfinity κ C :=
  (arrowInterpolationCoconeIso
    ((SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u})))).inv ≫
      sliceOverUncurry (indArrowInterpolationGlue V)

/-- 元の円柱側の全制限は、同じ延長された C 全図式の Yoneda 像。 -/
lemma indArrowInterpolationSquare_old :
    (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))) Δ[0] ▷ Δ[1]) ≫
      indArrowInterpolationSquare V = indArrowInterpolationDiagram V ≫ indYoneda κ C := by
  let B := (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))
  have hi := congrArg (fun f => f ≫ sliceOverUncurry (indArrowInterpolationGlue V))
    (arrowInterpolationCoconeIso_inv_old B)
  have hp := sliceOverUncurry_projection (indArrowInterpolationGlue V)
  calc
    _ = pushout.inl SSet.ι₀ (joinInl B Δ[0]) ≫
        joinInl (arrowInterpolationCorner B) Δ[0] ≫
          sliceOverUncurry (indArrowInterpolationGlue V) := by
      simpa only [indArrowInterpolationSquare, Category.assoc] using hi
    _ = pushout.inl SSet.ι₀ (joinInl B Δ[0]) ≫ indArrowInterpolationGlue V ≫
        sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)) := by rw [hp]
    _ = indArrowInterpolationSliceCylinder V ≫
        sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)) := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫
        sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)))
          (indArrowInterpolationGlue_old V)
    _ = _ := indArrowInterpolationSliceCylinder_projection V

/-- 零端点の全制限は、同じ元の始点全錐の全始点制限。 -/
lemma indArrowInterpolationSquare_source : SSet.ι₀ ≫ indArrowInterpolationSquare V =
    sliceOverUncurry (V.sourceCone ≫ pullback.snd (indYoneda κ C) (sliceOverProjection D) ≫
      sliceOverRestrict D (diagramShapePoint (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))) := by
  let B := (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))
  have hi := congrArg (fun f => f ≫ sliceOverUncurry (indArrowInterpolationGlue V))
    (arrowInterpolationCoconeIso_inv_source B)
  have hp := sliceOverUncurry_projection (indArrowInterpolationGlue V)
  calc
    _ = pushout.inr SSet.ι₀ (joinInl B Δ[0]) ≫
        joinInl (arrowInterpolationCorner B) Δ[0] ≫
          sliceOverUncurry (indArrowInterpolationGlue V) := by
      simpa only [indArrowInterpolationSquare, Category.assoc] using hi
    _ = pushout.inr SSet.ι₀ (joinInl B Δ[0]) ≫ indArrowInterpolationGlue V ≫
        sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)) := by rw [hp]
    _ = indArrowSourceSliceLift κ D V.sourceCone ≫
        sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)) := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫
        sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)))
          (indArrowInterpolationGlue_source V)
    _ = _ := indArrowSourceSliceLift_projection κ D V.sourceCone

end SerrePositivity.InfinityCategories.F2.Ind
