module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationCylinder

/-!
概要：元の全円柱延長の C 図式と終点 slice の全円柱を回収する。
方針：元の実引き戻しの両射影で読み、同じ元の全境界を計算する。
規約：元の C と Ind の全図式を保持。使われ方：元の射図式 comma の余錐への帰還。
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

/-- 延長された全円柱の元の C 図式。 -/
def indArrowInterpolationDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u})) ⊗ Δ[1] ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj C :=
  indArrowInterpolationRawCylinder V ≫ pullback.fst (indYoneda κ C)
    (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)))

/-- 延長された全円柱の同じ終点 slice 内の全族。 -/
def indArrowInterpolationSliceCylinder :
    (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u})) ⊗ Δ[1] ⟶
      sliceOver (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)) :=
  indArrowInterpolationRawCylinder V ≫ pullback.snd (indYoneda κ C)
    (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)))

/-- 同じ slice 円柱は元の C 全図式の Yoneda 像を厳密に被覆する。 -/
lemma indArrowInterpolationSliceCylinder_projection : indArrowInterpolationSliceCylinder V ≫
    sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)) =
      indArrowInterpolationDiagram V ≫ indYoneda κ C := by
  simpa only [indArrowInterpolationSliceCylinder, indArrowInterpolationDiagram,
    Category.assoc] using congrArg (fun f => indArrowInterpolationRawCylinder V ≫ f)
      (pullback.condition (f := indYoneda κ C)
        (g := sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)))).symm

/-- slice 円柱の始点は、元の始点全錐の同じ組み替えの族側。 -/
lemma indArrowInterpolationSliceCylinder_source : SSet.ι₀ ≫ indArrowInterpolationSliceCylinder V =
    joinInl ((SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}))) Δ[0] ≫
      indArrowSourceSliceLift κ D V.sourceCone := by
  simpa only [indArrowInterpolationSliceCylinder, Category.assoc,
    indArrowSourceEndpointRaw_slice] using congrArg (fun f => f ≫
      pullback.snd (indYoneda κ C)
        (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))))
          (indArrowInterpolationRawCylinder_source V)

/-- 元の全試験族側の slice 円柱は、元の構成した全持ち上げの制限そのもの。 -/
lemma indArrowInterpolationSliceCylinder_old :
    ((SSet.uliftFunctor.{u + 1, u}).map (joinInl A (Δ[0] : SSet.{u})) ▷ Δ[1]) ≫
      indArrowInterpolationSliceCylinder V =
        (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ▷ Δ[1]) ≫ V.slicePrism.val := by
  simpa only [indArrowInterpolationSliceCylinder, Category.assoc, indArrowEndpointRaw_slice] using
    congrArg (fun f => f ≫ pullback.snd (indYoneda κ C)
      (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))))
        (indArrowInterpolationRawCylinder_old V)

/-- 元の全試験族側の C 図式は同じ元の全射図式の族。 -/
lemma indArrowInterpolationDiagram_old :
    ((SSet.uliftFunctor.{u + 1, u}).map (joinInl A (Δ[0] : SSet.{u})) ▷ Δ[1]) ≫
      indArrowInterpolationDiagram V = indArrowOriginalFamily κ D q := by
  simpa only [indArrowInterpolationDiagram, Category.assoc, indArrowEndpointRaw_projection] using
    congrArg (fun f => f ≫ pullback.fst (indYoneda κ C)
      (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))))
        (indArrowInterpolationRawCylinder_old V)

end SerrePositivity.InfinityCategories.F2.Ind
