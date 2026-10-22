module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowSlicePrism
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowSourceEndpointFamily

/-!
概要：元の射図式の全円柱を、元の終点 comma 内の円柱族 F として実構成する。
方針：元の C 全図式と構成した slice 持ち上げを厳密に引き戻し、元の終点へ戻す。
規約：射影は元の C 全図式そのもの。使われ方：始点余錐と貼り合わせる二段補間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C)
  {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D)
  (H : T ⟶ pullback (indYoneda κ C) (sliceOverProjection D)) (V : IndArrowSlicePrism κ D q H)

/-- 元の C 全図式と実際の slice 円柱の、元の終点上の厳密な引き戻し。 -/
def indArrowEndpointRaw : T ⊗ (Δ[1] : SSet.{u + 1}) ⟶ pullback (indYoneda κ C)
    (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))) :=
  pullback.lift (indArrowOriginalFamily κ D q)
    ((joinInl T (Δ[0] : SSet.{u + 1}) ▷ Δ[1]) ≫ V.val)
    (by simpa only [Category.assoc, V.projection] using
      (indArrowNormalizedPrism_old κ D q).symm)

/-- 引き戻しの C 射影は元の全射図式の族そのもの。 -/
lemma indArrowEndpointRaw_projection : indArrowEndpointRaw κ D q H V ≫
    pullback.fst (indYoneda κ C)
      (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))) =
        indArrowOriginalFamily κ D q := pullback.lift_fst _ _ _

/-- 引き戻しの全錐は、元の試験族側の同じ slice 円柱の制限そのもの。 -/
lemma indArrowEndpointRaw_slice : indArrowEndpointRaw κ D q H V ≫
    pullback.snd (indYoneda κ C)
      (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))) =
        (joinInl T (Δ[0] : SSet.{u + 1}) ▷ Δ[1]) ≫ V.val := pullback.lift_snd _ _ _

/-- 元の指定終点の実 comma 内の円柱族 F。 -/
def indArrowEndpointFamily : T ⊗ (Δ[1] : SSet.{u + 1}) ⟶ leftKanShape (indYoneda κ C)
    (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))) :=
  indArrowEndpointRaw κ D q H V ≫ (indArrowEndpointCommaIso κ D).hom

/-- 元の終点 comma の円柱族は、元の C 全図式を厳密に保つ。 -/
lemma indArrowEndpointFamily_projection : indArrowEndpointFamily κ D q H V ≫
    leftKanProjection (indYoneda κ C)
      (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))) =
        indArrowOriginalFamily κ D q := by
  rw [indArrowEndpointFamily, Category.assoc, indArrowEndpointCommaIso_projection,
    indArrowEndpointRaw_projection]

end SerrePositivity.InfinityCategories.F2.Ind
