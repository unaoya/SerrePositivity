module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowNormalizedPrism
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowSourceSliceLift
public import SerrePositivity.InfinityCategories.F2.Ind.IntervalSlicePrismLift

/-!
概要：元の射図式 comma の全円柱を、元の始点全錐とともに終点 slice へ持ち上げる。
方針：元の三境界の等式を照合し、構成済みの全円柱持ち上げに渡す。
規約：底・始点・終端側面を全て保持。使われ方：終点 comma の円柱族 F の実構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C)
  {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D)
  (H : T ⟶ pullback (indYoneda κ C) (sliceOverProjection D))

/-- 元の全円柱の終点 slice 持ち上げと、元の全境界の厳密な回収。 -/
structure IndArrowSlicePrism where
  val : join T (Δ[0] : SSet.{u + 1}) ⊗ Δ[1] ⟶
    sliceOver (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))
  projection : val ≫ sliceOverProjection
    (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)) = indArrowNormalizedPrism κ D q
  start : (join T (Δ[0] : SSet.{u + 1}) ◁ stdSimplex.δ 1) ≫ val =
    fst (join T Δ[0]) Δ[0] ≫ indArrowSourceSliceLift κ D H
  tip : (joinInr T (Δ[0] : SSet.{u + 1}) ▷ Δ[1]) ≫ val =
    snd Δ[0] Δ[1] ≫ intervalTerminalSliceSection (liftedIntervalToSmall.{u} ≫ D)

/-- 元の始点の全変換が一致すれば、元の全円柱の slice 持ち上げを実際に構成できる。 -/
lemma indArrowSlicePrism_nonempty
    (hH : H ≫ diagramConePointRestriction κ D (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) =
      q ≫ diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) :
    Nonempty (IndArrowSlicePrism κ D q H) := by
  let d := liftedIntervalToSmall.{u} ≫ D
  let f := H ≫ pullback.snd (indYoneda κ C) (sliceOverProjection D) ≫
    sliceOverRestrict D liftedIntervalToSmall
  have hs := congrArg (fun e => fst (join T (Δ[0] : SSet.{u + 1})) Δ[0] ≫ e)
    (indArrowSourceSliceLift_projection_of_initial κ D H q hH)
  have h0 : (join T (Δ[0] : SSet.{u + 1}) ◁ stdSimplex.δ 1) ≫
      indArrowNormalizedPrism κ D q = fst (join T Δ[0]) Δ[0] ≫
        sliceOverUncurry (f ≫ sliceOverRestrict d (stdSimplex.δ 1)) := by
    have h := (indArrowNormalizedPrism_first κ D q).trans
      (by simpa only [Category.assoc] using hs.symm)
    simpa only [f, d, indArrowSourceSliceLift, intervalSliceConeLift_projection,
      Category.assoc] using h
  obtain ⟨W, hp, hW, ht⟩ := exists_intervalSlice_prism_lift d f
    (indArrowNormalizedPrism κ D q) h0 (indArrowNormalizedPrism_tip κ D q)
  refine ⟨⟨W, hp, ?_, ht⟩⟩
  simpa only [f, d, indArrowSourceSliceLift] using hW

end SerrePositivity.InfinityCategories.F2.Ind
