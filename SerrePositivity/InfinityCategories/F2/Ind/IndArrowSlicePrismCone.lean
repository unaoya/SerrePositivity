module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowSlicePrism
public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCoconeSurjective
public import SerrePositivity.InfinityCategories.F2.Ind.IntervalTerminalSliceLast

/-!
概要：元の実 slice 円柱を右余錐表示に移し、同じ底と恒等終点を回収する。
方針：補間領域の全円柱同型を前合成し、元の終端側面を最後の点へ制限する。
規約：元の q の全円柱を保持。使われ方：標準持ち上げとの実比較。
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

/-- 元の q の実全円柱を、同じ補間領域の右余錐として表示する。 -/
def indArrowSlicePrismBaseCone : join (arrowInterpolationCorner T) Δ[0] ⟶ IndInfinity κ C :=
  arrowInterpolationCocone T ≫ indArrowNormalizedPrism κ D q

/-- 元の実 slice 円柱の、同じ右余錐表示。 -/
def indArrowSlicePrismCone : join (arrowInterpolationCorner T) Δ[0] ⟶
    sliceOver (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)) :=
  arrowInterpolationCocone T ≫ W.val

/-- 同じ全底円柱を厳密に被覆する。 -/
lemma indArrowSlicePrismCone_projection : indArrowSlicePrismCone W ≫
    sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)) =
      indArrowSlicePrismBaseCone (q := q) := by
  rw [indArrowSlicePrismCone, Category.assoc, W.projection]
  rfl

/-- 右余錐の最後の点は、元の終端切断の最後の点そのもの。 -/
lemma indArrowSlicePrismCone_tip : joinInr (arrowInterpolationCorner T) Δ[0] ≫
    indArrowSlicePrismCone W =
      stdSimplex.δ 0 ≫ intervalTerminalSliceSection (liftedIntervalToSmall.{u} ≫ D) := by
  have hi := congrArg (fun f => f ≫ W.val) (arrowInterpolationCocone_inr T)
  have hn := congrArg (fun f => f ≫ W.val)
    (SSet.ι₁_comp (joinInr T (Δ[0] : SSet.{u + 1}))).symm
  have ht := congrArg (fun f => SSet.ι₁ ≫ f) W.tip
  have he : SSet.ι₁ ≫ snd (Δ[0] : SSet.{u + 1}) Δ[1] = stdSimplex.δ 0 := by
    rw [SSet.ι₁_snd, stdSimplex.δ_zero_eq_const]
  calc
    _ = joinInr T Δ[0] ≫ SSet.ι₁ ≫ W.val := by
      simpa only [indArrowSlicePrismCone, Category.assoc] using hi
    _ = SSet.ι₁ ≫ (joinInr T Δ[0] ▷ Δ[1]) ≫ W.val := by
      simpa only [Category.assoc] using hn
    _ = SSet.ι₁ ≫ snd Δ[0] Δ[1] ≫
        intervalTerminalSliceSection (liftedIntervalToSmall.{u} ≫ D) := by
      simpa only [Category.assoc] using ht
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ intervalTerminalSliceSection (liftedIntervalToSmall.{u} ≫ D)) he

include W in
/-- 右余錐の全底図式の終点は、元の指定終点そのもの。 -/
lemma indArrowSlicePrismBaseCone_fixed : joinInr (arrowInterpolationCorner T) Δ[0] ≫
    indArrowSlicePrismBaseCone (q := q) = stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D) := by
  have h := congrArg (fun f => f ≫ sliceOverProjection
    (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))) (indArrowSlicePrismCone_tip W)
  simpa only [Category.assoc, indArrowSlicePrismCone_projection,
    intervalTerminalSliceSection_projection] using h

/-- 実右余錐の終点条件は、同じ指定終点の恒等辺を全体で回収する。 -/
lemma indArrowSlicePrismCone_tip_uncurry :
    sliceOverUncurry (joinInr (arrowInterpolationCorner T) Δ[0] ≫ indArrowSlicePrismCone W) =
      SSet.const (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))) := by
  rw [indArrowSlicePrismCone_tip, intervalTerminalSliceSection_last]

/-- 右余錐表示の元の領域側は、同じ実 slice 円柱の制限そのもの。 -/
lemma indArrowSlicePrismCone_old : joinInl (arrowInterpolationCorner T) Δ[0] ≫
    indArrowSlicePrismCone W = arrowInterpolationCornerInclusion T ≫ W.val := by
  exact (congrArg (fun f => f ≫ W.val) (arrowInterpolationCocone_inl T)).trans
    (by rfl)

/-- 底の右余錐表示も、同じ元の全底円柱へ厳密に制限される。 -/
lemma indArrowSlicePrismBaseCone_old : joinInl (arrowInterpolationCorner T) Δ[0] ≫
    indArrowSlicePrismBaseCone (q := q) =
      arrowInterpolationCornerInclusion T ≫ indArrowNormalizedPrism κ D q := by
  simpa only [indArrowSlicePrismBaseCone, Category.assoc] using
    congrArg (fun f => f ≫ indArrowNormalizedPrism κ D q) (arrowInterpolationCocone_inl T)

end SerrePositivity.InfinityCategories.F2.Ind
