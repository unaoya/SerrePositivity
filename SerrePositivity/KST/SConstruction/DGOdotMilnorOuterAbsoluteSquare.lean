module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorOuterProjectionComparison
public import SerrePositivity.KST.SConstruction.DGOdotMilnorOuterInclusionComparison
public import SerrePositivity.KST.SConstruction.DGKPerfectNuEquivalence

/-!
概要：元 LT 長方形の絶対外周の四完全射を同じ Cat^perf 全一単体として回収する。
方針：元外周の指定辺と元恒等右面の零上辺を、同じ包含で検出する。
規約：元長方形の両合成二単体を選び直さない。
使われ方：元実外周の四境界全比較の終端表示。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "L" => dgOdotMilnorCompletedLaxQuotient R d h
local notation "hA" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalSource_isIdempotentComplete R d
local notation "hL" => perfectLaxCategory_isIdempotentComplete
  (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d)
  (dgOdotMilnorLaxLeft_complete R d) (dgOdotMilnorLaxRight_complete R d)
local notation "hQ" => dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonalSource R d
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

/-- 概要：絶対外周の零上辺は同じ右恒等面の元零上辺。
方針：同じ元長方形の共有右辺と元恒等提示の上辺を回収する。
規約：元全外周を保持。使われ方：絶対上辺の全区間照合。 -/
lemma dgOdotMilnorOuterRawSquare_top :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (L).rawOuterSquare =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (fromZeroCategory (Q))).edge := by
  rw [PerfectLaxQuotient.rawOuterSquare, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_top, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_outer_rightEdge,
    (L).rawRectangle.right_eq, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_right]
  exact (perfectIdentityLaxRawSquare_edges (Q) (hQ)).2.1

/-- 概要：元絶対 LT 外周の下辺は元の同じ包含。
方針：元提示の包含辺を同じ完備包含で検出する。
規約：元包含を保持。使われ方：外周第一側面の終端。 -/
lemma dgOdotMilnorOuterAbsoluteSquare_inclusion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (dgOdotMilnorActualOuterDiagram R d h).square =
      SSet.yonedaEquiv.symm (perfectStableArrow (dgOdotMilnorLaxInclusion R d) (hA) (hL)).edge := by
  apply (cancel_mono perfectStableInfinityInclusion).mp
  exact (Category.assoc _ _ _).trans
    ((dgOdotMilnorActualOuterDiagram R d h).bottom_edge.trans (perfectStableArrow_inclusion _ _ _).symm)

/-- 概要：元絶対 LT 外周の右辺は元の同じ完備化後射影。
方針：元提示の商辺を同じ完備包含で検出する。
規約：元実 c を保持。使われ方：外周第二側面の終端。 -/
lemma dgOdotMilnorOuterAbsoluteSquare_projection :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (dgOdotMilnorActualOuterDiagram R d h).square =
      SSet.yonedaEquiv.symm (perfectStableArrow (dgOdotMilnorOuterCompletedProjection R d h)
        (hL) (hQ)).edge := by
  apply (cancel_mono perfectStableInfinityInclusion).mp
  exact (Category.assoc _ _ _).trans
    ((dgOdotMilnorActualOuterDiagram R d h).right_edge.trans (perfectStableArrow_inclusion _ _ _).symm)

/-- 概要：元絶対 LT 外周の左辺は元始域から標準零圏への同じ完全射。
方針：元 raw 外周の左辺を同じ完備包含で検出する。
規約：元始域を保持。使われ方：外周零左側面の終端。 -/
lemma dgOdotMilnorOuterAbsoluteSquare_left :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (dgOdotMilnorActualOuterDiagram R d h).square =
      SSet.yonedaEquiv.symm (perfectStableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (A))
        (hA) perfectZeroCategory_isIdempotentComplete).edge := by
  apply (cancel_mono perfectStableInfinityInclusion).mp
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (L).outerSquare) ≫ _ = _
  rw [Category.assoc, PerfectLaxQuotient.outerSquare_inclusion]
  exact (L).rawOuterSquare_left.trans (perfectStableArrow_inclusion _ _ _).symm

/-- 概要：元絶対 LT 外周の上辺は標準零圏から元終域への同じ完全射。
方針：元 raw 外周の右面回収と同じ完備包含を使う。
規約：元完備化先を保持。使われ方：外周零上側面の終端。 -/
lemma dgOdotMilnorOuterAbsoluteSquare_top :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (dgOdotMilnorActualOuterDiagram R d h).square =
      SSet.yonedaEquiv.symm (perfectStableArrow (fromZeroCategory (Q))
        perfectZeroCategory_isIdempotentComplete (hQ)).edge := by
  apply (cancel_mono perfectStableInfinityInclusion).mp
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (L).outerSquare) ≫ _ = _
  rw [Category.assoc, PerfectLaxQuotient.outerSquare_inclusion]
  exact (dgOdotMilnorOuterRawSquare_top R d h).trans (perfectStableArrow_inclusion _ _ _).symm
end SerrePositivity.KST.SConstruction
