module
public import SerrePositivity.KST.NonConnective.DGKappaSplitRelations
public import SerrePositivity.KST.NonConnective.DGKappaSplitPerfSquareCoordinates

/-!
概要：元の実分裂の四合成と恒等分解を、同じ各 Perf ラベルで保持する。
方針：元の全次数 dg ラベル作用の閉関手で、同じ分裂等式を写す。
規約：元の閉注入・射影を保持し、cofiber の普遍性は別途証明する。
使われ方：実分裂零三角形の点ごとの cofiber 性の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (X : PresentedPerfectDGObject R (DGKappaCone R D I))

/-- 同じ Perf ラベルでの全入力作用の閉関手。 -/
abbrev dgKappaPerfLabelFunctor :=
  (presentedPerfectDGLabelAction R (DGKappaCone R D I) (DGKappaCone R D I) X).onClosed

/-- 同じ Perf ラベルで、左注入と左射影の分裂を保持する。 -/
theorem dgKappaSplitPerf_head_head :
    (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplitHead R D I) ≫
        (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplitHeadProjection R D I) = 𝟙 _ := by
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
    congrArg (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplit_head_head R D I)

/-- 同じ Perf ラベルで、右注入と左射影の交差合成は零。 -/
theorem dgKappaSplitPerf_tail_head :
    (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplitTail R D I) ≫
        (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplitHeadProjection R D I) = 0 := by
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] using
    congrArg (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplit_tail_head R D I)

/-- 同じ Perf ラベルで、左注入と右射影の交差合成は零。 -/
theorem dgKappaSplitPerf_head_tail :
    (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplitHead R D I) ≫
        (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplitTailProjection R D I) = 0 := by
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] using
    congrArg (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplit_head_tail R D I)

/-- 同じ Perf ラベルで、右注入と右射影の分裂を保持する。 -/
theorem dgKappaSplitPerf_tail_tail :
    (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplitTail R D I) ≫
        (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplitTailProjection R D I) = 𝟙 _ := by
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
    congrArg (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplit_tail_tail R D I)

/-- 同じ Perf ラベルで、元の二項直和の恒等分解を保持する。 -/
theorem dgKappaSplitPerf_decomposition :
    (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplitHeadProjection R D I) ≫
        (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplitHead R D I) +
      (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplitTailProjection R D I) ≫
        (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplitTail R D I) = 𝟙 _ := by
  simpa only [CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_id] using
      congrArg (dgKappaPerfLabelFunctor R D I X).map (dgKappaSplit_decomposition R D I)

end SerrePositivity.KST.NonConnective
