module
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareTranspose
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare

/-! # 転置と同じ二枝を持つ span

概要：四角形の転置は span の二枝交換に対応し、同じ辺を二枝に使う span は交換で変わらない。
方針：余錐形状と正方形の同型の交換則、および span の二枝への制限を使う。
規約：値域の quasicategory 性は不要。使われ方：対称な suspension 模型の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：span の二枝交換と正方形の転置は境界包含を通じて可換。
方針：join の左包含で余錐形状の交換則を制限する。
規約：形状だけの等号。使われ方：転置した四角形の span の計算。 -/
lemma spanSquareBoundary_swap :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary
  have h := congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (horn 2 0 : SSet.{u}) Δ[0] ≫ t)
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanCoconeSquareIso_swap
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap] at h
  simpa only [Category.comp_id, Category.assoc] using h

/-- 概要：転置した四角形の入力 span は元の span の二枝交換。
方針：境界包含と二枝交換の可換性を後合成する。
規約：任意の単体的四角形。使われ方：対称な二枝の suspension の span の等号。 -/
lemma pushoutSpan_transpose {X : SSet.{u}} (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ R) = _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan
  rw [← Category.assoc, ← spanSquareBoundary_swap, Category.assoc]

/-- 概要：同じ辺を二枝に使う span は二枝交換で不変。
方針：二枝への制限を取り、交換則と辺の span の両制限を使う。
規約：辺の始点と終点は任意。使われ方：同じ零射を二度使う suspension 模型。 -/
lemma edgeSpan_self_swap {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f := by
  apply horn₂₀.isPushout.hom_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap_left, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_right, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_left]
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap_right, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_left, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_right]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
