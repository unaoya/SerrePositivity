module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pasting
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareOpposite

/-! # 引き戻し四角形の貼り合わせ

概要：右が引き戻しなら、左が引き戻しであることと外側が引き戻しであることは同値。
方針：長方形と値域を反転し、join・slice で証明した押し出しの貼り合わせを適用する。
規約：HTT Lemma 4.4.2.1。安定性を仮定しない。
使われ方：S4 の fiber 列の貼り合わせと八面体。

対応節は Kerodon 7.6（Tag 03E8）。
-/
@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits

/-- 概要：右が引き戻しなら左と外側の引き戻し性は同値。
方針：面を反転して押し出しの貼り合わせの同値へ帰着する。
規約：値域は quasicategory、面二が左、零が右、一が外側。
使われ方：HTT Lemma 4.4.2.1 と fiber の合成。 -/
lemma isPullbackSquare_pasting_iff {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hright : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) := by
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F) 2) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_pastingSquare]
    exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_reverseGrid (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0)).mp hright
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_pasting_iff (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid F) hl
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_pastingSquare, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid_pastingSquare] at h
  exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_reverseGrid (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2)).trans
    (h.trans (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_reverseGrid (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1)).symm)

/-- 概要：隣り合う二つの引き戻し四角形の外側は引き戻し。
方針：右を固定した左と外側の判定の順方向を使う。
規約：実際の単体的な長方形を指定。使われ方：fiber 列の貼り合わせ。 -/
lemma isPullbackSquare_pasting {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2))
    (hright : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) :=
  (isPullbackSquare_pasting_iff F hright).mp hleft

/-- 概要：右と外側が引き戻しなら左四角形も引き戻し。
方針：右を固定した同値判定の逆方向を使う。
規約：値域は quasicategory。使われ方：八面体に現れる fiber の判定。 -/
lemma isPullbackSquare_pasting_cancel_right {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hright : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0))
    (houter : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) :=
  (isPullbackSquare_pasting_iff F hright).mpr houter

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
