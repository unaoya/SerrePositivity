module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.RelativeInputPostcomp

/-!
概要：追加入力を保つ比較が元の基底 filtered 表示を保つことを示す。
方針：制限で基底全余錐を保ち、元の脚の filtered 保存性を適用する。
規約：元の入力 coslice の全小余極限は要求しない。
使われ方：相対交互塔へ渡す共通入力付きの成分表示。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：元の基底で余極限の filtered 表示は追加入力を忘れて後合成しても基底で余極限。
方針：元の制限の全基底値の等式と脚の filtered 保存性を合成する。
規約：追加入力の単射性は保存性の判定に不要。
使われ方：異なる入力を持つ元の成分表示から共通入力の交互塔を作る。 -/
lemma relativeInputPostcomp_base_isColimitCone
    {μ : Cardinal.{u}} {K L C B : SSet.{u + 1}} [Quasicategory C] [Quasicategory B]
    (a : K ⟶ C) (i : L ⟶ K) (a₀ : L ⟶ C) (hi : i ≫ a = a₀)
    (z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone a) (z₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone a₀)
    (hzi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0]) ≫ z.val = z₀.val)
    (p : C ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ p)
    (r : L ⟶ B) (hpr : a₀ ≫ p = r) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r) (hzt : z₀.val ≫ p = t.val)
    {I : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I]
    (P : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)).symm z))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone P))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection r) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone
      (P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.relativeInputPostcomp a i a₀ hi z z₀ hzi p r hpr t hzt))) := by
  have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputRestriction_base_isColimitCone a i a₀ hi z z₀ hzi P hc
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputPostcomp_base_isColimitCone a₀ p hp r hpr z₀ t hzt
    (P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputRestriction a i a₀ hi z z₀ hzi) hR

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
