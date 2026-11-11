module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ArrowPullbackDiagonal
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionPullbackComparisonFamily

/-!
概要：実比較正方形の対角辺を保ったまま、同じ cospan の普遍錐を構成する。
方針：端点で可逆なホモトピーによる矢印圏の同値と、厳密な錐の輸送を使う。
規約：一般安定性を仮定しない。使われ方：切除判定の第二条件と実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma exists_excisionArrowPullbackSquare_diagonal {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] {F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c))))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionPullbackComparisonFamily c d hd)))
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone e) :
    ∃ R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan R = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionPullbackComparisonFamily c d hd) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare R ∧ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagonalArrow (uncurry (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparisonEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionPullbackComparisonFamily c d hd)
            e he).edge))).edge) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_arrowPullbackSquare_diagonal _ e he
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionPullbackComparisonFamily_source_isPullback c hc d hd)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
