module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopEquivalenceCofiberExists
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpecifiedCofiberSpan

/-!
概要：実 loop 同値から指定した零枝を持つ全 span の余極限を得る。
方針：構成済みの全 cofiber の span と、元の入力 span を全関手同型で比較する。
規約：有限余極限や一般安定性は入力しない。
使われ方：関手圏の cofiber 四角形の点ごとの評価。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：第二枝が指定終対象へ向かう元の span は余極限を持つ。
方針：第一枝の実 cofiber を選び、同じ第一枝と終対象への第二枝を比較する。
規約：第二枝を任意の零射へ置き換えない。
使われ方：全パラメーターの評価における cofiber の存在。 -/
lemma hasColimit_span_of_terminal_second_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
    (p : (horn 2 0 : SSet.{u}) ⟶ X)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((horn₂₀.ι₀₂ ≫ p).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ p))
  obtain ⟨t⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSquare_nonempty_of_loopEquivalence s hs hΩ e
  have hfirst : horn₂₀.ι₀₁ ≫ p = horn₂₀.ι₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan t.square := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge, t.bottom_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply _).symm
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan t.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
    exact t.zero_corner.2
  obtain ⟨i⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nonempty_functorIso_span_of_first_eq_terminal_second
    p (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan t.square) hfirst hz ht
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_of_functorIso i).mpr ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone t.square, t.isPushout⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
