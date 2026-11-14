module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.ULiftRelativeLocalization
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueRelative
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePostcompose
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueTransport

/-!
# 元の Hom の ULift の局所化同値と全語の評価

概要：同じ homEquiv は元の全 zigzag の局所化値を保つ。
方針：元の down・厳密な因子化・全語の評価の合成則を使う。
規約：元の両端の等式移送と元の通常の局所化を保持する。
使われ方：実 DK/Map^h 比較の既存 π₀ 同値への照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open CategoryTheory

lemma homEquiv_value {C : Type u} [Category.{v} C] (W : MorphismProperty C)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : ULiftHom.{w} C)
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.liftedWeakEquivalences W) a X Y) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.homEquiv W X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.liftedWeakEquivalences W).Q
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.liftedWeakEquivalences W).Q_inverts S) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value W.Q W.Q_inverts (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.down W) S) := by
  change eqToHom (Functor.congr_obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.down W)) X).symm ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.down W)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.liftedWeakEquivalences W).Q
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.liftedWeakEquivalences W).Q_inverts S) ≫
    eqToHom (Functor.congr_obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.down W)) Y) = _
  apply eq_of_heq
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact ((heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_relative (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.down W) W.Q W.Q_inverts S)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_functor_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.down W)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.relativeInverts (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.down W) W.Q W.Q_inverts)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postInverts (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.liftedWeakEquivalences W).Q
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.liftedWeakEquivalences W).Q_inverts (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.down W))) S).trans
      (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_postcompose (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.liftedWeakEquivalences W).Q
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.liftedWeakEquivalences W).Q_inverts (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.down W)) S)))).symm
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
