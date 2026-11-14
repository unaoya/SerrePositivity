module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StablePushoutExistence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FiniteLimitGeneration
/-!
概要：IsStable の定義だけから、任意の pushout・pullback と全有限極限・余極限を導く。
方針：fiber/cofiber の貼り合わせによる span の存在を双対化し、有限形状の生成判定へ渡す。
規約：quasicategory 性と IsStable 以外の存在仮定を追加せず、全図式を元の宇宙に保持する。
使われ方：D-7′。Ind_κ(C) の有限極限・余極限と安定性への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

lemma IsStable.hasLimit_cospan {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (p : (horn 2 2 : SSet.{u}) ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasLimit_iff_hasColimit_op p).mpr
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasColimit_iff_restrict_of_isIso (SSet.opFunctor.map p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso 2 2).hom).mpr
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.hasColimit_span _

lemma IsStable.exists_pushoutSquare {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) :
    ∃ R : Δ[1] ⊗ Δ[1] ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R = p ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R := by
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.hasColimit_span p
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare c, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_span c, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_isPushout c hc⟩

lemma IsStable.exists_pullbackSquare {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (p : (horn 2 2 : SSet.{u}) ⟶ X) :
    ∃ R : Δ[1] ⊗ Δ[1] ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan R = p ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare R := by
  obtain ⟨c, hc⟩ := IsStable.hasLimit_cospan p
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare c, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_cospan c, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_isPullback c hc⟩

theorem hasFiniteColimits_of_isStable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.hasFiniteColimits_of_initial_pushouts (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X).vertex
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X).isInitial _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.hasColimit_span

theorem hasFiniteLimits_of_isStable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hasFiniteLimits_of_terminal_pullbacks (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X).vertex
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X).isTerminal IsStable.hasLimit_cospan

theorem hasFiniteLimitsColimits_of_isStable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X :=
  ⟨hasFiniteLimits_of_isStable X, hasFiniteColimits_of_isStable X⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BGT "Def 2.12"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimitsColimits_of_isStable
attribute [cite HA "1.1.3.4"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimitsColimits_of_isStable
attribute [cite HA "1.1.3.5" (partial := component) "仮定：安定準圏と二対象（HA と一致）。結論：有限積・余積の存在と、零始点の押し出しから hX の双積を作る。∞ 圏の正方形自体から余積→積の標準同値を比較する宣言は採用した型にない（Lean が弱い）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimitsColimits_of_isStable
attribute [cite HA "6.1.1.7" (partial := component) "仮定：安定な準圏 C（HA と一致）。結論：C は全有限形状の極限を持つ（明記された条件(a)の自動成立に一致）。順序余極限と可算余積の存在の同値、条件(c)の自動成立は含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_of_isStable
