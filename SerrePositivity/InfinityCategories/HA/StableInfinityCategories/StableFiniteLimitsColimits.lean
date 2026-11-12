module
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
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.hasFiniteColimits_of_initial_pushouts (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).vertex
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).isInitial _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.hasColimit_span

theorem hasFiniteLimits_of_isStable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hasFiniteLimits_of_terminal_pullbacks (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).vertex
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).isTerminal IsStable.hasLimit_cospan

theorem hasFiniteLimitsColimits_of_isStable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X :=
  ⟨hasFiniteLimits_of_isStable X, hasFiniteColimits_of_isStable X⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
