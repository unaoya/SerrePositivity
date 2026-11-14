module
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SquareFamilyReading

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.YonedaSquarePreservation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.YonedaCoconeFamily
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteCospanInclusion
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SpanSquareUniverseReading
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Bicartesian

/-!
概要：C の同じ span 全余極限余錐族を、Ind の実 bicartesian 四角形族へ移す。
方針：元の全余錐の宇宙整合性で各値を回収し、C の安定性をその四角形へ適用する。
規約：全パラメーターと元の C 全余錐を固定し、交換入力は明示する。
使われ方：I-2 c の単一 filtered 表示の同じ各段の両普遍性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 同じ C の span 全余錐族を元の Ind Yoneda の全四角形族へ移す。 -/
def indYonedaSpanSquareFamily (κ : Cardinal.{u}) {A C : SSet.{u}} [Quasicategory C]
    (l : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (horn 2 0) (Δ[0] : SSet.{u}))).obj C) :
    (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYonedaCoconeFamily κ l ≫
    (pre (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.uliftSpanSquareReadingIso.{u, u + 1}).inv).app (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)

/-- 全四角形族の各値は、元の同じ C 全余錐の実四角形の Yoneda 像。 -/
lemma indYonedaSpanSquareFamily_vertex (κ : Cardinal.{u}) {A C : SSet.{u}}
    [Quasicategory C] (l : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (horn 2 0) (Δ[0] : SSet.{u}))).obj C)
    (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexSquare ((indYonedaSpanSquareFamily κ l).app
      (Opposite.op ⦋0⦌) (ULift.up a)) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt l a)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm
    (((pre (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.uliftSpanSquareReadingIso.{u, u + 1}).inv).app (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYonedaCoconeFamily κ l).app _ (ULift.up a))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexMap_precomp]
  change (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.uliftSpanSquareReadingIso.{u, u + 1}).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.functorVertexCocone ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYonedaCoconeFamily κ l).app _ (ULift.up a))).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYonedaCoconeFamily_vertex_val]
  change (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.uliftSpanSquareReadingIso.{u, u + 1}).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt l a)).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.uliftCoconeSquareReading]

/-- 同じ各段の実四角形は、包含後の引き戻しであり Ind 内の押し出しでもある。 -/
lemma indYonedaSpanSquareFamily_bicartesian (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndFiniteLimitExchangeInput.{u})
    {A C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits C]
    (l : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (horn 2 0) (Δ[0] : SSet.{u}))).obj C)
    (hl : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt l a)) (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexSquare ((indYonedaSpanSquareFamily κ l).app
      (Opposite.op ⦋0⦌) (ULift.up a)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C) ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexSquare ((indYonedaSpanSquareFamily κ l).app
      (Opposite.op ⦋0⦌) (ULift.up a))) := by
  rw [indYonedaSpanSquareFamily_vertex]
  have hp := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_isPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt l a) (hl a)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_inclusion_preservesPullbackSquare κ hκ hex _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_preservesPullbackSquare κ _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout_square _ hp)),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_preservesPushoutSquare κ hκ hex _ hp⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
