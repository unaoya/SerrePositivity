module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ChosenColimitParameterApex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorColimitEvaluation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.PointwiseColimitChoiceTransport

/-!
概要：選んだ余極限関手の全パラメータ余錐を、元の錐族の交換述語へ接続する。
方針：点ごとの余極限判定、変数交換の評価、選択余錐の厳密な頂点式を使う。
規約：元の錐と同じ選択した余極限関手を保持する。
使われ方：I-2 d′ の交換述語と有限極限保存の相互移送。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories


/-- 元の選択した全パラメータ余錐は、各評価でも余極限。 -/
lemma chosenColimitParameterCocone_pointwise {B A X : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : B ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) (U : A ⟶ (ihom B).obj X) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone hX U) := by
  intro a
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.isColimitCone_functor_evaluation_of_pointwise_exists
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone hX U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone_isColimit hX U)
    (fun k ↦ hX _) a

/-- 変数交換した元の全錐族の段階は、同じ関手圏の全錐の評価である。 -/
lemma functorVertexCone_flip_isLimit_iff {B K X : SSet.{u}}
    {p : K ⟶ (ihom B).obj X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv _ _ _ c.val).app
      (Opposite.op ⦋0⦌) b)) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone c b) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply _

/-- 選択した全余錐の完成頂点の全錐は、元の余極限関手による像の錐と同じ。 -/
lemma chosenColimitParameterCompletedLimit_iff {B K X : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : B ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) {p : K ⟶ (ihom B).obj X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone hX c.val).vertex) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitFunctor B X hX) c) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone_vertex]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
