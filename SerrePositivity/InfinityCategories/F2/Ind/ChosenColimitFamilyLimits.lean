module

public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitParameterApex
public import SerrePositivity.InfinityCategories.HomotopyLimits.FunctorColimitEvaluation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointwiseColimitChoiceTransport

/-!
概要：選んだ余極限関手の全パラメータ余錐を、元の錐族の交換述語へ接続する。
方針：点ごとの余極限判定、変数交換の評価、選択余錐の厳密な頂点式を使う。
規約：元の錐と同じ選択した余極限関手を保持する。
使われ方：I-2 d′ の交換述語と有限極限保存の相互移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open Presentable HomotopyLimits

/-- 元の選択した全パラメータ余錐は、各評価でも余極限。 -/
lemma chosenColimitParameterCocone_pointwise {B A X : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : B ⟶ X, HasColimit p) (U : A ⟶ (ihom B).obj X) :
    IsPointwiseColimitCone (chosenColimitParameterCocone hX U) := by
  intro a
  exact isColimitCone_functor_evaluation_of_pointwise_exists
    (chosenColimitParameterCocone hX U) (chosenColimitParameterCocone_isColimit hX U)
    (fun k ↦ hX _) a

/-- 変数交換した元の全錐族の段階は、同じ関手圏の全錐の評価である。 -/
lemma functorVertexCone_flip_isLimit_iff {B K X : SSet.{u}}
    {p : K ⟶ (ihom B).obj X} (c : JoinCone p) (b : B _⦋0⦌) :
    IsLimitCone (functorVertexCone ((internalHomFlipHomEquiv _ _ _ c.val).app
      (Opposite.op ⦋0⦌) b)) ↔ IsLimitCone (evaluateFunctorCone c b) := by
  rw [internalHomFlipHomEquiv_app_zero]
  apply isLimitCone_iff_of_cone_val_eq
  exact (functorVertexEquiv _ _).symm_apply_apply _

/-- 選択した全余錐の完成頂点の全錐は、元の余極限関手による像の錐と同じ。 -/
lemma chosenColimitParameterCompletedLimit_iff {B K X : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : B ⟶ X, HasColimit p) {p : K ⟶ (ihom B).obj X} (c : JoinCone p) :
    IsLimitCone (functorVertexCone (chosenColimitParameterCocone hX c.val).vertex) ↔
      IsLimitCone (mapJoinCone (chosenColimitFunctor B X hX) c) := by
  rw [chosenColimitParameterCocone_vertex]
  apply isLimitCone_iff_of_cone_val_eq
  exact (functorVertexEquiv _ _).symm_apply_apply _

end SerrePositivity.InfinityCategories.F2.Ind
