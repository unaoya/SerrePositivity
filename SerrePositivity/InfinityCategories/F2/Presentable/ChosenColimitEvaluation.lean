module

public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitPointwise

/-!
概要：全図式の普遍余錐族を元の指定図式で評価すると選んだ同じ余錐になる。
方針：変数交換後の評価公式を恒等図式族に適用する。
規約：元の指定図式を保持する。
使われ方：全関手比較から任意の指定余錐の保存へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：恒等図式族の普遍余錐の評価は元の指定図式の選んだ全余錐そのもの。
方針：元の全余錐族の指定頂点を回収する。
規約：全余錐の射の等式である。
使われ方：有限余積の全比較の十分条件。 -/
lemma chosenColimitParameterCocone_id_evaluate_val {K X : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : K ⟶ X, HasColimit p) (p : K ⟶ X) :
    (evaluateFunctorCocone (chosenColimitParameterCocone hX (𝟙 ((ihom K).obj X)))
      (functorVertex p)).val = (chosenColimitCocone K X hX p).val := by
  change internalHomFlipHomEquiv ((ihom K).obj X) (join K Δ[0]) X
    (chosenColimitCoconeFamily K X hX) ≫ evaluateFunctorAt (functorVertex p) = _
  rw [flippedDiagram_evaluation]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable
