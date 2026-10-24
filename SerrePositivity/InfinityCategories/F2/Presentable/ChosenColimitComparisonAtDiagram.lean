module

public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitEvaluation

/-!
概要：指定図式の選んだ余錐像が普遍なら、同じ全余極限比較の指定成分は可逆。
方針：全余錐族の像を指定図式の元の余錐像へ厳密に照合する。
規約：比較の射を選び直さない。
使われ方：Yoneda 像からなる有限図式の比較の可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：指定図式の選んだ普遍余錐の像で全比較の元の成分を検査できる。
方針：同じ全余錐族の評価を選んだ指定余錐そのものへ戻す。
規約：元の指定図式を保つ。
使われ方：Yoneda 制限上の有限余積条件の適用。 -/
lemma chosenColimitComparison_isIso_at_diagram
    {K X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (hX : ∀ p : K ⟶ X, HasColimit p) (hY : ∀ p : K ⟶ Y, HasColimit p)
    (q : X ⟶ Y) (p : K ⟶ X)
    (h : IsColimitCone (mapJoinCocone q (chosenColimitCocone K X hX p))) :
    IsIso (functorHomEvaluate (chosenColimitComparison hX hY q) (functorVertex p)) := by
  apply chosenColimitComparison_evaluate_isIso hX hY q (functorVertex p)
  have hv : (evaluateFunctorCocone
      (chosenColimitImageCocone hX (𝟙 ((ihom K).obj X)) q) (functorVertex p)).val =
      (mapJoinCocone q (chosenColimitCocone K X hX p)).val := by
    rw [chosenColimitImageCocone_evaluate_val]
    change (evaluateFunctorCocone (chosenColimitParameterCocone hX (𝟙 ((ihom K).obj X)))
      (functorVertex p)).val ≫ q = (chosenColimitCocone K X hX p).val ≫ q
    rw [chosenColimitParameterCocone_id_evaluate_val]
  exact (isColimitCone_iff_of_cocone_val_eq _ _ hv).mpr h

end SerrePositivity.InfinityCategories.F2.Presentable
