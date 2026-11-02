module

public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitParameterCocone
public import SerrePositivity.InfinityCategories.Core.CatInfinity.CoconeValEquality
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorCoconeEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.FlippedConeEvaluation

/-!
概要：選んだ全余錐族の変数交換は点ごとにも元の余極限余錐である。
方針：交換後の評価を元の族の指定頂点の全余錐へ戻す。
規約：全余錐の射を厳密に比較する。
使われ方：有限余積の比較の各点での普遍性。
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

/-- 概要：選んだパラメータ余錐は各点でも元の指定余極限を与える。
方針：全余錐の評価を選んだ一つの余錐そのものへ戻す。
規約：パラメータの充填性は不要。
使われ方：全余錐比較の可逆性の各点判定。 -/
lemma chosenColimitParameterCocone_isPointwiseColimit {K A X : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : K ⟶ X, HasColimit p) (U : A ⟶ (ihom K).obj X) :
    IsPointwiseColimitCone (chosenColimitParameterCocone hX U) := by
  intro a
  let p := (functorVertexEquiv K X).symm (U.app (Opposite.op ⦋0⦌) a)
  have hp : functorVertex p = U.app (Opposite.op ⦋0⦌) a :=
    (functorVertexEquiv K X).apply_symm_apply _
  have hv : (evaluateFunctorCocone (chosenColimitParameterCocone hX U) a).val =
      (chosenColimitCocone K X hX p).val := by
    change internalHomFlipHomEquiv A (join K Δ[0]) X
      (U ≫ chosenColimitCoconeFamily K X hX) ≫ evaluateFunctorAt a = _
    rw [flippedDiagram_evaluation]
    change (functorVertexEquiv (join K Δ[0]) X).symm
      ((chosenColimitCoconeFamily K X hX).app _ (U.app _ a)) =
      (functorVertexEquiv (join K Δ[0]) X).symm
        ((chosenColimitCoconeFamily K X hX).app _ (functorVertex p))
    rw [hp]
  exact (isColimitCone_iff_of_cocone_val_eq _ _ hv).mpr
    (chosenColimitCocone_isColimit K X hX p)

end SerrePositivity.InfinityCategories.F2.Presentable
