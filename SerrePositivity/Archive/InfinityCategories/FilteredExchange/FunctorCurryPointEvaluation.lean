module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorCurryPointVertex

/-!
概要：元の全関手族の一点評価を、元の同じ実係数制限の射へ戻す。
方針：元の一点頂点の式に、同じ関手頂点の同値の逆を適用する。
規約：元の射と指定点を保持。使われ方：普遍区間比較の実両端の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の curry の一点評価は、元の指定点で制限した同じ実射。 -/
lemma functorCurry_point_evaluation {A C X : SSet.{u}} (f : A ⊗ C ⟶ X) (l : C _⦋0⦌) :
    (functorVertexEquiv A X).symm ((curry f).app (Opposite.op ⦋0⦌) l) =
      lift (𝟙 A) (SSet.const l) ≫ f := by
  rw [functorCurry_point_vertex]
  exact (functorVertexEquiv A X).symm_apply_apply _

/-- 全作用の同じ射の等式は、元の実係数制限と同じ一点評価を一致させる。 -/
lemma functorCurry_point_evaluation_of_map_eq {A C X : SSet.{u}}
    (f : A ⊗ C ⟶ X) (g : C ⟶ (ihom A).obj X) (h : curry f = g) (l : C _⦋0⦌) :
    lift (𝟙 A) (SSet.const l) ≫ f = (functorVertexEquiv A X).symm (g.app (Opposite.op ⦋0⦌) l) := by
  rw [← functorCurry_point_evaluation f l, h]

end SerrePositivity.InfinityCategories.F2
