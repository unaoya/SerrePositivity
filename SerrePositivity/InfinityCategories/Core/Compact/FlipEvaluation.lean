module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.InternalHomFlipAdjunction
public import SerrePositivity.InfinityCategories.Core.InternalHomFlipVertices

/-!
概要：全二変数族の転置後の各評価関手を、元の同じ関手頂点として厳密に回収する。
方針：二重転置の往復と既存の頂点公式を使う。
規約：元の族・評価点を保持。使われ方：全 Hom 錐族の頂点と各生成点の読み戻し。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 転置後の指定点での全評価は、元の同じ関手頂点を回収する。 -/
lemma flipFamily_evaluate_vertex {A B X : SSet.{u}} (F : A ⟶ (ihom B).obj X)
    (a : A _⦋0⦌) :
    functorVertex (internalHomFlipHomEquiv A B X F ≫ evaluateFunctorAt a) =
      F.app (Opposite.op ⦋0⦌) a := by
  have h := internalHomFlipHomEquiv_app_zero (internalHomFlipHomEquiv A B X F) a
  have hF : internalHomFlipHomEquiv B A X (internalHomFlipHomEquiv A B X F) = F :=
    (internalHomFlipHomEquiv A B X).left_inv F
  rw [hF] at h
  exact h.symm

end SerrePositivity.InfinityCategories.F2.Compact
