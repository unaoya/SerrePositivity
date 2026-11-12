module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedTriangleDiagramSource
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorCurryHom

/-!
概要：相対 curry の豊穣作用の値側の点評価を、元の全族の同じ点への制限へ戻す。
方針：二段階の curry を展開し、結合子と指定点を挿入する射を照合する。
規約：全次数・全係数の厳密な等式。使われ方：切断の終点評価と prism 終点評価の交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 相対 curry の値を元の指定点で評価すると、元の族の同じ点での制限を回収する。 -/
lemma relativeFunctorCurryHom_evaluate_ι {K A E B : SSet.{u}} (p : E ⟶ B) (d : K ⟶ B)
    (k : K _⦋0⦌) :
    uncurry (relativeFunctorCurryHom p d A) ≫ relativeFunctorEvaluate p d k ≫
      vertexFiberι p (d.app (Opposite.op ⦋0⦌) k) =
      (lift (SSet.const k) (𝟙 A) ▷ relativeFunctorSpace p (fst K A ≫ d)) ≫
        relativeFunctorUncurry (𝟙 (relativeFunctorSpace p (fst K A ≫ d))) := by
  unfold relativeFunctorCurryHom
  rw [uncurry_curry, relativeCurry_evaluate_ι]
  rfl

end SerrePositivity.InfinityCategories.F2
