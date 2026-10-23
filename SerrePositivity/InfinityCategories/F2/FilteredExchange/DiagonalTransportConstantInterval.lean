module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalUniversalPrism
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorCurryPointEvaluation

/-!
概要：同じ固定区間での対角普遍輸送の実終点を、元の普遍全作用の一点評価へ戻す。
方針：動く初期値を一点制限の前合成へ移し、同じ curry の一点評価を使う。
規約：初期値は任意の全係数を持つ。使われ方：元の直接比較と native 比較の終点照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の同じ固定区間の対角輸送は、同じ普遍全作用の一点評価の初期値による前合成。 -/
lemma diagonalFiberTransport_constant_interval {E B K : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (f : K ⟶ vertexFiber p a)
    (v : (intervalMappingSpace a b) _⦋0⦌) :
    diagonalFiberTransport p f (SSet.const v) = f ≫ (functorVertexEquiv _ _).symm
      ((parametrizedFiberTransport p a b).app (Opposite.op ⦋0⦌) v) := by
  unfold diagonalFiberTransport
  have hj : f ≫ lift (𝟙 (vertexFiber p a)) (SSet.const v) = lift f (SSet.const v) := by
    rw [comp_lift, Category.comp_id, SSet.comp_const]
  rw [← hj, Category.assoc, ← functorCurry_point_evaluation]
  rfl

end SerrePositivity.InfinityCategories.F2
