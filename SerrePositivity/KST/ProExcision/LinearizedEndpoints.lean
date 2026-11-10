module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedHomotopy

/-!
# 線形化した区間の端点の基底公式

概要：C(X)⊗ℤΔ¹ の端点包含を自由加群の基底で計算する。
方針：積の自由化とテンソルの同型の逆を評価する。
規約：KST Definition A.3、非被約な両端。零次を含む。
使われ方：Lemma A.4 の bar に持ち上げた m 次ホモトピーの両端条件。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
open scoped Simplicial

/-- 概要：積の基底をテンソル同型の逆で送ると二つの基底の純テンソルになる。
方針：有限台関数の同型の逆の公式を使う。
規約：KST Definition A.3。使われ方：自由化した端点包含の計算。 -/
@[simp] lemma integerTensorIso_inv_generator (X Y : Type u) (x : X) (y : Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorIso X Y).inv (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (x, y)) =
      TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator y) := by
  change (finsuppTensorFinsupp' ℤ X Y).symm (Finsupp.single (x, y) 1) = _
  rw [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

/-- 概要：零端点は基底を零頂点の定数単体との純テンソルへ送る。
方針：幾何的端点の自由化とテンソル同型の逆を計算する。
規約：KST Definition A.3。使われ方：bar の m 次ホモトピーの始点条件。 -/
@[simp] lemma linearizedEndpoint₀_generator (X : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (x : X.obj n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀ X).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) =
      TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.const 1 0 n)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorIso (X.obj n) ((Δ[1] : SSet.{u}).obj n)).inv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (SSet.ι₀.app n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
  have hx : SSet.ι₀.app n x = (x, SSet.stdSimplex.const 1 0 n) := by rfl
  rw [hx, integerTensorIso_inv_generator]

/-- 概要：一端点は基底を一頂点の定数単体との純テンソルへ送る。
方針：幾何的端点の自由化とテンソル同型の逆を計算する。
規約：KST Definition A.3。使われ方：bar の m 次ホモトピーの終点条件。 -/
@[simp] lemma linearizedEndpoint₁_generator (X : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (x : X.obj n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁ X).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) =
      TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.const 1 1 n)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorIso (X.obj n) ((Δ[1] : SSet.{u}).obj n)).inv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (SSet.ι₁.app n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
  have hx : SSet.ι₁.app n x = (x, SSet.stdSimplex.const 1 1 n) := by rfl
  rw [hx, integerTensorIso_inv_generator]

end SerrePositivity.KST.ProExcision
