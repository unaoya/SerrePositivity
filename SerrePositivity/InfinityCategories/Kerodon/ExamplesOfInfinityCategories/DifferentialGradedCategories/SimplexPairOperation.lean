module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexPairEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IntegerTensorBifunctor

/-!
# 普遍鎖が定める二変数のテンソル作用素

概要：普遍模型の各鎖を、二つの N 単体のテンソルからの実線形写像として評価する。
方針：単体射の対を二つの制限のテンソルへ送り、鎖の係数について線形に拡張する。
規約：KST Construction A.5、非被約で全ての次数を許す。
使われ方：再帰で構成した普遍鎖を比較ホモトピーの実成分にする。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite
open scoped Simplicial
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- 概要：普遍模型の鎖を二変数のテンソル作用素へ送る整数線形写像。
方針：単体射の対を制限のテンソルへ送る自由加群の lift。
規約：KST A.5、入力の二つの群の可換性を要求しない。
使われ方：普遍充填からホモトピーの実線形成分を得る。 -/
def simplexPairOperation {N : ℕ} (r : SimplexCategoryᵒᵖ) :
    (linearizedSpace (simplexPairModel.{u} N)).obj r →ₗ[ℤ]
      (integerTensor (C.obj (op ⦋N⦌)) (D.obj (op ⦋N⦌)) ⟶
        (simplicialIntegerTensor C D).obj r) :=
  Finsupp.lift _ ℤ _ (fun z ↦ integerTensorMap (C.map z.down.1.op) (D.map z.down.2.op))

/-- 概要：普遍鎖の作用素を基底へ評価すると対応する二つの制限のテンソル。
方針：自由加群の lift の単項評価。
規約：KST A.5。使われ方：作用素の全ての自然性の基底上の検証。 -/
@[simp] lemma simplexPairOperation_generator {N : ℕ} (r : SimplexCategoryᵒᵖ)
    (z : (simplexPairModel.{u} N).obj r) :
    simplexPairOperation C D r (integerGenerator z) =
      integerTensorMap (C.map z.down.1.op) (D.map z.down.2.op) := by
  dsimp [simplexPairOperation, integerGenerator]
  erw [Finsupp.lift_apply, Finsupp.sum_single_index]
  · exact one_smul ℤ _
  · exact zero_smul ℤ _

/-- 概要：普遍鎖の作用素は固定した二つの単体への評価に一致。
方針：鎖の整数線形性により基底の場合へ帰着する。
規約：KST A.5。使われ方：普遍模型の鎖写像による評価との接続。 -/
lemma simplexPairOperation_tmul {N : ℕ} (r : SimplexCategoryᵒᵖ)
    (z : (linearizedSpace (simplexPairModel.{u} N)).obj r)
    (x : C.obj (op ⦋N⦌)) (y : D.obj (op ⦋N⦌)) :
    simplexPairOperation C D r z (TensorProduct.tmul ℤ x y) =
      simplexPairEvaluationApp C D x y r z := by
  induction z using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero]
    rfl
  | add a b ha hb =>
    simp only [map_add]
    change (simplexPairOperation C D r a) (TensorProduct.tmul ℤ x y) +
      (simplexPairOperation C D r b) (TensorProduct.tmul ℤ x y) = _
    rw [ha, hb]
  | single w a =>
    have hw : Finsupp.single w a = a • integerGenerator w := by
      exact (Finsupp.smul_single_one w a).symm
    rw [hw]
    simp only [map_smul, simplexPairOperation_generator, simplexPairEvaluationApp_generator]
    rfl

/-- 概要：普遍鎖の作用素は単体構造の写像と可換。
方針：純テンソルに評価し、既に構成した単体的評価射の自然性を使う。
規約：KST A.5。使われ方：普遍サイクルの微分を実作用素へ移す。 -/
lemma simplexPairOperation_naturality {N : ℕ}
    {r s : SimplexCategoryᵒᵖ} (f : r ⟶ s)
    (z : (linearizedSpace (simplexPairModel.{u} N)).obj r) :
    simplexPairOperation C D s ((linearizedSpace (simplexPairModel N)).map f z) =
      simplexPairOperation C D r z ≫ (simplicialIntegerTensor C D).map f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  refine TensorProduct.inductionOn t (fun x y ↦ ?_) (fun a b ha hb ↦ ?_)
  ·
    change simplexPairOperation C D s _ (TensorProduct.tmul ℤ x y) =
      (simplicialIntegerTensor C D).map f
        (simplexPairOperation C D r z (TensorProduct.tmul ℤ x y))
    rw [simplexPairOperation_tmul, simplexPairOperation_tmul]
    exact congrArg (fun k ↦ k z) (simplexPairEvaluation_naturality C D x y f)
  · simp only [map_add, ha, hb]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
