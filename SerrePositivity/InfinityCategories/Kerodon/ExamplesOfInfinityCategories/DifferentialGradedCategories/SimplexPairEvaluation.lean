module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexPairModel
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IntegerLinearizationDesc
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedTensor

/-!
# 普遍な単体の対の任意の整数加群への評価

概要：二つの N 単体を固定し、普遍模型の二つの単体射を反変に評価する。
方針：各基底の値を純テンソルで定め、整数線形に拡張する。
規約：KST Construction A.5 の標準比較。群の可換性に依存しない。
使われ方：普遍模型で充填した鎖を任意の二つの入力へ移す。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite
open scoped Simplicial
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- 概要：普遍な単体射の対を二つの固定単体へ評価する次数ごとの写像。
方針：各基底を二つの制限の純テンソルへ送り、整数線形に拡張する。
規約：KST A.5、任意の加群の宇宙で定義する。
使われ方：標準比較の普遍鎖から任意の入力への評価。 -/
def simplexPairEvaluationApp {N : ℕ} (x : C.obj (op ⦋N⦌)) (y : D.obj (op ⦋N⦌))
    (r : SimplexCategoryᵒᵖ) :
    (linearizedSpace (simplexPairModel N)).obj r ⟶ (simplicialIntegerTensor C D).obj r :=
  integerLinearizationDesc (fun z ↦
    TensorProduct.tmul ℤ (C.map z.down.1.op x) (D.map z.down.2.op y))

/-- 概要：普遍模型の評価は基底の二つの制限の純テンソルに一致。
方針：整数線形拡張を基底上で評価する。
規約：KST A.5。使われ方：評価の自然性の検証。 -/
@[simp] lemma simplexPairEvaluationApp_generator {N : ℕ}
    (x : C.obj (op ⦋N⦌)) (y : D.obj (op ⦋N⦌)) (r : SimplexCategoryᵒᵖ)
    (z : (simplexPairModel.{u} N).obj r) :
    simplexPairEvaluationApp C D x y r (integerGenerator z) =
      TensorProduct.tmul ℤ (C.map z.down.1.op x) (D.map z.down.2.op y) :=
  integerLinearizationDesc_generator _ z

/-- 概要：普遍模型の評価は単体射に自然。
方針：基底上で反変関手の合成則とテンソル写像の評価を確認する。
規約：KST A.5。使われ方：評価を単体的な射へ束ねる。 -/
lemma simplexPairEvaluation_naturality {N : ℕ}
    (x : C.obj (op ⦋N⦌)) (y : D.obj (op ⦋N⦌))
    {r s : SimplexCategoryᵒᵖ} (f : r ⟶ s) :
    (linearizedSpace (simplexPairModel N)).map f ≫ simplexPairEvaluationApp C D x y s =
      simplexPairEvaluationApp C D x y r ≫ (simplicialIntegerTensor C D).map f := by
  apply integerLinearization_hom_ext
  intro z
  change simplexPairEvaluationApp C D x y s
      (integerLinearization.map ((simplexPairModel N).map f) (integerGenerator z)) =
    integerTensorMap (C.map f) (D.map f)
      (simplexPairEvaluationApp C D x y r (integerGenerator z))
  rw [integerLinearization_map_generator, simplexPairEvaluationApp_generator,
    simplexPairEvaluationApp_generator]
  change TensorProduct.tmul ℤ
    (C.map (f.unop ≫ z.down.1).op x) (D.map (f.unop ≫ z.down.2).op y) =
    TensorProduct.tmul ℤ (C.map f (C.map z.down.1.op x)) (D.map f (D.map z.down.2.op y))
  simp only [op_comp, C.map_comp, D.map_comp, Quiver.Hom.op_unop, ModuleCat.comp_apply]

/-- 概要：普遍な単体の対を任意の二つの固定単体へ評価する実単体的射。
方針：基底ごとの評価に証明済みの単体的自然性を付ける。
規約：KST Construction A.5、非被約で整数双線形な評価。
使われ方：普遍模型の充填を実際の二つの入力へ移す鎖写像。 -/
def simplexPairEvaluation {N : ℕ} (x : C.obj (op ⦋N⦌)) (y : D.obj (op ⦋N⦌)) :
    linearizedSpace (simplexPairModel N) ⟶ simplicialIntegerTensor C D where
  app := simplexPairEvaluationApp C D x y
  naturality _ _ f := simplexPairEvaluation_naturality C D x y f

/-- 概要：普遍模型の評価は二つの入力加群の射にも自然。
方針：基底上で二つの入力射の単体的自然性を使う。
規約：KST A.5、外部群の作用も含む。
使われ方：再帰的な比較ホモトピーの同変性。 -/
lemma simplexPairEvaluation_map_naturality
    {C' D' : SimplicialObject (ModuleCat.{u} ℤ)} (f : C ⟶ C') (g : D ⟶ D')
    {N : ℕ} (x : C.obj (op ⦋N⦌)) (y : D.obj (op ⦋N⦌)) :
    simplexPairEvaluation C D x y ≫ simplicialIntegerTensorMap f g =
      simplexPairEvaluation C' D' (f.app (op ⦋N⦌) x) (g.app (op ⦋N⦌) y) := by
  apply NatTrans.ext
  funext r
  apply integerLinearization_hom_ext
  intro z
  change integerTensorMap (f.app r) (g.app r)
    (simplexPairEvaluationApp C D x y r (integerGenerator z)) =
      simplexPairEvaluationApp C' D' _ _ r (integerGenerator z)
  rw [simplexPairEvaluationApp_generator, simplexPairEvaluationApp_generator]
  change TensorProduct.tmul ℤ (f.app r (C.map z.down.1.op x))
    (g.app r (D.map z.down.2.op y)) = _
  have hf := congrArg (fun k ↦ k x) (f.naturality z.down.1.op)
  have hg := congrArg (fun k ↦ k y) (g.naturality z.down.2.op)
  exact congrArg₂ (TensorProduct.tmul ℤ) hf hg

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
