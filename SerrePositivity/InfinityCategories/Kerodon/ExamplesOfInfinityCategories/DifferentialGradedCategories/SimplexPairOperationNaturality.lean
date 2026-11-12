module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexPairOperation
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# 普遍鎖の作用素の自然性と微分

概要：模型の標的単体・入力加群・交代面微分との可換性を実作用素として確認する。
方針：純テンソル上で単体的評価射の自然性を使う。
規約：KST Construction A.5、群や環の可換性を追加しない。
使われ方：普遍な充填による比較ホモトピーの再帰と外部作用の同変性。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

/-- 概要：整数テンソルからの射は全ての純テンソル上で決定する。
方針：テンソル積の帰納法と加法性を使う。
規約：KST A.5、加群と整数環の宇宙は独立。
使われ方：普遍鎖の作用素の等式の検出。 -/
lemma integerTensor_pure_hom_ext {M N P : ModuleCat.{u} ℤ} {f g : integerTensor M N ⟶ P}
    (h : ∀ x y, f (TensorProduct.tmul ℤ x y) = g (TensorProduct.tmul ℤ x y)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine TensorProduct.inductionOn z (fun x y ↦ h x y) (fun a b ha hb ↦ ?_)
  simp only [map_add, ha, hb]

variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- 概要：普遍模型の後合成による移送と入力単体の制限は同じ評価を与える。
方針：基底上で反変関手の合成則を適用する。
規約：KST A.5。使われ方：低次の普遍鎖を面に沿って現在の模型へ送る。 -/
lemma simplexPairEvaluation_modelMap {N M : ℕ} (f g : ⦋N⦌ ⟶ ⦋M⦌)
    (x : C.obj (op ⦋M⦌)) (y : D.obj (op ⦋M⦌)) :
    linearizedSpaceMap (simplexPairModelMap f g) ≫ simplexPairEvaluation C D x y =
      simplexPairEvaluation C D (C.map f.op x) (D.map g.op y) := by
  apply NatTrans.ext
  funext r
  apply integerLinearization_hom_ext
  intro z
  change simplexPairEvaluationApp C D x y r
    (integerLinearization.map ((simplexPairModelMap f g).app r) (integerGenerator z)) = _
  rw [integerLinearization_map_generator]
  change simplexPairEvaluationApp C D x y r (integerGenerator _) =
    simplexPairEvaluationApp C D _ _ r (integerGenerator z)
  rw [simplexPairEvaluationApp_generator, simplexPairEvaluationApp_generator]
  change TensorProduct.tmul ℤ (C.map (z.down.1 ≫ f).op x) (D.map (z.down.2 ≫ g).op y) = _
  simp only [op_comp, C.map_comp, D.map_comp, ModuleCat.comp_apply]

/-- 概要：普遍鎖の標的単体に沿う移送は入力側の制限の前合成に一致。
方針：純テンソル上で単体的評価の後合成公式を使う。
規約：KST A.5。使われ方：再帰の低次境界の実写像への同定。 -/
lemma simplexPairOperation_modelMap {N M : ℕ} (f g : ⦋N⦌ ⟶ ⦋M⦌)
    (r : SimplexCategoryᵒᵖ) (z : (linearizedSpace (simplexPairModel.{u} N)).obj r) :
    simplexPairOperation C D r ((linearizedSpaceMap (simplexPairModelMap f g)).app r z) =
      integerTensorMap (C.map f.op) (D.map g.op) ≫ simplexPairOperation C D r z := by
  apply integerTensor_pure_hom_ext
  intro x y
  change simplexPairOperation C D r _ (TensorProduct.tmul ℤ x y) =
    simplexPairOperation C D r z (TensorProduct.tmul ℤ (C.map f.op x) (D.map g.op y))
  rw [simplexPairOperation_tmul, simplexPairOperation_tmul]
  exact congrArg (fun k ↦ k.app r z) (simplexPairEvaluation_modelMap C D f g x y)

/-- 概要：普遍鎖の作用素は二つの入力加群の射に自然。
方針：純テンソルに評価し、単体的評価射の入力自然性を使う。
規約：KST A.5、外部群の作用を含む。
使われ方：標準比較ホモトピーの同変性。 -/
lemma simplexPairOperation_map_naturality
    {C' D' : SimplicialObject (ModuleCat.{u} ℤ)} (f : C ⟶ C') (g : D ⟶ D')
    {N : ℕ} (r : SimplexCategoryᵒᵖ) (z : (linearizedSpace (simplexPairModel.{u} N)).obj r) :
    integerTensorMap (f.app (op ⦋N⦌)) (g.app (op ⦋N⦌)) ≫ simplexPairOperation C' D' r z =
      simplexPairOperation C D r z ≫ integerTensorMap (f.app r) (g.app r) := by
  apply integerTensor_pure_hom_ext
  intro x y
  change simplexPairOperation C' D' r z
      (TensorProduct.tmul ℤ (f.app (op ⦋N⦌) x) (g.app (op ⦋N⦌) y)) =
    integerTensorMap (f.app r) (g.app r) (simplexPairOperation C D r z (TensorProduct.tmul ℤ x y))
  rw [simplexPairOperation_tmul, simplexPairOperation_tmul]
  exact (congrArg (fun k ↦ k.app r z) (simplexPairEvaluation_map_naturality C D f g x y)).symm

/-- 概要：普遍鎖の境界の評価は評価した作用素の後の交代面微分に一致。
方針：純テンソル上で評価射が誘導する実鎖写像の微分可換性を使う。
規約：KST Construction A.5、模型の標的次数 N と鎖の次数は独立。
使われ方：普遍サイクルの充填を実比較ホモトピーの境界へ移す。 -/
lemma simplexPairOperation_boundary {N : ℕ} (n : ℕ)
    (z : (linearizedSpace (simplexPairModel.{u} N)).obj (op ⦋n + 1⦌)) :
    simplexPairOperation C D (op ⦋n⦌)
      (((alternatingFaceMapComplex _).obj (linearizedSpace (simplexPairModel N))).d (n + 1) n z) =
    simplexPairOperation C D (op ⦋n + 1⦌) z ≫
      ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).d (n + 1) n := by
  apply integerTensor_pure_hom_ext
  intro x y
  change simplexPairOperation C D (op ⦋n⦌) _ (TensorProduct.tmul ℤ x y) =
    ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).d (n + 1) n
      (simplexPairOperation C D (op ⦋n + 1⦌) z (TensorProduct.tmul ℤ x y))
  rw [simplexPairOperation_tmul, simplexPairOperation_tmul]
  exact (congrArg (fun k ↦ k z)
    (((alternatingFaceMapComplex _).map (simplexPairEvaluation C D x y)).comm (n + 1) n)).symm

/-- 概要：普遍な対角単体を整数自由加群の基底として取る。
方針：二つの恒等単体射の対。
規約：KST A.5。使われ方：標準比較の帰納法の恒等項。 -/
def simplexPairUniversalDiagonal (N : ℕ) :
    (linearizedSpace (simplexPairModel.{u} N)).obj (op ⦋N⦌) :=
  integerGenerator (ULift.up (𝟙 ⦋N⦌, 𝟙 ⦋N⦌))

/-- 概要：普遍な対角単体の作用素は恒等写像。
方針：二つの恒等射のテンソルの評価公式を使う。
規約：KST A.5。使われ方：比較の普遍サイクルの恒等項。 -/
lemma simplexPairOperation_universalDiagonal (N : ℕ) :
    simplexPairOperation C D (op ⦋N⦌) (simplexPairUniversalDiagonal N) =
      𝟙 (integerTensor (C.obj (op ⦋N⦌)) (D.obj (op ⦋N⦌))) := by
  rw [simplexPairUniversalDiagonal, simplexPairOperation_generator]
  simp only [op_id, C.map_id, D.map_id, integerTensorMap_id]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
