module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexPairFaithfulEvaluation

/-!
# 普遍模型の交代面移送

概要：一つ低い標的次数の普遍鎖を全ての面に沿って移し、交代和を取る。
方針：二つの単体射へ同じ面を後合成する写像を自由化する。
規約：KST Construction A.5、標的次数と鎖次数は独立。
使われ方：標準比較ホモトピーの再帰の既構成部分と二重面の相殺。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

/-- 概要：普遍鎖を標的の全ての面へ送り交代和を取る。
方針：両方の標的単体へ同じ面を後合成する。
規約：KST A.5、鎖次数 r は固定する。
使われ方：再帰的比較の一つ低いホモトピーの境界。 -/
def simplexPairFaceSum {N : ℕ} (r : SimplexCategoryᵒᵖ)
    (z : (linearizedSpace (simplexPairModel.{u} N)).obj r) :
    (linearizedSpace (simplexPairModel (N + 1))).obj r :=
  ∑ i : Fin (N + 2), (-1 : ℤ) ^ (i : ℕ) •
    (linearizedSpaceMap (simplexPairModelMap (SimplexCategory.δ i) (SimplexCategory.δ i))).app r z

/-- 概要：交代面移送は零を零へ送る。
方針：各移送の線形性を使う。
規約：KST A.5。使われ方：比較の再帰の零次の端。 -/
@[simp] lemma simplexPairFaceSum_zero (N : ℕ) (r : SimplexCategoryᵒᵖ) :
    simplexPairFaceSum r (0 : (linearizedSpace (simplexPairModel.{u} N)).obj r) = 0 := by
  simp only [simplexPairFaceSum, map_zero, smul_zero, Finset.sum_const_zero]

/-- 概要：交代面移送は鎖の差を保つ。
方針：各移送と整数作用の加法性を有限和へ分配する。
規約：KST A.5。使われ方：再帰での二つの既構成項の相殺。 -/
lemma simplexPairFaceSum_sub {N : ℕ} (r : SimplexCategoryᵒᵖ)
    (z w : (linearizedSpace (simplexPairModel.{u} N)).obj r) :
    simplexPairFaceSum r (z - w) = simplexPairFaceSum r z - simplexPairFaceSum r w := by
  simp only [simplexPairFaceSum, map_sub, smul_sub, Finset.sum_sub_distrib]

/-- 概要：交代面移送の作用素は入力対角の微分の前合成。
方針：面ごとの後合成の評価を有限交代和へ移す。
規約：KST A.5。使われ方：標的方向の二重面和の消滅と再帰の微分。 -/
lemma simplexPairOperation_faceSum (C D : SimplicialObject (ModuleCat.{u} ℤ))
    {N : ℕ} (r : SimplexCategoryᵒᵖ)
    (z : (linearizedSpace (simplexPairModel.{u} N)).obj r) :
    simplexPairOperation C D r (simplexPairFaceSum r z) =
      ((alternatingFaceMapComplex _).obj (simplicialIntegerTensor C D)).d (N + 1) N ≫
        simplexPairOperation C D r z := by
  rw [simplexPairFaceSum, map_sum, alternatingFaceMapComplex_obj_d,
    AlternatingFaceMapComplex.objD, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, simplexPairOperation_modelMap, Preadditive.zsmul_comp]
  rfl

/-- 概要：標的方向の交代面移送を二回行うと零。
方針：普遍作用素で検出し、実鎖複体の二重微分が零であることを使う。
規約：KST A.5、追加公理なしで等式を普遍模型へ戻す。
使われ方：再帰で構成する充填入力のサイクル性。 -/
lemma simplexPairFaceSum_faceSum {N : ℕ} (r : SimplexCategoryᵒᵖ)
    (z : (linearizedSpace (simplexPairModel.{u} N)).obj r) :
    simplexPairFaceSum r (simplexPairFaceSum r z) = 0 := by
  apply simplexPairOperation_injective (N + 2) r
  rw [simplexPairOperation_faceSum, simplexPairOperation_faceSum, map_zero,
    ← Category.assoc, HomologicalComplex.d_comp_d, Limits.zero_comp]

/-- 概要：交代面移送は普遍鎖の微分と可換。
方針：作用素で検出し、二つの方向の微分を前合成と後合成へ分ける。
規約：KST A.5、標的と鎖の二つの次数を混同しない。
使われ方：再帰の低次ホモトピーの境界を現在の普遍模型へ移す。 -/
lemma simplexPairFaceSum_boundary {N : ℕ} (n : ℕ)
    (z : (linearizedSpace (simplexPairModel.{u} N)).obj (op ⦋n + 1⦌)) :
    ((alternatingFaceMapComplex _).obj (linearizedSpace (simplexPairModel (N + 1)))).d
        (n + 1) n (simplexPairFaceSum (op ⦋n + 1⦌) z) =
      simplexPairFaceSum (op ⦋n⦌)
        (((alternatingFaceMapComplex _).obj (linearizedSpace (simplexPairModel N))).d (n + 1) n z) := by
  apply simplexPairOperation_injective (N + 1) (op ⦋n⦌)
  rw [simplexPairOperation_boundary, simplexPairOperation_faceSum,
    simplexPairOperation_faceSum, simplexPairOperation_boundary, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
