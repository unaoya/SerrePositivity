module

public import SerrePositivity.EInfinity.BarrattEccles.ModelCategory
public import SerrePositivity.HomotopicalAlgebra.ModelCategory.OppositeFactorization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution
public import Mathlib.AlgebraicTopology.ModelCategory.Opposite

/-!
# E 代数の関手的な右 frame

概要：BM 命題 4.1 の実際の E 代数モデルから Hovey §5 の右 frame を構成する。
方針：生成類による分解を反対圏へ移し、関手的な余単体的 cofibrant 分解を使う。
規約：単体集合のモデル構造・E 代数のモデル構造の存在を入力仮定にしない。
使われ方：一般図式の homotopy 極限の重み付き余テンソル。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.Reedy

variable (A : Type u) [CommRing A]

/-- 概要：E 代数の反対圏の第一の関手的モデル分解（BM 命題 4.1、Hovey §1.1）。
方針：元の trivial cofibration・fibration 分解を左右反転する。
規約：具体的なモデルを局所的に使い、分解の存在は証明して供給する。
使われ方：右 frame の関手的な選択。 -/
def rightFrameFactorization :
    let := modelCategory A
    MorphismProperty.FunctorialFactorizationData
      (cofibrations (operad A).Algebraᵒᵖ) (trivialFibrations (operad A).Algebraᵒᵖ) := by
  let := modelCategory A
  have := modelCategory_cofibrantlyGenerated A
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_trivialCofibration_fibration
    ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).strictMap (operad A).freeAlgebraFunctor)
    ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A).strictMap (operad A).freeAlgebraFunctor)
  change MorphismProperty.FunctorialFactorizationData
    (cofibrations (operad A).Algebraᵒᵖ) (trivialFibrations (operad A).Algebraᵒᵖ)
  rw [cofibrations_op, trivialFibrations_op]
  exact _root_.SerrePositivity.OppositeFactorization.OppositeFactorization.opposite (MorphismProperty.functorialFactorizationData
    (trivialCofibrations (operad A).Algebra) (fibrations (operad A).Algebra))

/-- 概要：実際の E 代数の右 frame の関手的な族（Hovey §5.2）。
方針：反対圏で余単体的 cofibrant 分解の既存構成を使う。
規約：反対圏の余単体図式として記述し、すべての代数射に関手的。
使われ方：小図式へ同時に右 frame を適用する。 -/
def rightFrameFamily :
    let := modelCategory A
    CofibrantResolutionFamily (C := (operad A).Algebraᵒᵖ) simplex := by
  let := modelCategory A
  exact cosimplicialResolutionFamily (rightFrameFactorization A)

/-- 概要：指定した E 代数の反対圏での余単体的右 frame（Hovey §5.2）。
方針：構成した関手族を元の対象で評価する。
規約：元の E 代数の型と作用を保持する。
使われ方：右 frame の重み付き実現の入力。 -/
def rightFrame (X : (operad A).Algebra) : SimplexCategory ⥤ (operad A).Algebraᵒᵖ := by
  let := modelCategory A
  exact (rightFrameFamily A).obj.obj (op X)

/-- 概要：元の代数から右 frame の各成分への比較（Hovey §5.2）。
方針：反対圏での augmentation の各成分を反転する。
規約：すべての次元で同じ元の代数を使う。
使われ方：余テンソルの標準単体での値を元の対象と比較する。 -/
def rightFrameComparison (X : (operad A).Algebra) (n : SimplexCategory) :
    X ⟶ ((rightFrame A X).obj n).unop := by
  let := modelCategory A
  exact (((rightFrameFamily A).augmentation.app (op X)).app n).unop

/-- 概要：右 frame の各成分への比較は底の擬同型（Hovey §5.2）。
方針：Reedy 自明 fibration の各成分の弱同値性を反対圏から移す。
規約：元の代数の cofibrancy は不要。
使われ方：標準単体の余テンソルのホモトピー型。 -/
lemma rightFrameComparison_quasiIso (X : (operad A).Algebra) (n : SimplexCategory) :
    QuasiIso (rightFrameComparison A X n).hom := by
  let := modelCategory A
  exact ((rightFrameFamily A).atObject (op X)).augmentation_weakEquivalence n

/-- 概要：選んだ右 frame は反対圏で Reedy cofibrant（Hovey §5.2）。
方針：関手的分解の第一のクラスの保証を使う。
規約：元の圏では Reedy fibrant な右 frame に対応する。
使われ方：余テンソルの境界包含に沿う fibration の証明。 -/
lemma rightFrame_cofibrant (X : (operad A).Algebra) :
    let := modelCategory A
    reedyLeft simplex (cofibrations (operad A).Algebraᵒᵖ)
      (Limits.initial.to (rightFrame A X)) := by
  let := modelCategory A
  exact (rightFrameFamily A).cofibrant (op X)

/-- 概要：右 frame のすべての単体作用素は弱同値（Hovey §5.2）。
方針：定値図式への augmentation と二つのうち三つの性質を使う。
規約：全次元・全単体作用素、単体集合のモデル構造は不要。
使われ方：余テンソルのホーン包含に沿う自明 fibration の証明。 -/
lemma rightFrame_homotopicallyConstant (X : (operad A).Algebra)
    {n m : SimplexCategory} (f : n ⟶ m) :
    let := modelCategory A
    weakEquivalences (operad A).Algebraᵒᵖ ((rightFrame A X).map f) := by
  let := modelCategory A
  exact ((rightFrameFamily A).atObject (op X)).homotopicallyConstant f

/-- 概要：右 frame は元の E 代数の擬同型を全次数で保つ（BM §1、Hovey §5.2）。
方針：元の比較への augmentation の自然性と二つのうち三つの性質を使う。
規約：始域の cofibrancy は不要。
使われ方：図式の右 frame をホモトピー不変に選ぶ。 -/
lemma rightFrame_map_weakEquivalence {X Y : (operad A).Algebra}
    (f : X ⟶ Y) (hf : QuasiIso f.hom) (n : SimplexCategory) :
    let := modelCategory A
    weakEquivalences (operad A).Algebraᵒᵖ
      (((rightFrameFamily A).obj.map f.op).app n) := by
  let := modelCategory A
  exact (rightFrameFamily A).map_weakEquivalence f.op hf n

end SerrePositivity.EInfinity.BarrattEccles
