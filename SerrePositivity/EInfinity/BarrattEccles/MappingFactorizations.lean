module

public import SerrePositivity.EInfinity.BarrattEccles.ModelCategory
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution

/-!
# E 代数の導来写像空間の具体的な関手的分解

概要：BM 命題 4.1 のモデルから Hovey §5 の写像空間の二つの関手的分解を選ぶ。
方針：具体的な自由生成類による小対象論法を使う。
規約：分解の存在やモデル構造を入力仮定にせず、大域モデル instance は登録しない。
使われ方：E2a-5 の実際の homotopy function complex。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomotopicalAlgebra

variable (A : Type u) [CommRing A]

/-- 概要：導来写像空間の cofibrant 側の関手的分解（BM 命題 4.1、Hovey §5）。
方針：自由生成 cofibration の小対象分解を使う。
規約：具体的な E 代数モデルを局所的に選ぶ。
使われ方：関手的な余単体的始域 frame。 -/
def mappingCofibrantFactorization :
    let := modelCategory A
    MorphismProperty.FunctorialFactorizationData
      (cofibrations (operad A).Algebra) (trivialFibrations (operad A).Algebra) := by
  let := modelCategory A
  have := modelCategory_cofibrantlyGenerated A
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_cofibration_trivialFibration
    ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).strictMap (operad A).freeAlgebraFunctor)
    ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A).strictMap (operad A).freeAlgebraFunctor)
  exact MorphismProperty.functorialFactorizationData _ _

/-- 概要：導来写像空間の fibrant 側の関手的分解（BM 命題 4.1、Hovey §5）。
方針：自由生成 trivial cofibration の小対象分解を使う。
規約：元の E 代数に cofibrancy を仮定しない。
使われ方：終域の関手的 fibrant 置換と π₀ の計算。 -/
def mappingFibrantFactorization :
    let := modelCategory A
    MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations (operad A).Algebra) (fibrations (operad A).Algebra) := by
  let := modelCategory A
  have := modelCategory_cofibrantlyGenerated A
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_trivialCofibration_fibration
    ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).strictMap (operad A).freeAlgebraFunctor)
    ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A).strictMap (operad A).freeAlgebraFunctor)
  exact MorphismProperty.functorialFactorizationData _ _

end SerrePositivity.EInfinity.BarrattEccles
