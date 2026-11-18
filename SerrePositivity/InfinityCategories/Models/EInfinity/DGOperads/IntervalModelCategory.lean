module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraSmallObject
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IntervalJCellAcyclicity

/-!
模型。文献の定義との比較は後で
# 余代数区間からの完全な転送モデル構造

概要：Berger–Moerdijk 命題 4.1 の Hopf オペラッドと余代数区間から代数のモデル構造を得る。
方針：小極限余極限・自由像の小対象性・任意の始域での J-cell acyclicity を転送に渡す。
規約：係数環は任意の可換環で、モデル構造は局所的に選ぶ。
使われ方：具体的な Barratt–Eccles の余代数区間を代入する工程の受け口となる。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：Hopf オペラッドの余代数区間は完全な代数のモデル構造を与える（BM 命題 4.1）。
方針：構成済みの二つの小対象分解と J-cell acyclicity に右転送を適用する。
規約：始域の cofibrancy は不要で、大域 instance には登録しない。
使われ方：具体区間の代入で E∞ 代数のモデル構造を供給する。 -/
@[instance_reducible]
def intervalModelCategory (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit) :
    ModelCategory P.Algebra := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory_cofibrantlyGenerated A
  exact _root_.SerrePositivity.ModelGeneration.rightTransfer (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A)
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A) P.freeAlgebraAdjunction
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.freeGeneratingTrivialCofibrations_cell_acyclicity hP I)

/-- 概要：転送された弱同値は忘却後の擬同型（BM 命題 4.1）。
方針：転送に指定した逆像の類を評価する。
規約：選んだモデル構造のフィールドを明示する。
使われ方：E∞ 代数の弱同値を底の複体で判定する。 -/
lemma intervalModelCategory_weakEquivalences (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P)
    (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit) :
    @weakEquivalences P.Algebra _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.intervalModelCategory hP I).categoryWithWeakEquivalences =
      (quasiIso (ModuleCat A) (.up ℤ)).inverseImage (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) := rfl

/-- 概要：転送された fibration は忘却後の全次数全射（BM 命題 4.1）。
方針：転送に指定した射影 fibration の逆像を評価する。
規約：選んだモデル構造のフィールドを明示する。
使われ方：代数の fibration を底の複体で判定する。 -/
lemma intervalModelCategory_fibrations (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P)
    (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit) :
    @fibrations P.Algebra _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.intervalModelCategory hP I).categoryWithFibrations =
      (_root_.SerrePositivity.ProjectiveModel.projectiveFibrations A).inverseImage (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) := rfl

/-- 概要：転送モデル構造は自由像の I・J で生成される（BM 命題 4.1）。
方針：右転送の生成射の判定を適用する。
規約：小対象引数の補助宇宙は u。
使われ方：代数の cofibrant 置換と写像空間を構成する。 -/
lemma intervalModelCategory_cofibrantlyGenerated (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P)
    (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit) :
    let := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.intervalModelCategory hP I
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u}
      ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).strictMap P.freeAlgebraFunctor)
      ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A).strictMap P.freeAlgebraFunctor) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory_cofibrantlyGenerated A
  exact _root_.SerrePositivity.ModelGeneration.rightTransfer_cofibrantlyGenerated (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A)
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A) P.freeAlgebraAdjunction
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.freeGeneratingTrivialCofibrations_cell_acyclicity hP I)

/-- 概要：転送後の忘却関手は右 Quillen（BM 命題 4.1）。
方針：右転送による二つの右類の保存を使う。
規約：底と代数のモデル構造を局所的に選ぶ。
使われ方：具体区間の代入後に U の導来関手を構成する。 -/
lemma intervalModelCategory_forget_isRightQuillen (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P)
    (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.intervalModelCategory hP I
    SerrePositivity.Quillen.IsRightQuillen (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory_cofibrantlyGenerated A
  exact _root_.SerrePositivity.ModelGeneration.rightTransfer_isRightQuillen (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A)
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A) P.freeAlgebraAdjunction
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.freeGeneratingTrivialCofibrations_cell_acyclicity hP I)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
