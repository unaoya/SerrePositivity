module

public import SerrePositivity.EInfinity.Operad.AlgebraSmallObject
public import SerrePositivity.EInfinity.Operad.IntervalJCellAcyclicity

/-!
# 余代数区間からの完全な転送モデル構造

概要：Berger–Moerdijk 命題 4.1 の Hopf オペラッドと余代数区間から代数のモデル構造を得る。
方針：小極限余極限・自由像の小対象性・任意の始域での J-cell acyclicity を転送に渡す。
規約：係数環は任意の可換環で、モデル構造は局所的に選ぶ。
使われ方：具体的な Barratt–Eccles の余代数区間を代入する工程の受け口となる。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory HomotopicalAlgebra HomologicalComplex
open SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {P : Operad A}

/-- 概要：Hopf オペラッドの余代数区間は完全な代数のモデル構造を与える（BM 命題 4.1）。
方針：構成済みの二つの小対象分解と J-cell acyclicity に右転送を適用する。
規約：始域の cofibrancy は不要で、大域 instance には登録しない。
使われ方：具体区間の代入で E∞ 代数のモデル構造を供給する。 -/
@[instance_reducible]
def intervalModelCategory (hP : Hopf P) (I : CoalgebraInterval hP.counit) :
    ModelCategory P.Algebra := by
  let := projectiveModelCategory A
  have := projectiveModelCategory_cofibrantlyGenerated A
  exact ModelGeneration.rightTransfer (projectiveGeneratingCofibrations A)
    (projectiveGeneratingTrivialCofibrations A) P.freeAlgebraAdjunction
    (CoalgebraInterval.freeGeneratingTrivialCofibrations_cell_acyclicity hP I)

/-- 概要：転送された弱同値は忘却後の擬同型（BM 命題 4.1）。
方針：転送に指定した逆像の類を評価する。
規約：選んだモデル構造のフィールドを明示する。
使われ方：E∞ 代数の弱同値を底の複体で判定する。 -/
lemma intervalModelCategory_weakEquivalences (hP : Hopf P)
    (I : CoalgebraInterval hP.counit) :
    @weakEquivalences P.Algebra _ (intervalModelCategory hP I).categoryWithWeakEquivalences =
      (quasiIso (ModuleCat A) (.up ℤ)).inverseImage (Algebra.forget P) := rfl

/-- 概要：転送された fibration は忘却後の全次数全射（BM 命題 4.1）。
方針：転送に指定した射影 fibration の逆像を評価する。
規約：選んだモデル構造のフィールドを明示する。
使われ方：代数の fibration を底の複体で判定する。 -/
lemma intervalModelCategory_fibrations (hP : Hopf P)
    (I : CoalgebraInterval hP.counit) :
    @fibrations P.Algebra _ (intervalModelCategory hP I).categoryWithFibrations =
      (projectiveFibrations A).inverseImage (Algebra.forget P) := rfl

/-- 概要：転送モデル構造は自由像の I・J で生成される（BM 命題 4.1）。
方針：右転送の生成射の判定を適用する。
規約：小対象引数の補助宇宙は u。
使われ方：代数の cofibrant 置換と写像空間を構成する。 -/
lemma intervalModelCategory_cofibrantlyGenerated (hP : Hopf P)
    (I : CoalgebraInterval hP.counit) :
    let := intervalModelCategory hP I
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u}
      ((projectiveGeneratingCofibrations A).strictMap P.freeAlgebraFunctor)
      ((projectiveGeneratingTrivialCofibrations A).strictMap P.freeAlgebraFunctor) := by
  let := projectiveModelCategory A
  have := projectiveModelCategory_cofibrantlyGenerated A
  exact ModelGeneration.rightTransfer_cofibrantlyGenerated (projectiveGeneratingCofibrations A)
    (projectiveGeneratingTrivialCofibrations A) P.freeAlgebraAdjunction
    (CoalgebraInterval.freeGeneratingTrivialCofibrations_cell_acyclicity hP I)

/-- 概要：転送後の忘却関手は右 Quillen（BM 命題 4.1）。
方針：右転送による二つの右類の保存を使う。
規約：底と代数のモデル構造を局所的に選ぶ。
使われ方：具体区間の代入後に U の導来関手を構成する。 -/
lemma intervalModelCategory_forget_isRightQuillen (hP : Hopf P)
    (I : CoalgebraInterval hP.counit) :
    let := projectiveModelCategory A
    let := intervalModelCategory hP I
    SerrePositivity.Quillen.IsRightQuillen (Algebra.forget P) := by
  let := projectiveModelCategory A
  have := projectiveModelCategory_cofibrantlyGenerated A
  exact ModelGeneration.rightTransfer_isRightQuillen (projectiveGeneratingCofibrations A)
    (projectiveGeneratingTrivialCofibrations A) P.freeAlgebraAdjunction
    (CoalgebraInterval.freeGeneratingTrivialCofibrations_cell_acyclicity hP I)

end SerrePositivity.EInfinity.Operad
