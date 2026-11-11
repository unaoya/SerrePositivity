module

public import SerrePositivity.EInfinity.BarrattEccles.Hopf
public import SerrePositivity.EInfinity.IntervalCuts.CoalgebraInterval
public import SerrePositivity.EInfinity.Operad.IntervalModelCategory

/-!
# 実際の Barratt–Eccles 代数の転送モデル構造

概要：Berger–Moerdijk 命題 4.1 に具体的な Hopf E と正規化区間を代入する。
方針：構成済みの E-coalgebra 区間を完全な抽象右転送へ渡す。
規約：任意の可換環、モデル構造は局所的に選び大域 instance にしない。
使われ方：E2a-4・5 の右 Quillen 忘却・homotopy 引き戻し・写像空間、E2b。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomotopicalAlgebra HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：実際の E 代数の完全な転送モデル構造（BM 命題 4.1）。
方針：AW Hopf 構造と実際の正規化区間を抽象転送定理へ代入する。
規約：任意の可換基礎環、始域の cofibrancy 仮定なし、大域 instance にはしない。
使われ方：E 代数の導来圏と CAlg_R の具体的なモデル。 -/
@[instance_reducible]
def modelCategory : ModelCategory (operad A).Algebra :=
  Operad.intervalModelCategory (hopf A) (IntervalCuts.coalgebraInterval A)

/-- 概要：具体的な E 代数の弱同値は忘却後の擬同型（BM 命題 4.1）。
方針：具体区間を代入した転送モデル構造の弱同値類を評価する。
規約：モデル構造のフィールドを明示する。
使われ方：E 代数の弱同値を底の複体で判定する。 -/
lemma modelCategory_weakEquivalences :
    @weakEquivalences (operad A).Algebra _ (modelCategory A).categoryWithWeakEquivalences =
      (quasiIso (ModuleCat A) (.up ℤ)).inverseImage (Operad.Algebra.forget (operad A)) :=
  Operad.intervalModelCategory_weakEquivalences (hopf A) (IntervalCuts.coalgebraInterval A)

/-- 概要：具体的な E 代数の fibration は忘却後の全次数全射（BM 命題 4.1）。
方針：具体区間を代入した転送モデル構造の fibration 類を評価する。
規約：モデル構造のフィールドを明示する。
使われ方：底の複体で E 代数の fibration を判定する。 -/
lemma modelCategory_fibrations :
    @fibrations (operad A).Algebra _ (modelCategory A).categoryWithFibrations =
      (projectiveFibrations A).inverseImage (Operad.Algebra.forget (operad A)) :=
  Operad.intervalModelCategory_fibrations (hopf A) (IntervalCuts.coalgebraInterval A)

/-- 概要：具体的な E 代数のモデル構造は自由像の生成類で生成される（BM 命題 4.1）。
方針：抽象転送の小対象性と生成類判定へ具体区間を代入する。
規約：補助宇宙は基礎環と同じ u、モデル構造を局所的に選ぶ。
使われ方：cofibrant 置換と homotopy function complex の具体的構成。 -/
lemma modelCategory_cofibrantlyGenerated :
    let := modelCategory A
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u}
      ((projectiveGeneratingCofibrations A).strictMap (operad A).freeAlgebraFunctor)
      ((projectiveGeneratingTrivialCofibrations A).strictMap (operad A).freeAlgebraFunctor) :=
  Operad.intervalModelCategory_cofibrantlyGenerated (hopf A) (IntervalCuts.coalgebraInterval A)

/-- 概要：具体的な E 代数の忘却関手は右 Quillen（BM 命題 4.1）。
方針：完全な右転送の保存定理へ具体区間を代入する。
規約：底と代数のモデル構造を局所的に選ぶ。
使われ方：E2a-4 の導来忘却と E2b の U : CAlg_R → D(R)。 -/
lemma forget_isRightQuillen :
    let := projectiveModelCategory A
    let := modelCategory A
    SerrePositivity.Quillen.IsRightQuillen (Operad.Algebra.forget (operad A)) :=
  Operad.intervalModelCategory_forget_isRightQuillen (hopf A) (IntervalCuts.coalgebraInterval A)

end SerrePositivity.EInfinity.BarrattEccles
