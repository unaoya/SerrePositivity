module

public import SerrePositivity.HomologicalAlgebra.LinearCoYonedaNaturality
public import SerrePositivity.HomologicalAlgebra.ChainTotalizationHomotopy
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.BarWeightComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.DirectSumTotal
public import Mathlib.Algebra.Category.ModuleCat.Projective
import all SerrePositivity.HomologicalAlgebra.LinearCoYonedaNaturality
import all SerrePositivity.HomologicalAlgebra.StandardSimplexWeight
import all SerrePositivity.HomologicalAlgebra.BarWeightProjective
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.BarWeightComparison

/-!
# 線形重みの同じ比較の非有界全複体

## 概要
指定された bar／標準重みの比較を、実際の複体図式との coend と直和全複体へ移す。

## 方針
加法的 coend で重みの鎖ホモトピーを移し、有界性を仮定しない全複体の補題を適用する。

## 規約
前向きの射は先頭頂点の同じ比較。標準重み側は全自然 co-Yoneda 同型で元の複体へ戻す。

## 使われ方
HA 1.2.4。native bar の計算比較の入力であり、native 余錐の主張ではない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
variable (A : Type u) [CommRing A]

/-- 線形重みの鎖複体を元の図式と coend を取り、同じ直和全複体へ送る関手。 -/
def linearWeightTotalFunctor (X : SimplicialObject (Complex A)) :
    ChainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℕ ⥤ Complex A :=
  (linearWeightRealization A X).mapHomologicalComplex (.down ℕ) ⋙
    chainTotalizationFunctor (ModuleCat.{u} A)

/-- 標準重みとの coend は、すべての単体作用素を保って元の図式そのものへ戻る。 -/
def standardWeightRealizationIso (X : SimplicialObject (Complex A)) :
    standardSimplexWeight (𝟙_ (ModuleCat.{u} A)) ⋙ linearWeightRealization A X ≅ X :=
  freeWeightEvaluationNatIso A X

/-- 標準重みの全複体は元の直和全複体と、同じ評価射で同型。 -/
def standardWeightTotalIso (X : SimplicialObject (Complex A)) :
    (linearWeightTotalFunctor A X).obj
      (standardSimplexWeightResolution (𝟙_ (ModuleCat.{u} A))).complex ≅
      (directSumTotalFunctor A).obj X :=
  (chainTotalizationFunctor (ModuleCat.{u} A)).mapIso
    ((alternatingFaceMapComplexCompMapHomologicalComplexIso
      (linearWeightRealization A X)).app _ ≪≫
        (alternatingFaceMapComplex (Complex A)).mapIso (standardWeightRealizationIso A X))

/-- 実際の bar 重みの比較射を前向きに持つ、非有界係数での全複体の鎖ホモトピー同値。 -/
def barStandardLinearTotalHomotopyEquiv (X : SimplicialObject (Complex A)) :
    HomotopyEquiv
      ((linearWeightTotalFunctor A X).obj
        (coefficientBarWeightResolution SimplexCategoryᵒᵖ (𝟙_ (ModuleCat.{u} A))).complex)
      ((linearWeightTotalFunctor A X).obj
        (standardSimplexWeightResolution (𝟙_ (ModuleCat.{u} A))).complex) :=
  chainTotalizationHomotopyEquiv (ModuleCat.{u} A)
    ((linearWeightRealization A X).mapHomotopyEquiv
      (barStandardWeightHomotopyEquiv (𝟙_ (ModuleCat.{u} A))))

/-- 同じ先頭頂点比較の coend の全複体の射は擬同型。 -/
instance barStandardLinearTotal_quasiIso (X : SimplicialObject (Complex A)) :
    QuasiIso ((linearWeightTotalFunctor A X).map
      ((alternatingFaceMapComplex _).map (barStandardWeightComparison (𝟙_ (ModuleCat.{u} A))))) :=
  inferInstanceAs (QuasiIso (barStandardLinearTotalHomotopyEquiv A X).hom)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
