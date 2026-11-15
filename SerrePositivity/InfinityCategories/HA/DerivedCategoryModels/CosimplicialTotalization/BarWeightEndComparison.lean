module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardWeightTotalComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.BarWeightComparison
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
概要：元の積 Tot を、bar 重みからの線形 end の積全複体と鎖ホモトピー同値で結ぶ。
方針：3b-1 の指定された先頭頂点比較の鎖ホモトピー同値を、反変 end と積全複体に移す。
規約：前向き射は標準重みへの指定射の前合成。任意の持ち上げは逆射にのみ使う。
使われ方：HA 1.2.4、G10 の線形計算比較。native 錐の極限性はこの宣言には含まない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 指定された bar 重みの線形 end の積全複体。 -/
def barWeightEndTotal (X : CosimplicialObject (Complex A)) : Complex A :=
  (linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).obj
    (op (coefficientBarWeightResolution SimplexCategoryᵒᵖ (ModuleCat.of A A)).complex)

/-- 元の積 Tot と bar 重みの end を、先頭頂点の同じ比較で結ぶ鎖ホモトピー同値。 -/
def barWeightEndTotalHomotopyEquiv (X : CosimplicialObject (Complex A)) :
    HomotopyEquiv ((productTotalFunctor A).obj X) (barWeightEndTotal X) :=
  (HomotopyEquiv.ofIso (standardWeightEndTotalIso X).symm).trans
    (linearWeightEndTotalHomotopyEquiv A (doubleOppositeDiagram X)
      (SimplicialRealization.barStandardWeightHomotopyEquiv (ModuleCat.of A A)))

/-- 前向き射は指定された先頭頂点比較の前合成であり、比較の選び直しではない。 -/
theorem barWeightEndTotalHomotopyEquiv_hom (X : CosimplicialObject (Complex A)) :
    (barWeightEndTotalHomotopyEquiv X).hom =
      (standardWeightEndTotalIso X).inv ≫
        (linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).map
          ((alternatingFaceMapComplex _).map
            (SimplicialRealization.barStandardWeightComparison (ModuleCat.of A A))).op := rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
