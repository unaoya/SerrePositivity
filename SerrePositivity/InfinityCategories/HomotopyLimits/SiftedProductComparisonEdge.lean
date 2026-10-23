module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SiftedProductComparison
public import SerrePositivity.InfinityCategories.F2.FiberwisePullbackKanObjects
public import SerrePositivity.InfinityCategories.F2.EdgeApexPrism
public import SerrePositivity.InfinityCategories.F1.Coherent.KanInvertible

/-!
概要：元の全空間積比較を、その同じ coherent な辺の頂点円柱にする。
方針：両対象を既存の Kan 模型に束ね、元の比較を辺として保つ。
規約：sifted 性は可逆性にだけ使用。使われ方：native な積錐の指定頂点輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)

/-- 元の全空間積比較を元の Kan 対象間の射として保持する。 -/
def totalProductComparisonKanMap :
    F2.continuousKanObject (pullback p q) ⟶
      (kanTensorLeft (F2.continuousKanObject E)).obj (F2.continuousKanObject D) :=
  F2.totalKanProductComparison p q

/-- 元の比較辺を、その全一単体を保つ頂点円柱にする。 -/
def totalProductComparisonApexPrism :
    (Δ[1] : SSet.{u + 1}) ⊗ (Δ[0] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} :=
  F2.edgeApexPrism (coherentNerveEdge (totalProductComparisonKanMap p q))

/-- 頂点円柱の始点は元の fiber ごとの積の全空間 Kan 模型。 -/
lemma totalProductComparisonApexPrism_zero :
    prismEndpoint 0 (Δ[0] : SSet.{u + 1}) ≫ totalProductComparisonApexPrism p q =
      SSet.yonedaEquiv.symm (coherentNerveVertex (F2.continuousKanObject (pullback p q))) :=
  F2.edgeApexPrism_zero _

/-- 頂点円柱の終点は元の二全空間の Kan 模型の直積。 -/
lemma totalProductComparisonApexPrism_one :
    prismEndpoint 1 (Δ[0] : SSet.{u + 1}) ≫ totalProductComparisonApexPrism p q =
      SSet.yonedaEquiv.symm (coherentNerveVertex
        ((kanTensorLeft (F2.continuousKanObject E)).obj (F2.continuousKanObject D))) :=
  F2.edgeApexPrism_one _

/-- sifted な底上の元の比較の頂点円柱は、全ての垂直辺が可逆。 -/
lemma totalProductComparisonApexPrism_vertical_isInvertible [IsSiftedInfinity B]
    [LeftFibration p] [LeftFibration q] (x : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    IsInvertibleEdge (edgeOfSimplex ((totalProductComparisonApexPrism p q).app
      (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})),
        PinchedHom.constant x 1))) := by
  have := kanTensor_isKan (F2.continuousKanReplacement.obj E) (F2.continuousKanReplacement.obj D)
  exact F2.edgeApexPrism_vertical_isInvertible _
    (coherentKanEdge_isInvertible_of_isQCatEquivalence
      (totalKanProductComparison_homotopyEquivalence_of_sifted p q).isQCatEquivalence) x

end SerrePositivity.InfinityCategories.HomotopyLimits
