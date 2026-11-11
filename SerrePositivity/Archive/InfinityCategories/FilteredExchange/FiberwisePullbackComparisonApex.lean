module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackKanObjects
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.EdgeApexPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible

/-!
概要：実際の全空間 Kan 引き戻し比較を 𝒮 内の指定可逆頂点円柱にする。
方針：元の Kan 比較を coherent nerve の辺にし、その全一単体を円柱へ写す。
規約：別の同値を選ばない。使われ方：元の比較を保つ native 極限錐の頂点輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H)

/-- 概要：実際の比較の coherent な辺を保持する 𝒮 内の頂点円柱。
方針：元の比較辺の Yoneda 表示。規約：全一単体。使われ方：全錐比較の頂点の指定。 -/
def fiberwisePullbackComparisonApexPrism :
    (Δ[1] : SSet.{u + 1}) ⊗ (Δ[0] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} :=
  edgeApexPrism (coherentNerveEdge (fiberwisePullbackComparisonKanMap p f g))

/-- 概要：頂点円柱の始点は元の引き戻し全空間の Kan 模型。
方針：元の辺の始点。規約：厳密な射。使われ方：輸送後の錐の頂点。 -/
lemma fiberwisePullbackComparisonApexPrism_zero :
    prismEndpoint 0 (Δ[0] : SSet.{u + 1}) ≫ fiberwisePullbackComparisonApexPrism p f g =
      SSet.yonedaEquiv.symm (coherentNerveVertex (fiberwisePullbackTotalKanObject p f g)) :=
  edgeApexPrism_zero _

/-- 概要：頂点円柱の終点は元の三 Kan 全空間の path 引き戻し。
方針：元の辺の終点。規約：厳密な射。使われ方：既存の極限錐の頂点との照合。 -/
lemma fiberwisePullbackComparisonApexPrism_one :
    prismEndpoint 1 (Δ[0] : SSet.{u + 1}) ≫ fiberwisePullbackComparisonApexPrism p f g =
      SSet.yonedaEquiv.symm (coherentNerveVertex (fiberwisePullbackTargetKanObject f g)) :=
  edgeApexPrism_one _

/-- 概要：元の filtered 引き戻し比較の頂点円柱は全垂直辺が可逆。
方針：証明済みのホモトピー逆を coherent 辺の可逆性へ移す。
規約：元の比較自体。使われ方：極限性を保つ全錐の輸送。 -/
lemma fiberwisePullbackComparisonApexPrism_vertical_isInvertible
    [Quasicategory B] [IsFilteredInfinity B] [LeftFibration p]
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] (x : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    IsInvertibleEdge (edgeOfSimplex ((fiberwisePullbackComparisonApexPrism p f g).app
      (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})),
        PinchedHom.constant x 1))) := by
  have hq : IsQCatEquivalence (fiberwisePullbackComparisonKanMap p f g) :=
    (fiberwisePullbackKanComparison_isSimplicialHomotopyEquivalence p f g).isQCatEquivalence
  exact edgeApexPrism_vertical_isInvertible _
    (coherentKanEdge_isInvertible_of_isQCatEquivalence hq) x

end SerrePositivity.InfinityCategories.F2
