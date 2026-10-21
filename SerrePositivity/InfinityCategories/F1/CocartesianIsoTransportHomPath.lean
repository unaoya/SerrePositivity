module

public import SerrePositivity.InfinityCategories.F1.CocartesianIsoTransportEdge
public import SerrePositivity.InfinityCategories.F1.InvertibleFunctorEdgePathEdgeFamily

/-!
概要：全局所 Hom の同じ可逆比較辺を、元の全区間族を保持する path の族へ持ち上げる。
方針：同じ辺の Yoneda 表現を使って包含後の族を厳密に回収する。
規約：辺の代表を選び直さず、両端の元の分類主写像を保持する。
使われ方：既存の結合 Hom span への全局所比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (A : Type u) [Category.{u} A]

/-- 同じ全局所比較辺の一単体は、元の転置区間族の Yoneda 表現。 -/
lemma cocartesianIsoTransportEdge_yoneda :
    SSet.yonedaEquiv (transposeFunctorFamily (cocartesianIsoTransportIntervalFamily A)) =
      (cocartesianIsoTransportEdge A).edge := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})) = homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  change SSet.yonedaEquiv (transposeFunctorFamily (cocartesianIsoTransportIntervalFamily A)) =
    (transposeFunctorFamily (cocartesianIsoTransportIntervalFamily A)).app
      (Opposite.op ⦋1⦌) homotopyIntervalEdge.edge
  simpa only [Category.id_comp, hi] using SSet.yonedaEquiv_comp
    (𝟙 (Δ[1] : SSet.{u + 1}))
    (transposeFunctorFamily (cocartesianIsoTransportIntervalFamily A))

/-- 元の全局所 Hom に自然な、同じ比較辺の可逆 path の族。 -/
def cocartesianIsoTransportHomPath :
    CocartesianIsoTransportInfinity A ⟶
      equivalencePath (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))) :=
  invertibleFunctorEdgePath (cocartesianIsoTransportEdge A).toTruncated
    (cocartesianIsoTransportEdge_isInvertible A)

/-- 同じ path の包含は、元の全局所比較の区間族そのもの。 -/
lemma cocartesianIsoTransportHomPath_ι :
    cocartesianIsoTransportHomPath A ≫ equivalencePathι _ =
      cocartesianIsoTransportIntervalFamily A :=
  invertibleFunctorEdgePath_ι_of_edge_family
    (A := CocartesianIsoTransportInfinity A)
    (Y := CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A)))
    (cocartesianIsoTransportEdge A) (cocartesianIsoTransportEdge_isInvertible A)
    (cocartesianIsoTransportIntervalFamily A) (cocartesianIsoTransportEdge_yoneda A)

/-- 同じ path の零端点は、元の始域評価に続く同じ分類。 -/
lemma cocartesianIsoTransportHomPath_zero :
    cocartesianIsoTransportHomPath A ≫ equivalencePathEndpoint _ 0 =
      cocartesianIsoTransportSource A ≫ cocartesianStraighteningCoherentMap A :=
  invertibleFunctorEdgePath_zero _ _

/-- 同じ path の一端点は、元の結合共役に続く同じ分類。 -/
lemma cocartesianIsoTransportHomPath_one :
    cocartesianIsoTransportHomPath A ≫ equivalencePathEndpoint _ 1 =
      cocartesianIsoTransportTarget A ≫ cocartesianStraighteningCoherentMap A :=
  invertibleFunctorEdgePath_one _ _

end SerrePositivity.InfinityCategories
