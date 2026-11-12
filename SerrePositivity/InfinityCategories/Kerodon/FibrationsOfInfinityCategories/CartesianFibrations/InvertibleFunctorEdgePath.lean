module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.PointwiseHomotopyPath

/-!
概要：指定された可逆な関手の辺を、同じ全円柱の可逆 path の族として保つ。
方針：元の辺のホモトピーを点ごとの可逆 path に持ち上げる。
規約：ホモトピー圏の同型から別の辺の代表を選び直さない。
使われ方：底変換比較の同じ辺の Hom を共通比較空間にする。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

variable {A Y : SSet.{u}} [Quasicategory Y] {f g : A ⟶ Y}
  (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj Y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e)

/-- 指定された可逆辺の全円柱を保つ、元の始域上の可逆 path の族。 -/
def invertibleFunctorEdgePath : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.pointwiseHomotopyPath (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible e he)

/-- 同じ可逆 path の始点は、元の辺の始域関手。 -/
lemma invertibleFunctorEdgePath_zero :
    invertibleFunctorEdgePath e he ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0 = f :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.pointwiseHomotopyPath_zero _ _

/-- 同じ可逆 path の終点は、元の辺の終域関手。 -/
lemma invertibleFunctorEdgePath_one :
    invertibleFunctorEdgePath e he ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 1 = g :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.pointwiseHomotopyPath_one _ _

/-- 可逆 path の包含は、指定された元の辺の円柱の curry を厳密に回収する。 -/
lemma invertibleFunctorEdgePath_ι :
    invertibleFunctorEdgePath e he ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y =
      curry ((β_ (Δ[1] : SSet.{u}) A).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e).h) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.pointwiseHomotopyPath_ι _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
