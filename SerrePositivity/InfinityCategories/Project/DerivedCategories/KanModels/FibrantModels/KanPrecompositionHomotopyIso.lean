module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.KanEvaluationEdgeIso

/-! # Kan 標的への任意ホモトピーによる全前合成同型

概要：始域内の辺の可逆性を要求せず、指定実ホモトピーを全関手圏の前合成同型にする。
方針：Kan な関手空間内の実辺と二段降下の普遍比較を接続する。
規約：パラメータごとに選び直さない。使われ方：任意標的での実屋根評価と合成の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
/-- 任意の指定実ホモトピーは、全 Kan 標的への前合成作用の一つの関手同型を与える。 -/
def kanPrecompositionHomotopyIso {A B Z : SSet.{u}} [KanComplex Z]
    {f g : A ⟶ B} (H : SSet.Homotopy f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((pre f).app Z) ((pre g).app Z) := by
  let t := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).map
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPrecompositionMap A B Z))
  let v : Truncated.Edge
      (X := (truncation 2).obj ((ihom ((ihom B).obj Z)).obj ((ihom A).obj Z)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((pre f).app Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((pre g).app Z)) := {
    edge := t.edge
    src_eq := t.src_eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPrecompositionMap_vertex f)
    tgt_eq := t.tgt_eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPrecompositionMap_vertex g) }
  have : IsIso (Truncated.HomotopyCategory.homMk v) :=
    IsGroupoid.all_isIso
      (C := hoFunctor.obj ((ihom ((ihom B).obj Z)).obj ((ihom A).obj Z))) _
  exact asIso (Truncated.HomotopyCategory.homMk v)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
