module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.OuterHornConverse
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram

/-!
概要：区間 path 置換の元の全 path を正規化した円柱と指定同型で読む。
方針：元の path 射影を uncurry して Kan 標的で辺の類を可逆にする。
規約：代表を選び直さない。使われ方：元の二射影と native 錐の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {X Y : SSet.{u}} (f : X ⟶ Y)

/-- 概要：置換の元の全 path を二端点の指定ホモトピーにする。
方針：元の円柱の恒等入力を正規化。規約：全 path を保持。使われ方：指定可換同型。 -/
def intervalReplacementCanonicalPathHomotopy :
    SSet.Homotopy (pullback.snd ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f ≫ f)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f) where
  h := (β_ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacement f) (Δ[1] : SSet.{u})).hom ≫
    uncurry (pullback.fst ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f)
  h₀ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacement f) ≫
      uncurry (pullback.fst ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f) =
        pullback.snd ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f ≫ f
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    exact pullback.condition
  h₁ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacement f) ≫
      uncurry (pullback.fst ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f) = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：元の置換の path 円柱を指定可換同型にする。
方針：Kan 内部 Hom の辺の可逆性。規約：元の辺の類。使われ方：交換則の入力。 -/
def intervalReplacementPathIso [KanComplex Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (pullback.snd ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f ≫ f)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (intervalReplacementCanonicalPathHomotopy f)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_kanComplex _)
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (intervalReplacementCanonicalPathHomotopy f)))

/-- 概要：指定可換同型の順方向の射は元の全円柱の類。
方針：asIso の定義。規約：指定値。使われ方：切断上での簡約。 -/
lemma intervalReplacementPathIso_hom [KanComplex Y] :
    (intervalReplacementPathIso f).hom = SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (intervalReplacementCanonicalPathHomotopy f)) := rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
