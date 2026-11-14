module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanCospanPathEndpoints
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanCospanPoint

/-!
概要：元の二入力を持つ Kan 引き戻し射を、元の指定全 path の表示へ戻す。
方針：元の path 座標を uncurry し、端点を二入力の式で照合する。
規約：表示は元の射と厳密に一致し、path を選び直さない。
使われ方：任意の有限標的射を元の二入力の場合の検出へ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：二入力が元の入力の単位像なら、元の Kan 引き戻し射を指定 path 表示できる。
方針：指定 path をそのまま uncurry し、三座標の一致を確認する。
規約：等式による表示。使われ方：任意の標的射の有限検出。 -/
lemma kanCospanPoint_recognition {K E D H : SSet.{u}} (f : E ⟶ H) (g : D ⟶ H)
    (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g))
    (u : K ⟶ E) (v : K ⟶ D)
    (hl : a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) = u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E)
    (hr : a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) = v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app D) :
    ∃ L : SSet.Homotopy (u ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H)
      (v ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H), a = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint f g u v L := by
  let q := a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g)
  let L : SSet.Homotopy
      ((u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f)
      ((v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) :=
    { h := (β_ K (Δ[1] : SSet.{u})).hom ≫ uncurry q
      h₀ := by
        change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ uncurry q =
          (u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f
        rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
        change (a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath _ _) ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app _ = _
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath_zero, ← Category.assoc, hl]
      h₁ := by
        change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ uncurry q =
          (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g
        rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
        change (a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath _ _) ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 1).app _ = _
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath_one, ← Category.assoc, hr]
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanRawPath f g u v L, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback_hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint_path]
    change q = curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫
      (β_ K (Δ[1] : SSet.{u})).hom ≫ uncurry q)
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp, curry_uncurry]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint_left, hl]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint_right, hr]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
