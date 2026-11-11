module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ReplacementSpanComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanFibrationEquivalenceLifting

/-!
概要：三成分で同値な Kan cospan の同じ厳密 pullback 比較は前合成同値。
方針：両側の一脚の Kan 性を既存の同時 path 置換による比較へ渡す。
規約：構成した同じ pullback 写像を保持する。
使われ方：境界のホーンと欠けた面の比較を貼り合わせる。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 同値な三成分と両側の一脚の Kan 性から、同じ pullback 比較の前合成同値を得る。 -/
lemma kanSpanPullbackMap_isPrecompositionEquivalence
    {A₀ A₁ A₂ B₀ B₁ B₂ : SSet.{u}}
    [KanComplex A₀] [KanComplex A₁] [KanComplex A₂]
    [KanComplex B₀] [KanComplex B₁] [KanComplex B₂]
    (p₁ : A₁ ⟶ A₀) (p₂ : A₂ ⟶ A₀) (q₁ : B₁ ⟶ B₀) (q₂ : B₂ ⟶ B₀)
    [Fibration p₁] [Fibration q₁]
    (u₀ : A₀ ⟶ B₀) (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂)
    (h₁ : u₁ ≫ q₁ = p₁ ≫ u₀) (h₂ : u₂ ≫ q₂ = p₂ ≫ u₀)
    (hu₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence u₀) (hu₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence u₁) (hu₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence u₂) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.spanPullbackMap p₁ p₂ q₁ q₂ u₀ u₁ u₂ h₁ h₂) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt q₁ 0) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_trivialKanFibration_of_fibration q₁ 0
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_spanPullbackMap_of_equivalenceLifting
    p₁ p₂ q₁ q₂ u₀ u₁ u₂ h₁ h₂ hu₀ hu₁ hu₂
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEquivalenceLifting_of_kanFibration p₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEquivalenceLifting_of_kanFibration q₁)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
