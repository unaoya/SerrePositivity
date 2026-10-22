module

public import SerrePositivity.InfinityCategories.F1.ReplacementSpanComparison
public import SerrePositivity.InfinityCategories.F1.KanFibrationEquivalenceLifting

/-!
概要：三成分で同値な Kan cospan の同じ厳密 pullback 比較は前合成同値。
方針：両側の一脚の Kan 性を既存の同時 path 置換による比較へ渡す。
規約：構成した同じ pullback 写像を保持する。
使われ方：境界のホーンと欠けた面の比較を貼り合わせる。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories

/-- 同値な三成分と両側の一脚の Kan 性から、同じ pullback 比較の前合成同値を得る。 -/
lemma kanSpanPullbackMap_isPrecompositionEquivalence
    {A₀ A₁ A₂ B₀ B₁ B₂ : SSet.{u}}
    [KanComplex A₀] [KanComplex A₁] [KanComplex A₂]
    [KanComplex B₀] [KanComplex B₁] [KanComplex B₂]
    (p₁ : A₁ ⟶ A₀) (p₂ : A₂ ⟶ A₀) (q₁ : B₁ ⟶ B₀) (q₂ : B₂ ⟶ B₀)
    [Fibration p₁] [Fibration q₁]
    (u₀ : A₀ ⟶ B₀) (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂)
    (h₁ : u₁ ≫ q₁ = p₁ ≫ u₀) (h₂ : u₂ ≫ q₂ = p₂ ≫ u₀)
    (hu₀ : IsQCatEquivalence u₀) (hu₁ : IsQCatEquivalence u₁) (hu₂ : IsQCatEquivalence u₂) :
    IsPrecompositionEquivalence (spanPullbackMap p₁ p₂ q₁ q₂ u₀ u₁ u₂ h₁ h₂) := by
  have : TrivialKanFibration (relativeEquivalencePathMapAt q₁ 0) :=
    HomotopyLimits.relativeEquivalencePathMapAt_trivialKanFibration_of_fibration q₁ 0
  exact isPrecompositionEquivalence_spanPullbackMap_of_equivalenceLifting
    p₁ p₂ q₁ q₂ u₀ u₁ u₂ h₁ h₂ hu₀ hu₁ hu₂
    (kanEquivalenceLifting_of_kanFibration p₁) (kanEquivalenceLifting_of_kanFibration q₁)

end SerrePositivity.InfinityCategories
