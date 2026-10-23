module

public import SerrePositivity.InfinityCategories.F1.Joins.SpanPullbackLifting

/-!
概要：三成分が同型な同じ span 比較の pullback 射は同型。
方針：元の三成分と可換式を保ったまま、通常の pullback.map の同型性へ戻す。
規約：元の二つの pullback と比較射を変更しない。
使われ方：標準セルと元の nerve セルの表示同型による Segal 制限の移送。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 三成分が同型なら、同じ指定された span の pullback 比較も同型。 -/
lemma spanPullbackMap_isIso {A₀ A₁ A₂ B₀ B₁ B₂ : SSet.{u}}
    (p₁ : A₁ ⟶ A₀) (p₂ : A₂ ⟶ A₀) (q₁ : B₁ ⟶ B₀) (q₂ : B₂ ⟶ B₀)
    (u₀ : A₀ ⟶ B₀) (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂)
    (h₁ : u₁ ≫ q₁ = p₁ ≫ u₀) (h₂ : u₂ ≫ q₂ = p₂ ≫ u₀)
    [IsIso u₀] [IsIso u₁] [IsIso u₂] :
    IsIso (spanPullbackMap p₁ p₂ q₁ q₂ u₀ u₁ u₂ h₁ h₂) := by
  change IsIso (pullback.map p₁ p₂ q₁ q₂ u₁ u₂ u₀ h₁.symm h₂.symm)
  infer_instance

end SerrePositivity.InfinityCategories
