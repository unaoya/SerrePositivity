module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonSequence
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.OneConeSimplexShape

/-!
概要：二つの元の前置添字形状を、一次数ずつ延びる標準単体列で表示する。
方針：左右一巡では各側の形状が一回だけ右錐になることを使う。
規約：元の全前置包含を保持する。使われ方：両側の小さい添字図式の貼合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact
variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {C : SSet.{u + 1}} [Quasicategory C]
  {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁}
variable (hμ : Cardinal.aleph0 < μ)
  [Quasicategory I₀] [IsKappaFiltered μ I₀]
  [Quasicategory I₁] [IsKappaFiltered μ I₁]
  (hC : HasSmallColimits C) (hc₀ : IsColimitCone c₀) (hc₁ : IsColimitCone c₁)
  (hD₀ : ∀ i : I₀ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
  (hD₁ : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
  (s₀ : CompactPresentationComparison μ D₀ D₁ c₀ c₁)

/-- 左側の元の全添字形状を、同じ前置標準単体列へ移す同型。 -/
def comparisonSequenceLeftShapeIso {m : ℕ} (e₀ : s₀.left_shape ≅ (Δ[m] : SSet.{u})) : ∀ n,
    (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_shape ≅ (Δ[m + n] : SSet.{u}) :=
  Nat.rec (motive := fun n ↦
    (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_shape ≅ (Δ[m + n] : SSet.{u})) e₀
    (fun _ e ↦ oneConeSimplexIso e)

/-- 右側の元の全添字形状についても、同じ一段ずつの標準単体表示を得る。 -/
def comparisonSequenceRightShapeIso {m : ℕ} (e₀ : s₀.right_shape ≅ (Δ[m] : SSet.{u})) : ∀ n,
    (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_shape ≅ (Δ[m + n] : SSet.{u}) :=
  Nat.rec (motive := fun n ↦
    (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_shape ≅ (Δ[m + n] : SSet.{u})) e₀
    (fun _ e ↦ oneConeSimplexIso e)

/-- 左側の旧全形状への包含は同じ前置標準単体となる。 -/
lemma comparisonSequenceLeftShapeIso_prefix {m : ℕ}
    (e₀ : s₀.left_shape ≅ (Δ[m] : SSet.{u})) (n : ℕ) :
    joinInl (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_shape Δ[0] ≫
      (comparisonSequenceLeftShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ (n + 1)).hom =
    (comparisonSequenceLeftShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n).hom ≫
      simplexPrefix (Nat.add_le_add_left (Nat.le_succ n) m) :=
  oneConeSimplexIso_prefix (comparisonSequenceLeftShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n)

/-- 右側の旧全形状への包含についても同じ前置包含と厳密に可換。 -/
lemma comparisonSequenceRightShapeIso_prefix {m : ℕ}
    (e₀ : s₀.right_shape ≅ (Δ[m] : SSet.{u})) (n : ℕ) :
    joinInl (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_shape Δ[0] ≫
      (comparisonSequenceRightShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ (n + 1)).hom =
    (comparisonSequenceRightShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n).hom ≫
      simplexPrefix (Nat.add_le_add_left (Nat.le_succ n) m) :=
  oneConeSimplexIso_prefix (comparisonSequenceRightShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
