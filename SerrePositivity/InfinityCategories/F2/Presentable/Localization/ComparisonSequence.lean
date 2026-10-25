module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonRoundRestriction

/-!
概要：元の二表示の相対因子化から、全前置比較の可算交互列を実際に構成する。
方針：存在を証明済みの左右一巡を自然数再帰で選び、全制限の等式を保持する。
規約：可算交互列の存在を入力へ移さない。使われ方：共通の小さい部分表示への貼合。
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

/-- 元の二表示を保持する全比較の可算列。各後続は証明済みの実一巡で作る。 -/
def comparisonSequence : ℕ → CompactPresentationComparison μ D₀ D₁ c₀ c₁ :=
  Nat.rec s₀ (fun _ s ↦ (comparisonRoundChoice hμ hC hc₀ hc₁ hD₀ s).next hD₁)

/-- 列の各段で使った、元の同じ二表示内の実因子化の一巡。 -/
def comparisonSequenceRound (n : ℕ) :
    ComparisonRound hD₀ (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n) :=
  comparisonRoundChoice hμ hC hc₀ hc₁ hD₀ _

/-- 初項は指定した元の初期比較そのもの。 -/
lemma comparisonSequence_zero : comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ 0 = s₀ := rfl

/-- 後続は選んだ同じ実一巡の後続状態そのもの。 -/
lemma comparisonSequence_succ (n : ℕ) :
    comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ (n + 1) =
      (comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).next hD₁ := rfl

/-- 可算列の隣接する全形状を結ぶ、指定された単射。 -/
def comparisonSequenceInclusion (n : ℕ) :
    (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).shape ⟶
      (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ (n + 1)).shape :=
  (comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).inclusion hD₁

/-- 各隣接形状の指定包含は、全次数で単射。 -/
lemma comparisonSequenceInclusion_mono (n : ℕ) :
    Mono (comparisonSequenceInclusion hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n) :=
  (comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).inclusion_mono hD₁

/-- 列の全図式は隣接する元の全形状上で厳密に一致する。 -/
lemma comparisonSequence_diagram_restrict (n : ℕ) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (comparisonSequenceInclusion hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n) ≫
        (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ (n + 1)).diagram =
      (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).diagram :=
  (comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).diagram_restrict hD₁

/-- 列の全増大余錐も、隣接する元の全形状上で厳密に一致する。 -/
lemma comparisonSequence_augmentation_restrict_val (n : ℕ) :
    (((comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ (n + 1)).augmentation).restrict
      ((SSet.uliftFunctor.{u + 1, u}).map
        (comparisonSequenceInclusion hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n))).val =
      (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).augmentation.val :=
  (comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).augmentation_restrict_val hD₁

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
