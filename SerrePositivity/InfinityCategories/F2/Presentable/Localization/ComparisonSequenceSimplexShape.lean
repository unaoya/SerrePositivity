module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonSequence
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonRoundSimplexShape

/-!
概要：可算全比較列の全形状を、共終な次数の標準単体列へ正規化する。
方針：初期形状の同型を各実一巡に沿って再帰的に延ばす。
規約：隣接する元の指定包含を全前置包含として保持する。使われ方：公開貼合入口。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact

/-- 一巡ごとに二次数進む、元の比較列の標準単体次数。 -/
def comparisonSequenceDegree (m : ℕ) : ℕ → ℕ :=
  Nat.rec m (fun _ k ↦ k + 2)

/-- この次数は元の自然数上で単調。 -/
lemma comparisonSequenceDegree_monotone (m : ℕ) : Monotone (comparisonSequenceDegree m) := by
  apply monotone_nat_of_le_succ
  intro n
  change comparisonSequenceDegree m n ≤ comparisonSequenceDegree m n + 2
  omega

/-- 比較列の次数は全ての有限次数に達する。 -/
lemma comparisonSequenceDegree_cofinal (m : ℕ) :
    ∀ k, ∃ n, k ≤ comparisonSequenceDegree m n := by
  have h : ∀ n, n ≤ comparisonSequenceDegree m n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n hn =>
      change n + 1 ≤ comparisonSequenceDegree m n + 2
      omega
  exact fun k ↦ ⟨k, h k⟩

variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {C : SSet.{u + 1}} [Quasicategory C]
  {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁}
variable (hμ : Cardinal.aleph0 < μ)
  [Quasicategory I₀] [IsKappaFiltered μ I₀]
  [Quasicategory I₁] [IsKappaFiltered μ I₁]
  (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hc₀ : IsColimitCone c₀) (hc₁ : IsColimitCone c₁)
  (hD₀ : ∀ i : I₀ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
  (hD₁ : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
  (s₀ : CompactPresentationComparison μ D₀ D₁ c₀ c₁)
  {m : ℕ} (e₀ : s₀.shape ≅ (Δ[m] : SSet.{u}))

/-- 各段の元の全形状と同じ標準単体の指定同型。 -/
def comparisonSequenceShapeIso : ∀ n,
    (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).shape ≅
      (Δ[comparisonSequenceDegree m n] : SSet.{u}) :=
  Nat.rec (motive := fun n ↦
    (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).shape ≅
      (Δ[comparisonSequenceDegree m n] : SSet.{u})) e₀
    (fun n e ↦ (comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).simplexShapeIso hD₁ e)

/-- 全形状の元の包含は、共終標準単体列の同じ前置包含となる。 -/
lemma comparisonSequenceShapeIso_prefix (n : ℕ) :
    comparisonSequenceInclusion hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n ≫
      (comparisonSequenceShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ (n + 1)).hom =
    (comparisonSequenceShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n).hom ≫
      simplexPrefix ((comparisonSequenceDegree_monotone m) (Nat.le_succ n)) :=
  (comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).simplexShapeIso_prefix hD₁
    (comparisonSequenceShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
