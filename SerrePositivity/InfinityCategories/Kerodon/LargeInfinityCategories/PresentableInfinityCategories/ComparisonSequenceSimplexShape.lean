module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonSequence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonRoundSimplexShape

/-!
概要：可算全比較列の全形状を、共終な次数の標準単体列へ正規化する。
方針：初期形状の同型を各実一巡に沿って再帰的に延ばす。
規約：隣接する元の指定包含を全前置包含として保持する。使われ方：公開貼合入口。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 一巡ごとに二次数進む、元の比較列の標準単体次数。 -/
def comparisonSequenceDegree (m : ℕ) : ℕ → ℕ :=
  Nat.rec m (fun _ k ↦ k + 2)

/-- この次数は元の自然数上で単調。 -/
lemma comparisonSequenceDegree_monotone (m : ℕ) : Monotone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceDegree m) := by
  apply monotone_nat_of_le_succ
  intro n
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceDegree m n ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceDegree m n + 2
  omega

/-- 比較列の次数は全ての有限次数に達する。 -/
lemma comparisonSequenceDegree_cofinal (m : ℕ) :
    ∀ k, ∃ n, k ≤ comparisonSequenceDegree m n := by
  have h : ∀ n, n ≤ comparisonSequenceDegree m n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n hn =>
      change n + 1 ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceDegree m n + 2
      omega
  exact fun k ↦ ⟨k, h k⟩

variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {C : SSet.{u + 1}} [Quasicategory C]
  {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀} {c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁}
variable (hμ : Cardinal.aleph0 < μ)
  [Quasicategory I₀] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I₀]
  [Quasicategory I₁] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I₁]
  (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hc₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₀) (hc₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₁)
  (hD₀ : ∀ i : I₀ _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
  (hD₁ : ∀ i : I₁ _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
  (s₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactPresentationComparison μ D₀ D₁ c₀ c₁)
  {m : ℕ} (e₀ : s₀.shape ≅ (Δ[m] : SSet.{u}))

/-- 各段の元の全形状と同じ標準単体の指定同型。 -/
def comparisonSequenceShapeIso : ∀ n,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).shape ≅
      (Δ[_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceDegree m n] : SSet.{u}) :=
  Nat.rec (motive := fun n ↦
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).shape ≅
      (Δ[_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceDegree m n] : SSet.{u})) e₀
    (fun n e ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).simplexShapeIso hD₁ e)

/-- 全形状の元の包含は、共終標準単体列の同じ前置包含となる。 -/
lemma comparisonSequenceShapeIso_prefix (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceInclusion hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ (n + 1)).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefix ((comparisonSequenceDegree_monotone m) (Nat.le_succ n)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).simplexShapeIso_prefix hD₁
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
