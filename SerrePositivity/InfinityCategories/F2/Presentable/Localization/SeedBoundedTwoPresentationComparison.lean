module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.TwoPresentationComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonSeedBounds
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.NerveIndexPieceCofinality

/-!
概要：元の二つの種集合を支配する、共通大域頂点上の全比較を構成する。
方針：元の各 filtered poset 内の上界から全比較を開始し、右側の元の順序射も回収する。
規約：全比較と両余錐の厳密な一致を保持する。使われ方：共通小部分表示の存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact

/-- 両種集合を支配する、元の二つの全添字図式と全比較の証拠。 -/
structure SeedBoundedTwoPresentationComparison
    {C : SSet.{u + 1}} [Quasicategory C] {A₀ A₁ : Type u} [Preorder A₀] [Preorder A₁]
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₀) ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₁) ⟶ C}
    (c₀ : JoinCocone D₀) (c₁ : JoinCocone D₁) (hv : c₀.vertex = c₁.vertex)
    (seed₀ : Set A₀) (seed₁ : Set A₁) where
  leftIndex : nerve (ULift.{u} ℕ) ⟶ nerve A₀
  rightIndex : nerve (ULift.{u} ℕ) ⟶ nerve A₁
  diagram : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶
    sliceOver (SSet.yonedaEquiv.symm c₀.vertex)
  left_eq : (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n) alternatingEven_monotone)) ≫ diagram =
    (SSet.uliftFunctor.{u + 1, u}).map leftIndex ≫ coconeSliceDiagram c₀
  right_eq : (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n + 1) alternatingOdd_monotone)) ≫ diagram =
    (SSet.uliftFunctor.{u + 1, u}).map rightIndex ≫ transportedCoconeSliceDiagram c₁ c₀.vertex hv.symm
  left_seed : ∀ a ∈ seed₀, a ≤ nerveIndexSequence leftIndex 0
  right_seed : ∀ b ∈ seed₁, b ≤ nerveIndexSequence rightIndex 0

/-- 元の二表示の任意の小さい種集合から、同じ全可算比較が存在する。 -/
lemma nonempty_seedBoundedTwoPresentationComparison
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C] {A₀ A₁ : Type u}
    [Preorder A₀] [Preorder A₁] [IsCardinalFiltered A₀ μ] [IsCardinalFiltered A₁ μ]
    [IsKappaFiltered μ (nerve A₀)] [IsKappaFiltered μ (nerve A₁)]
    (D₀ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₀) ⟶ C)
    (D₁ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₁) ⟶ C)
    (c₀ : JoinCocone D₀) (c₁ : JoinCocone D₁)
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hc₀ : IsColimitCone c₀) (hc₁ : IsColimitCone c₁)
    (hD₀ : ∀ i, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
    (hD₁ : ∀ i, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
    (hv : c₀.vertex = c₁.vertex)
    (seed₀ : Set A₀) (hs₀ : HasCardinalLT seed₀ μ)
    (seed₁ : Set A₁) (hs₁ : HasCardinalLT seed₁ μ) :
    Nonempty (SeedBoundedTwoPresentationComparison c₀ c₁ hv seed₀ seed₁) := by
  obtain ⟨a, ha⟩ := exists_sequentialSeed_bound seed₀ hs₀
  obtain ⟨b, hb⟩ := exists_sequentialSeed_bound seed₁ hs₁
  obtain ⟨J₀, J₁, H, h₀, h₁, hstart₀, j, hstart₁⟩ :=
    exists_twoPresentationComparison hμ D₀ D₁ c₀ c₁ hC hc₀ hc₁ hD₀ hD₁ hv
      (nerveEquiv.symm a) (nerveEquiv.symm b)
  refine ⟨⟨J₀, J₁, H, h₀, h₁, ?_, ?_⟩⟩
  · intro x hx
    change x ≤ nerveEquiv (J₀.app (Opposite.op ⦋0⦌) ((nerveEquiv (C := ULift.{u} ℕ)).symm (ULift.up 0)))
    rw [hstart₀, Equiv.apply_symm_apply]
    exact ha x hx
  · intro y hy
    change y ≤ nerveEquiv (J₁.app (Opposite.op ⦋0⦌) ((nerveEquiv (C := ULift.{u} ℕ)).symm (ULift.up 0)))
    rw [hstart₁]
    exact (hb y hy).trans (nerve_pointCoslice_le b j)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
