module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonSuccessorState

/-!
概要：元の二つの表示に沿い、全前置比較を左右一回ずつ進める一巡を構成する。
方針：同じ原典経路の相対因子化を二回適用し、元の全データを各段に保持する。
規約：一巡の存在は元の filtered 表示から証明する。使われ方：可算交互比較の再帰。
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

/-- 左右それぞれの元の表示内にある実因子化を保持する一巡。 -/
structure ComparisonRound
    (hD₀ : ∀ i : I₀ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
    (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁) where
  left : ComparisonLeftFactor s
  right : ComparisonLeftFactor (comparisonLeftSuccessor left hD₀).swap

/-- 一巡後の状態も、元の同じ二表示と全増大余錐を保持する。 -/
def ComparisonRound.next
    {hD₀ : ∀ i : I₀ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i))}
    {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
    (r : ComparisonRound hD₀ s)
    (hD₁ : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i))) :
    CompactPresentationComparison μ D₀ D₁ c₀ c₁ :=
  comparisonRightSuccessor r.right hD₁

/-- 左右一巡分の全因子化は、元の二つの filtered 表示から構成できる。 -/
lemma nonempty_comparisonRound (hμ : Cardinal.aleph0 < μ)
    [Quasicategory I₀] [IsKappaFiltered μ I₀]
    [Quasicategory I₁] [IsKappaFiltered μ I₁]
    (hC : HasSmallColimits C) (hc₀ : IsColimitCone c₀) (hc₁ : IsColimitCone c₁)
    (hD₀ : ∀ i : I₀ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
    (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁) :
    Nonempty (ComparisonRound hD₀ s) := by
  obtain ⟨f⟩ := nonempty_comparisonLeftFactor hμ hC hc₀ s
  obtain ⟨g⟩ := nonempty_comparisonLeftFactor hμ hC hc₁ (comparisonLeftSuccessor f hD₀).swap
  exact ⟨⟨f, g⟩⟩

/-- 元の全二表示から一巡を選ぶ。選択するのは上で存在を証明した実因子化だけ。 -/
def comparisonRoundChoice (hμ : Cardinal.aleph0 < μ)
    [Quasicategory I₀] [IsKappaFiltered μ I₀]
    [Quasicategory I₁] [IsKappaFiltered μ I₁]
    (hC : HasSmallColimits C) (hc₀ : IsColimitCone c₀) (hc₁ : IsColimitCone c₁)
    (hD₀ : ∀ i : I₀ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
    (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁) : ComparisonRound hD₀ s :=
  Classical.choice (nonempty_comparisonRound hμ hC hc₀ hc₁ hD₀ s)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
