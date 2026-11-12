module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportSquareCoherence
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoEndpointProjection

/-!
概要：指定切断の制限正方形が任意の元の作用上で満たす正規化した等式。
方針：同じ全データと端点等式を保持して貼り合わせ等式を命題に束ねる。
規約：元の指定自然性と因子比較を保持する。
使われ方：大きな大域比較への特殊化時に、同じ等式の構造を保持する。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 元の作用で引き戻した指定制限正方形の、端点正規化後の貼り合わせ等式。 -/
def HomSpanSectionRestrictionCommutesAt
    {H₀ H₁ X₀ X₁ Y₀ Y₁ K : SSet.{u}}
    [Quasicategory H₀] [Quasicategory H₁] [Quasicategory X₀] [Quasicategory X₁]
    [Quasicategory Y₀] [Quasicategory Y₁] [Quasicategory K]
    (p₀ : H₀ ⟶ X₀) (p₁ : H₀ ⟶ X₁) (q₀ : H₁ ⟶ Y₀) (q₁ : H₁ ⟶ Y₁) (r : H₀ ⟶ H₁)
    (s₀ : X₁ ⟶ H₀) (s₁ : Y₁ ⟶ H₁) (u₀ : X₀ ⟶ Y₀) (u₁ : X₁ ⟶ Y₁)
    (hp₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence p₁) (hq₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful q₁)
    (hs₀ : s₀ ≫ p₁ = 𝟙 _) (hs₁ : s₁ ≫ q₁ = 𝟙 _)
    (h₀ : p₀ ≫ u₀ = r ≫ q₀) (h₁ : p₁ ≫ u₁ = r ≫ q₁) (a : K ⟶ H₀)
    (hs : ((a ≫ r) ≫ q₁) ≫ (s₁ ≫ q₀) = ((a ≫ p₁) ≫ u₁) ≫ (s₁ ≫ q₀))
    (ht : (a ≫ r) ≫ q₀ = (a ≫ p₀) ≫ u₀) : Prop :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionTransportNaturalityIso p₀ p₁ q₀ q₁ r s₀ s₁ u₀ u₁
      hp₁ hq₁ hs₀ hs₁ h₀ h₁).precomp (a ≫ p₁) ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionTransportFactorIso q₁ q₀ s₁ hq₁ hs₁ (a ≫ r)) hs ht =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionTransportFactorIso p₁ p₀ s₀ hp₁.isFullyFaithful hs₀ a).postcomp u₀

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
