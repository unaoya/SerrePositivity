module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomSpanSectionRestrictionNaturality

/-!
概要：同じ制限正方形の指定値を、大域比較の両射影が回収する元の作用へ移す。
方針：零・一作用の厳密な等式を消去し、同じ正規化した因子を保持する。
規約：新しい自然性や同型の代表を選ばない。
使われ方：第一辺の制限正方形と元の大域自然性を同じ端点で貼り合わせる。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

variable {H₀ H₁ X₀ X₁ Y₀ Y₁ K : SSet.{u}}
  [Quasicategory H₀] [Quasicategory H₁] [Quasicategory X₀] [Quasicategory X₁]
  [Quasicategory Y₀] [Quasicategory Y₁] [Quasicategory K]
  (p₀ : H₀ ⟶ X₀) (p₁ : H₀ ⟶ X₁) (q₀ : H₁ ⟶ Y₀) (q₁ : H₁ ⟶ Y₁) (r : H₀ ⟶ H₁)
  (s₀ : X₁ ⟶ H₀) (s₁ : Y₁ ⟶ H₁) (u₀ : X₀ ⟶ Y₀) (u₁ : X₁ ⟶ Y₁)
  (hp₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence p₁) (hq₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful q₁)
  (hs₀ : s₀ ≫ p₁ = 𝟙 _) (hs₁ : s₁ ≫ q₁ = 𝟙 _)
  (h₀ : p₀ ≫ u₀ = r ≫ q₀) (h₁ : p₁ ≫ u₁ = r ≫ q₁) (a : K ⟶ H₀)
  (hs : ((a ≫ r) ≫ q₁) ≫ (s₁ ≫ q₀) = ((a ≫ p₁) ≫ u₁) ≫ (s₁ ≫ q₀))
  (ht : (a ≫ r) ≫ q₀ = (a ≫ p₀) ≫ u₀)
  (a₁ : K ⟶ X₁) (a₀ : K ⟶ X₀) (ha₁ : a ≫ p₁ = a₁) (ha₀ : a ≫ p₀ = a₀)
  {f g : K ⟶ Y₀} (n : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)

/-- 元の零・一作用へ端点を移した、同じ指定制限正方形の貼り合わせ等式。 -/
def HomSpanSectionRestrictionRebasedNaturalityAt : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoPastingHEq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionTransportNaturalityIso p₀ p₁ q₀ q₁ r s₀ s₁ u₀ u₁
      hp₁ hq₁ hs₀ hs₁ h₀ h₁).precomp a₁)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionTransportFactorIso q₁ q₀ s₁ hq₁ hs₁ (a ≫ r)) hs ht)
      (congrArg (fun m ↦ (m ≫ u₁) ≫ (s₁ ≫ q₀)) ha₁)
      (congrArg (fun m ↦ m ≫ u₀) ha₀)) n

/-- 元の両射影の厳密な回収は、貼り合わせの指定値全体を保持する。 -/
lemma HomSpanSectionRestrictionNaturalityAt.rebase
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomSpanSectionRestrictionNaturalityAt p₀ p₁ q₀ q₁ r s₀ s₁ u₀ u₁
      hp₁ hq₁ hs₀ hs₁ h₀ h₁ a hs ht n) :
    HomSpanSectionRestrictionRebasedNaturalityAt p₀ p₁ q₀ q₁ r s₀ s₁ u₀ u₁
      hp₁ hq₁ hs₀ hs₁ h₀ h₁ a hs ht a₁ a₀ ha₁ ha₀ n := by
  subst a₁ a₀
  exact h

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
