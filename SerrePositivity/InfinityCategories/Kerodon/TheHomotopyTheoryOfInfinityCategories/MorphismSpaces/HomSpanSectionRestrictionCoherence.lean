module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportSquareEndpointNormalization
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomSpanSectionRestrictionIdentity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomSpanSectionBoundaryCoherence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportSquarePrecomposition

/-!
概要：同じ span の指定切断の制限自然性を、任意の作用上で端点正規化した因子比較に移す。
方針：指定正方形を引き戻し、等号同型を消去して同じ境界の因子比較を回収する。
規約：元の指定切断・制限自然性・因子比較の値を保持する。
使われ方：第一辺の指定比較を元の大域自然性へ接続する。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 任意の元の作用上で、指定制限同型と端点正規化した因子比較は同じ源の因子比較。 -/
lemma homSpanSectionTransportNaturalityIso_normalized_identity
    {H₀ H₁ X₀ X₁ Y₀ Y₁ K : SSet.{u}}
    [Quasicategory H₀] [Quasicategory H₁] [Quasicategory X₀] [Quasicategory X₁]
    [Quasicategory Y₀] [Quasicategory Y₁] [Quasicategory K]
    (p₀ : H₀ ⟶ X₀) (p₁ : H₀ ⟶ X₁) (q₀ : H₁ ⟶ Y₀) (q₁ : H₁ ⟶ Y₁) (r : H₀ ⟶ H₁)
    (s₀ : X₁ ⟶ H₀) (s₁ : Y₁ ⟶ H₁) (u₀ : X₀ ⟶ Y₀) (u₁ : X₁ ⟶ Y₁)
    (hp₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence p₁) (hq₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful q₁)
    (hs₀ : s₀ ≫ p₁ = 𝟙 _) (hs₁ : s₁ ≫ q₁ = 𝟙 _)
    (h₀ : p₀ ≫ u₀ = r ≫ q₀) (h₁ : p₁ ≫ u₁ = r ≫ q₁) (a : K ⟶ H₀)
    (hs : ((a ≫ r) ≫ q₁) ≫ (s₁ ≫ q₀) = ((a ≫ p₁) ≫ u₁) ≫ (s₁ ≫ q₀))
    (ht : (a ≫ r) ≫ q₀ = (a ≫ p₀) ≫ u₀) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomSpanSectionRestrictionCommutesAt p₀ p₁ q₀ q₁ r s₀ s₁ u₀ u₁
      hp₁ hq₁ hs₀ hs₁ h₀ h₁ a hs ht := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomSpanSectionRestrictionCommutesAt
  have h0a : (a ≫ p₀) ≫ u₀ = (a ≫ r) ≫ q₀ :=
    (Category.assoc a p₀ u₀).trans
      ((congrArg (fun v ↦ a ≫ v) h₀).trans (Category.assoc a r q₀).symm)
  have h1a : (a ≫ p₁) ≫ u₁ = (a ≫ r) ≫ q₁ :=
    (Category.assoc a p₁ u₁).trans
      ((congrArg (fun v ↦ a ≫ v) h₁).trans (Category.assoc a r q₁).symm)
  have hA := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportSquareCommutes.precomp _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionTransportNaturalityIso_identity p₀ p₁ q₀ q₁ r s₀ s₁ u₀ u₁
      hp₁ hq₁ hs₀ hs₁ h₀ h₁) a
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportSquareCommutes at hA
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso.precomp_eqToIso h₀ a, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso.precomp_eqToIso h₁ a] at hA
  have hN := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportSquareCommutes.strict_normalized
    (a ≫ p₀) (a ≫ p₁) q₀ q₁ (a ≫ r) (s₀ ≫ p₀) (s₁ ≫ q₀) u₀ u₁
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionBoundaryIso p₁ p₀ s₀ hp₁.isFullyFaithful hs₀).precomp a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionBoundaryIso q₁ q₀ s₁ hq₁ hs₁)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionTransportNaturalityIso p₀ p₁ q₀ q₁ r s₀ s₁ u₀ u₁
      hp₁ hq₁ hs₀ hs₁ h₀ h₁) h0a h1a hs hA
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionBoundaryIso_precomp] using hN

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
