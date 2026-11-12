module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportSquareCoherence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportTriangleIdentity

/-!
概要：既存の輸送正方形を共通 Hom へ戻すと、指定された四辺の合成の等式を回収する。
方針：同値による前合成の逆像の像を計算し、同じ指定同型の逆を消去する。
規約：既存の輸送正方形と全境界同型の値を保持する。
使われ方：大域分類 Hom の自然性と共有セルの底制限の整合性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 共通 Hom 上で指定輸送正方形が満たす四辺の等式。 -/
def HomTransportSquareCommutes
    {H₀ H₁ X₀ X₁ Y₀ Y₁ : SSet.{u}}
    (p₀ : H₀ ⟶ X₀) (p₁ : H₀ ⟶ X₁) (q₀ : H₁ ⟶ Y₀) (q₁ : H₁ ⟶ Y₁) (r : H₀ ⟶ H₁)
    (t₀ : X₁ ⟶ X₀) (t₁ : Y₁ ⟶ Y₀) (u₀ : X₀ ⟶ Y₀) (u₁ : X₁ ⟶ Y₁)
    (e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p₁ ≫ t₀) p₀) (e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q₁ ≫ t₁) q₀)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p₀ ≫ u₀) (r ≫ q₀))
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p₁ ≫ u₁) (r ≫ q₁))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (t₀ ≫ u₀) (u₁ ≫ t₁)) : Prop :=
  e.precomp p₁ ≪≫ h₁.postcomp t₁ ≪≫ e₁.precomp r = e₀.postcomp u₀ ≪≫ h₀

/-- 既存の輸送正方形は、同じ共通 Hom 上で指定された四辺の等式を満たす。 -/
lemma homTransportSquareCoherence_identity
    {H₀ H₁ X₀ X₁ Y₀ Y₁ : SSet.{u}}
    [Quasicategory H₀] [Quasicategory H₁] [Quasicategory X₀] [Quasicategory X₁]
    [Quasicategory Y₀] [Quasicategory Y₁]
    (p₀ : H₀ ⟶ X₀) (p₁ : H₀ ⟶ X₁) (q₀ : H₁ ⟶ Y₀) (q₁ : H₁ ⟶ Y₁) (r : H₀ ⟶ H₁)
    (t₀ : X₁ ⟶ X₀) (t₁ : Y₁ ⟶ Y₀) (u₀ : X₀ ⟶ Y₀) (u₁ : X₁ ⟶ Y₁)
    (hp₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence p₁)
    (e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p₁ ≫ t₀) p₀) (e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q₁ ≫ t₁) q₀)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p₀ ≫ u₀) (r ≫ q₀))
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p₁ ≫ u₁) (r ≫ q₁)) :
    HomTransportSquareCommutes p₀ p₁ q₀ q₁ r t₀ t₁ u₀ u₁ e₀ e₁ h₀ h₁
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homTransportSquareCoherence p₀ p₁ q₀ q₁ r t₀ t₁ u₀ u₁ hp₁ e₀ e₁ h₀ h₁) := by
  have h := hp₁.preimage_precompFunctorIso
    (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p₁ ≫ (t₀ ≫ u₀)) (p₁ ≫ (u₁ ≫ t₁)) from
      e₀.postcomp u₀ ≪≫ h₀ ≪≫ (e₁.precomp r).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp h₁.symm t₁)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homTransportSquareCoherence p₀ p₁ q₀ q₁ r t₀ t₁ u₀ u₁
    hp₁ e₀ e₁ h₀ h₁).precomp p₁ = _ at h
  unfold HomTransportSquareCommutes
  rw [h, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_symm]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- 指定切断から作った元の自然性同型は、同じ境界比較の正方形の等式を満たす。 -/
lemma homSpanSectionTransportNaturalityIso_identity
    {H₀ H₁ X₀ X₁ Y₀ Y₁ : SSet.{u}}
    [Quasicategory H₀] [Quasicategory H₁] [Quasicategory X₀] [Quasicategory X₁]
    [Quasicategory Y₀] [Quasicategory Y₁]
    (p₀ : H₀ ⟶ X₀) (p₁ : H₀ ⟶ X₁) (q₀ : H₁ ⟶ Y₀) (q₁ : H₁ ⟶ Y₁) (r : H₀ ⟶ H₁)
    (s₀ : X₁ ⟶ H₀) (s₁ : Y₁ ⟶ H₁) (u₀ : X₀ ⟶ Y₀) (u₁ : X₁ ⟶ Y₁)
    (hp₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence p₁) (hq₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful q₁)
    (hs₀ : s₀ ≫ p₁ = 𝟙 _) (hs₁ : s₁ ≫ q₁ = 𝟙 _)
    (h₀ : p₀ ≫ u₀ = r ≫ q₀) (h₁ : p₁ ≫ u₁ = r ≫ q₁) :
    HomTransportSquareCommutes p₀ p₁ q₀ q₁ r (s₀ ≫ p₀) (s₁ ≫ q₀) u₀ u₁
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionBoundaryIso p₁ p₀ s₀ hp₁.isFullyFaithful hs₀)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionBoundaryIso q₁ q₀ s₁ hq₁ hs₁)
      (eqToIso (congrArg (fun f : H₀ ⟶ Y₀ ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) h₀))
      (eqToIso (congrArg (fun f : H₀ ⟶ Y₁ ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) h₁))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionTransportNaturalityIso p₀ p₁ q₀ q₁ r s₀ s₁ u₀ u₁
        hp₁ hq₁ hs₀ hs₁ h₀ h₁) := by
  exact homTransportSquareCoherence_identity p₀ p₁ q₀ q₁ r
    (s₀ ≫ p₀) (s₁ ≫ q₀) u₀ u₁ hp₁ _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
