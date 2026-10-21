module

public import SerrePositivity.InfinityCategories.F1.HomTransportSquareEndpointNormalization
public import SerrePositivity.InfinityCategories.F1.HomSpanSectionRestrictionIdentity
public import SerrePositivity.InfinityCategories.F1.HomSpanSectionBoundaryCoherence
public import SerrePositivity.InfinityCategories.F1.HomTransportSquarePrecomposition

/-!
概要：同じ span の指定切断の制限自然性を、任意の作用上で端点正規化した因子比較に移す。
方針：指定正方形を引き戻し、等号同型を消去して同じ境界の因子比較を回収する。
規約：元の指定切断・制限自然性・因子比較の値を保持する。
使われ方：第一辺の指定比較を元の大域自然性へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 任意の元の作用上で、指定制限同型と端点正規化した因子比較は同じ源の因子比較。 -/
lemma homSpanSectionTransportNaturalityIso_normalized_identity
    {H₀ H₁ X₀ X₁ Y₀ Y₁ K : SSet.{u}}
    [Quasicategory H₀] [Quasicategory H₁] [Quasicategory X₀] [Quasicategory X₁]
    [Quasicategory Y₀] [Quasicategory Y₁] [Quasicategory K]
    (p₀ : H₀ ⟶ X₀) (p₁ : H₀ ⟶ X₁) (q₀ : H₁ ⟶ Y₀) (q₁ : H₁ ⟶ Y₁) (r : H₀ ⟶ H₁)
    (s₀ : X₁ ⟶ H₀) (s₁ : Y₁ ⟶ H₁) (u₀ : X₀ ⟶ Y₀) (u₁ : X₁ ⟶ Y₁)
    (hp₁ : IsQCatEquivalence p₁) (hq₁ : IsFullyFaithful q₁)
    (hs₀ : s₀ ≫ p₁ = 𝟙 _) (hs₁ : s₁ ≫ q₁ = 𝟙 _)
    (h₀ : p₀ ≫ u₀ = r ≫ q₀) (h₁ : p₁ ≫ u₁ = r ≫ q₁) (a : K ⟶ H₀)
    (hs : ((a ≫ r) ≫ q₁) ≫ (s₁ ≫ q₀) = ((a ≫ p₁) ≫ u₁) ≫ (s₁ ≫ q₀))
    (ht : (a ≫ r) ≫ q₀ = (a ≫ p₀) ≫ u₀) :
    HomSpanSectionRestrictionCommutesAt p₀ p₁ q₀ q₁ r s₀ s₁ u₀ u₁
      hp₁ hq₁ hs₀ hs₁ h₀ h₁ a hs ht := by
  unfold HomSpanSectionRestrictionCommutesAt
  have h0a : (a ≫ p₀) ≫ u₀ = (a ≫ r) ≫ q₀ :=
    (Category.assoc a p₀ u₀).trans
      ((congrArg (fun v ↦ a ≫ v) h₀).trans (Category.assoc a r q₀).symm)
  have h1a : (a ≫ p₁) ≫ u₁ = (a ≫ r) ≫ q₁ :=
    (Category.assoc a p₁ u₁).trans
      ((congrArg (fun v ↦ a ≫ v) h₁).trans (Category.assoc a r q₁).symm)
  have hA := HomTransportSquareCommutes.precomp _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (homSpanSectionTransportNaturalityIso_identity p₀ p₁ q₀ q₁ r s₀ s₁ u₀ u₁
      hp₁ hq₁ hs₀ hs₁ h₀ h₁) a
  unfold HomTransportSquareCommutes at hA
  rw [FunctorIso.precomp_eqToIso h₀ a, FunctorIso.precomp_eqToIso h₁ a] at hA
  have hN := HomTransportSquareCommutes.strict_normalized
    (a ≫ p₀) (a ≫ p₁) q₀ q₁ (a ≫ r) (s₀ ≫ p₀) (s₁ ≫ q₀) u₀ u₁
    ((homSpanSectionBoundaryIso p₁ p₀ s₀ hp₁.isFullyFaithful hs₀).precomp a)
    (homSpanSectionBoundaryIso q₁ q₀ s₁ hq₁ hs₁)
    (homSpanSectionTransportNaturalityIso p₀ p₁ q₀ q₁ r s₀ s₁ u₀ u₁
      hp₁ hq₁ hs₀ hs₁ h₀ h₁) h0a h1a hs hA
  simpa only [homSpanSectionBoundaryIso_precomp] using hN

end SerrePositivity.InfinityCategories
