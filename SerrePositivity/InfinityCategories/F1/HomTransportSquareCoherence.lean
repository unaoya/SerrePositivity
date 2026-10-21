module

public import SerrePositivity.InfinityCategories.F1.HomSpanSectionTransport

/-!
概要：同じ Hom 比較 span の指定された輸送は、span の射に関して自然。
方針：元の共通 Hom で二つの作用を比較し、同値な一射影の前合成で検出する。
規約：指定された元の輸送と切断を選び直さない。
使われ方：元の底変換 Hom 輸送の底の制限に関する自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 共通 Hom の上で整合する二つの輸送の正方形は、元の作用の関手同型で可換。 -/
def homTransportSquareCoherence
    {H₀ H₁ X₀ X₁ Y₀ Y₁ : SSet.{u}}
    [Quasicategory H₀] [Quasicategory H₁] [Quasicategory X₀] [Quasicategory X₁]
    [Quasicategory Y₀] [Quasicategory Y₁]
    (p₀ : H₀ ⟶ X₀) (p₁ : H₀ ⟶ X₁) (q₀ : H₁ ⟶ Y₀) (q₁ : H₁ ⟶ Y₁) (r : H₀ ⟶ H₁)
    (t₀ : X₁ ⟶ X₀) (t₁ : Y₁ ⟶ Y₀) (u₀ : X₀ ⟶ Y₀) (u₁ : X₁ ⟶ Y₁)
    (hp₁ : IsQCatEquivalence p₁)
    (e₀ : FunctorIso (p₁ ≫ t₀) p₀) (e₁ : FunctorIso (q₁ ≫ t₁) q₀)
    (h₀ : FunctorIso (p₀ ≫ u₀) (r ≫ q₀))
    (h₁ : FunctorIso (p₁ ≫ u₁) (r ≫ q₁)) :
    FunctorIso (t₀ ≫ u₀) (u₁ ≫ t₁) := by
  apply (hp₁.precompose Y₀).isFullyFaithful.preimageVertexIso
  change FunctorIso (p₁ ≫ (t₀ ≫ u₀)) (p₁ ≫ (u₁ ≫ t₁))
  have e := e₀.postcomp u₀ ≪≫ h₀ ≪≫ (e₁.precomp r).symm ≪≫ FunctorIso.postcomp h₁.symm t₁
  simpa only [Category.assoc] using e

/-- 同じ二つの span の指定切断による輸送は、元の厳密な span の射に関して自然。 -/
def homSpanSectionTransportNaturalityIso
    {H₀ H₁ X₀ X₁ Y₀ Y₁ : SSet.{u}}
    [Quasicategory H₀] [Quasicategory H₁] [Quasicategory X₀] [Quasicategory X₁]
    [Quasicategory Y₀] [Quasicategory Y₁]
    (p₀ : H₀ ⟶ X₀) (p₁ : H₀ ⟶ X₁) (q₀ : H₁ ⟶ Y₀) (q₁ : H₁ ⟶ Y₁) (r : H₀ ⟶ H₁)
    (s₀ : X₁ ⟶ H₀) (s₁ : Y₁ ⟶ H₁) (u₀ : X₀ ⟶ Y₀) (u₁ : X₁ ⟶ Y₁)
    (hp₁ : IsQCatEquivalence p₁) (hq₁ : IsFullyFaithful q₁)
    (hs₀ : s₀ ≫ p₁ = 𝟙 _) (hs₁ : s₁ ≫ q₁ = 𝟙 _)
    (h₀ : p₀ ≫ u₀ = r ≫ q₀) (h₁ : p₁ ≫ u₁ = r ≫ q₁) :
    FunctorIso ((s₀ ≫ p₀) ≫ u₀) (u₁ ≫ (s₁ ≫ q₀)) := by
  apply homTransportSquareCoherence p₀ p₁ q₀ q₁ r (s₀ ≫ p₀) (s₁ ≫ q₀) u₀ u₁ hp₁
  · simpa only [Category.id_comp] using
      homSpanSectionTransportFactorIso p₁ p₀ s₀ hp₁.isFullyFaithful hs₀ (𝟙 H₀)
  · simpa only [Category.id_comp] using
      homSpanSectionTransportFactorIso q₁ q₀ s₁ hq₁ hs₁ (𝟙 H₁)
  · exact eqToIso (congrArg (fun f : H₀ ⟶ Y₀ ↦ SSet.HomotopyCategory.mk (functorVertex f)) h₀)
  · exact eqToIso (congrArg (fun f : H₀ ⟶ Y₁ ↦ SSet.HomotopyCategory.mk (functorVertex f)) h₁)

end SerrePositivity.InfinityCategories
