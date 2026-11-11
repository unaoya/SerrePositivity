module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomSpanSectionBoundaryIso

/-!
概要：同じ Hom 比較 span の指定された輸送は、span の射に関して自然。
方針：元の共通 Hom で二つの作用を比較し、同値な一射影の前合成で検出する。
規約：指定された元の輸送と切断を選び直さない。
使われ方：元の底変換 Hom 輸送の底の制限に関する自然性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 共通 Hom の上で整合する二つの輸送の正方形は、元の作用の関手同型で可換。 -/
def homTransportSquareCoherence
    {H₀ H₁ X₀ X₁ Y₀ Y₁ : SSet.{u}}
    [Quasicategory H₀] [Quasicategory H₁] [Quasicategory X₀] [Quasicategory X₁]
    [Quasicategory Y₀] [Quasicategory Y₁]
    (p₀ : H₀ ⟶ X₀) (p₁ : H₀ ⟶ X₁) (q₀ : H₁ ⟶ Y₀) (q₁ : H₁ ⟶ Y₁) (r : H₀ ⟶ H₁)
    (t₀ : X₁ ⟶ X₀) (t₁ : Y₁ ⟶ Y₀) (u₀ : X₀ ⟶ Y₀) (u₁ : X₁ ⟶ Y₁)
    (hp₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence p₁)
    (e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p₁ ≫ t₀) p₀) (e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q₁ ≫ t₁) q₀)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p₀ ≫ u₀) (r ≫ q₀))
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p₁ ≫ u₁) (r ≫ q₁)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (t₀ ≫ u₀) (u₁ ≫ t₁) := by
  apply (hp₁.precompose Y₀).isFullyFaithful.preimageVertexIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p₁ ≫ (t₀ ≫ u₀)) (p₁ ≫ (u₁ ≫ t₁))
  have e := e₀.postcomp u₀ ≪≫ h₀ ≪≫ (e₁.precomp r).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp h₁.symm t₁
  simpa only [Category.assoc] using e

/-- 同じ二つの span の指定切断による輸送は、元の厳密な span の射に関して自然。 -/
def homSpanSectionTransportNaturalityIso
    {H₀ H₁ X₀ X₁ Y₀ Y₁ : SSet.{u}}
    [Quasicategory H₀] [Quasicategory H₁] [Quasicategory X₀] [Quasicategory X₁]
    [Quasicategory Y₀] [Quasicategory Y₁]
    (p₀ : H₀ ⟶ X₀) (p₁ : H₀ ⟶ X₁) (q₀ : H₁ ⟶ Y₀) (q₁ : H₁ ⟶ Y₁) (r : H₀ ⟶ H₁)
    (s₀ : X₁ ⟶ H₀) (s₁ : Y₁ ⟶ H₁) (u₀ : X₀ ⟶ Y₀) (u₁ : X₁ ⟶ Y₁)
    (hp₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence p₁) (hq₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful q₁)
    (hs₀ : s₀ ≫ p₁ = 𝟙 _) (hs₁ : s₁ ≫ q₁ = 𝟙 _)
    (h₀ : p₀ ≫ u₀ = r ≫ q₀) (h₁ : p₁ ≫ u₁ = r ≫ q₁) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((s₀ ≫ p₀) ≫ u₀) (u₁ ≫ (s₁ ≫ q₀)) := by
  apply homTransportSquareCoherence p₀ p₁ q₀ q₁ r (s₀ ≫ p₀) (s₁ ≫ q₀) u₀ u₁ hp₁
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionBoundaryIso p₁ p₀ s₀ hp₁.isFullyFaithful hs₀
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homSpanSectionBoundaryIso q₁ q₀ s₁ hq₁ hs₁
  · exact eqToIso (congrArg (fun f : H₀ ⟶ Y₀ ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) h₀)
  · exact eqToIso (congrArg (fun f : H₀ ⟶ Y₁ ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) h₁)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
