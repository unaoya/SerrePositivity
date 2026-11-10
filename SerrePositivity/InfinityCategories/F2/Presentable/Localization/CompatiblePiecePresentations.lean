module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CofinalPartialColimitFamilies

/-!
概要：元の二表示を、同じ μ-filtered な比較可能部分表示対の上で再表示する。
方針：両共終射影に沿って公開の部分余極限族を制限する。
規約：両大域頂点と各値の実部分余錐を保持。使われ方：同時細分の二表示側の入力。
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
local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩

/-- 両元の大域頂点は、同じ比較可能部分表示対の nerve 上の compact 表示を持つ。 -/
lemma exists_compatiblePiecePresentations
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C] {A₀ A₁ : Type u}
    [PartialOrder A₀] [PartialOrder A₁]
    [IsCardinalFiltered A₀ μ] [IsCardinalFiltered A₁ μ]
    [IsKappaFiltered μ (nerve A₀)] [IsKappaFiltered μ (nerve A₁)]
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₀) ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₁) ⟶ C}
    (c₀ : JoinCocone D₀) (c₁ : JoinCocone D₁) (hv : c₀.vertex = c₁.vertex)
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hc₀ : IsColimitCone c₀) (hc₁ : IsColimitCone c₁)
    (hD₀ : ∀ i, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
    (hD₁ : ∀ i, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i))) :
    let B := CompatiblePresentationPieces μ c₀ c₁ hv
    ∃ F₀ F₁ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve B) ⟶ C,
      IsKappaFiltered μ (nerve B) ∧
      (∀ k, IsKappaCompact.{u, u + 1} μ (F₀.app (Opposite.op ⦋0⦌) k)) ∧
      (∀ k, IsKappaCompact.{u, u + 1} μ (F₁.app (Opposite.op ⦋0⦌) k)) ∧
      (∀ P, ∃ a : JoinCocone (smallFilteredPartialDiagram D₀ (compatibleLeftPiece P)),
        IsColimitCone a ∧ a.vertex = F₀.app _ (ULift.up (nerveVertex P))) ∧
      (∀ P, ∃ a : JoinCocone (smallFilteredPartialDiagram D₁ (compatibleRightPiece P)),
        IsColimitCone a ∧ a.vertex = F₁.app _ (ULift.up (nerveVertex P))) ∧
      ∃ d₀ : JoinCocone F₀, ∃ d₁ : JoinCocone F₁,
        IsColimitCone d₀ ∧ IsColimitCone d₁ ∧
        d₀.vertex = c₀.vertex ∧ d₁.vertex = c₁.vertex := by
  dsimp only
  have : IsCardinalFiltered A₀ Cardinal.aleph0.{u} := IsCardinalFiltered.of_le A₀ hμ.le
  have : IsCardinalFiltered A₁ Cardinal.aleph0.{u} := IsCardinalFiltered.of_le A₁ hμ.le
  obtain ⟨F₀, hF₀, d₀, hd₀, hv₀⟩ := exists_cofinalSmallPartialColimitFamily hμ hC c₀ hc₀
    (compatibleLeftPiece_monotone (c₀ := c₀) (c₁ := c₁) (hv := hv))
    (compatibleLeftPiece_nerve_isRightCofinal hμ hC hc₀ hc₁ hD₀ hD₁)
  obtain ⟨F₁, hF₁, d₁, hd₁, hv₁⟩ := exists_cofinalSmallPartialColimitFamily hμ hC c₁ hc₁
    (compatibleRightPiece_monotone (c₀ := c₀) (c₁ := c₁) (hv := hv))
    (compatibleRightPiece_nerve_isRightCofinal hμ hC hc₀ hc₁ hD₀ hD₁)
  refine ⟨F₀, F₁,
    compatiblePresentationPieces_nerve_isKappaFiltered μ c₀ c₁ hv hμ hC hc₀ hc₁ hD₀ hD₁,
    ?_, ?_, hF₀, hF₁, d₀, d₁, hd₀, hd₁, hv₀, hv₁⟩
  · exact cofinalSmallPartialColimitFamily_values_compact hμ
      (fun k ↦ hD₀ k.down) compatibleLeftPiece F₀ hF₀
  · exact cofinalSmallPartialColimitFamily_values_compact hμ
      (fun k ↦ hD₁ k.down) compatibleRightPiece F₁ hF₁

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
