module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.TwoMappedPartialPieces
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.PartialFamilyValues

/-!
概要：二つの大域像が実像に属す全図式を、二条件が各段で成立する同じ μ-filtered 全表示へ細分する。
方針：同時細分条件の部分集合族の共終射影に、coherent な部分余極限族を制限する。
規約：第三の保存像の compact 性と元の大域頂点も保持。使われ方：実像の全二対三則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact
local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩

/-- 元の全図式から、二つの実像条件と第三像の compact 性を各段で保つ全細分表示が存在する。 -/
lemma exists_twoMappedRefinementPresentation
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    {I : Type u} (edges : I → C _⦋1⦌) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, IsKappaCompact.{u, u + 1} μ
      ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
    (hcol : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (indArrowImageCategory edges G))
    (hpres : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (indArrowImageInclusion edges G))
    {T : SSet.{u + 1}} [Quasicategory T] (hT : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits T)
    (H₀ H₁ H₂ : T ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj C)
    (hH₀ : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits H₀) (hH₁ : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits H₁)
    (hH₂ : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits H₂)
    {J : Type u} [PartialOrder J] [IsCardinalFiltered J μ] [IsKappaFiltered μ (nerve J)]
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ T}
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hD₀ : ∀ j, IsKappaCompact.{u, u + 1} μ ((D ≫ H₀).app _ (ULift.up j)))
    (hD₁ : ∀ j, IsKappaCompact.{u, u + 1} μ ((D ≫ H₁).app _ (ULift.up j)))
    (hD₂ : ∀ k, IsKappaCompact.{u, u + 1} μ ((D ≫ H₂).app _ k))
    (hf₀ : IndArrowImageVertex edges G (H₀.app _ c.vertex))
    (hf₁ : IndArrowImageVertex edges G (H₁.app _ c.vertex)) :
    ∃ F : (SSet.uliftFunctor.{u + 1, u}).obj
        (nerve (TwoMappedPartialPieces edges G H₀ H₁ D)) ⟶ T,
      IsKappaFiltered μ (nerve (TwoMappedPartialPieces edges G H₀ H₁ D)) ∧
      (∀ k, IndArrowImageVertex edges G ((F ≫ H₀).app _ k)) ∧
      (∀ k, IndArrowImageVertex edges G ((F ≫ H₁).app _ k)) ∧
      (∀ k, IsKappaCompact.{u, u + 1} μ ((F ≫ H₂).app _ k)) ∧
      ∃ d : JoinCocone F, IsColimitCone d ∧ d.vertex = c.vertex := by
  have : IsCardinalFiltered J Cardinal.aleph0.{u} := IsCardinalFiltered.of_le J hμ.le
  have hp := twoMappedPartialPieceProjection_nerve_isRightCofinal edges G H₀ H₁ D
    hμ hC hG hcompact hcol hpres hT hH₀ hH₁ c hc hD₀ hD₁ hf₀ hf₁
  obtain ⟨F, hF, d, hd, hv⟩ := exists_cofinalSmallPartialColimitFamily hμ hT c hc
    (twoMappedPartialPieceProjection edges G H₀ H₁ D) hp
  refine ⟨F, twoMappedPartialPieces_nerve_isKappaFiltered edges G H₀ H₁ D
    hμ hC hG hcompact hcol hpres hT hH₀ hH₁ c hc hD₀ hD₁ hf₀ hf₁,
    ?_, ?_, ?_, d, hd, hv⟩
  · exact partialFamily_values_property _
      (fun e ↦ indArrowImageVertex_iff_vertexIso edges G (e.map H₀))
      Subtype.val F hF (fun b ↦ b.property.1)
  · exact partialFamily_values_property _
      (fun e ↦ indArrowImageVertex_iff_vertexIso edges G (e.map H₁))
      Subtype.val F hF (fun b ↦ b.property.2)
  · exact partialFamily_mapped_values_compact hμ H₂ hH₂ hD₂ Subtype.val F hF

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
