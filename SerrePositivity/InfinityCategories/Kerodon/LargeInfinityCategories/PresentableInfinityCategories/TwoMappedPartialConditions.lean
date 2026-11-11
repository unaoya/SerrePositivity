module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImageMappedPartialConditions

/-!
概要：二つの余極限保存関手の像が実像に属す場合、同じ小部分表示で両条件を満たす。
方針：各条件の実拡大と増大可算和閉性を、交互細分の共通和へ適用する。
規約：元の同じ全図式の部分余極限を使う。使われ方：三角形の二辺の同時細分。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩

/-- 元の二つの大域像の所属から、同じ小部分表示の両像の所属を構成する。 -/
lemma exists_twoMappedPartialConditions
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    {I : Type u} (edges : I → C _⦋1⦌) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A ≫ G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges).app _ (ULift.up a)))
    (hcol : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageCategory edges G))
    (hpres : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageInclusion edges G))
    {T : SSet.{u + 1}} [Quasicategory T] (hT : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits T)
    (H₀ H₁ : T ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj C)
    (hH₀ : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits H₀) (hH₁ : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits H₁)
    {J : Type u} [PartialOrder J] [IsCardinalFiltered J μ] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (nerve J)]
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ T}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (hD₀ : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((D ≫ H₀).app _ (ULift.up j)))
    (hD₁ : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((D ≫ H₁).app _ (ULift.up j)))
    (hf₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (H₀.app _ c.vertex))
    (hf₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (H₁.app _ c.vertex))
    (P : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) :
    ∃ Q, P ≤ Q ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HasPropertyPartialColimit (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (H₀.app _ t)) D Q ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HasPropertyPartialColimit (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (H₁.app _ t)) D Q := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CommonRefinementConditions.exists_commonRefinementConditions hμ _ _ ?_ ?_ ?_ ?_ P
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImageMappedPartialConditions.exists_mappedIndImagePartialCondition_extension
      (edges := edges) (G := G) (hcol := hcol) (hpres := hpres)
      (hT := hT) (H := H₀) (hH := hH₀) (D := D)
      hμ hC hG hcompact c hc hD₀ hf₀
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImageMappedPartialConditions.exists_mappedIndImagePartialCondition_extension
      (edges := edges) (G := G) (hcol := hcol) (hpres := hpres)
      (hT := hT) (H := H₁) (hH := hH₁) (D := D)
      hμ hC hG hcompact c hc hD₁ hf₁
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImageMappedPartialConditions.mappedIndImagePartialCondition_sequenceUnion
      (edges := edges) (G := G) (hcol := hcol) (hpres := hpres)
      (hT := hT) (H := H₀) (hH := hH₀) (D := D) hμ
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImageMappedPartialConditions.mappedIndImagePartialCondition_sequenceUnion
      (edges := edges) (G := G) (hcol := hcol) (hpres := hpres)
      (hT := hT) (H := H₁) (hH := hH₁) (D := D) hμ

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
