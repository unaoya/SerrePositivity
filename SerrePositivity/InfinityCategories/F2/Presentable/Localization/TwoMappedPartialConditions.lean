module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageMappedPartialConditions

/-!
概要：二つの余極限保存関手の像が実像に属す場合、同じ小部分表示で両条件を満たす。
方針：各条件の実拡大と増大可算和閉性を、交互細分の共通和へ適用する。
規約：元の同じ全図式の部分余極限を使う。使われ方：三角形の二辺の同時細分。
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

/-- 元の二つの大域像の所属から、同じ小部分表示の両像の所属を構成する。 -/
lemma exists_twoMappedPartialConditions
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    {I : Type u} (edges : I → C _⦋1⦌) (hC : HasSmallColimits C)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hG : IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, IsKappaCompact.{u, u + 1} μ
      ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
    (hcol : HasSmallColimits (indArrowImageCategory edges G))
    (hpres : PreservesSmallColimits (indArrowImageInclusion edges G))
    {T : SSet.{u + 1}} [Quasicategory T] (hT : HasSmallColimits T)
    (H₀ H₁ : T ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj C)
    (hH₀ : PreservesSmallColimits H₀) (hH₁ : PreservesSmallColimits H₁)
    {J : Type u} [PartialOrder J] [IsCardinalFiltered J μ] [IsKappaFiltered μ (nerve J)]
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ T}
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hD₀ : ∀ j, IsKappaCompact.{u, u + 1} μ ((D ≫ H₀).app _ (ULift.up j)))
    (hD₁ : ∀ j, IsKappaCompact.{u, u + 1} μ ((D ≫ H₁).app _ (ULift.up j)))
    (hf₀ : IndArrowImageVertex edges G (H₀.app _ c.vertex))
    (hf₁ : IndArrowImageVertex edges G (H₁.app _ c.vertex))
    (P : SmallFilteredPieces Cardinal.aleph0 μ J) :
    ∃ Q, P ≤ Q ∧
      HasPropertyPartialColimit (fun t ↦ IndArrowImageVertex edges G (H₀.app _ t)) D Q ∧
      HasPropertyPartialColimit (fun t ↦ IndArrowImageVertex edges G (H₁.app _ t)) D Q := by
  apply exists_commonRefinementConditions hμ _ _ ?_ ?_ ?_ ?_ P
  · exact exists_mappedIndImagePartialCondition_extension
      (edges := edges) (G := G) (hcol := hcol) (hpres := hpres)
      (hT := hT) (H := H₀) (hH := hH₀) (D := D)
      hμ hC hG hcompact c hc hD₀ hf₀
  · exact exists_mappedIndImagePartialCondition_extension
      (edges := edges) (G := G) (hcol := hcol) (hpres := hpres)
      (hT := hT) (H := H₁) (hH := hH₁) (D := D)
      hμ hC hG hcompact c hc hD₁ hf₁
  · exact mappedIndImagePartialCondition_sequenceUnion
      (edges := edges) (G := G) (hcol := hcol) (hpres := hpres)
      (hT := hT) (H := H₀) (hH := hH₀) (D := D) hμ
  · exact mappedIndImagePartialCondition_sequenceUnion
      (edges := edges) (G := G) (hcol := hcol) (hpres := hpres)
      (hT := hT) (H := H₁) (hH := hH₁) (D := D) hμ

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
