module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwoMappedPartialConditions

/-!
概要：二つの像の所属条件を満たす小部分表示族は、μ-filtered かつ元の部分表示族に共終。
方針：小さい族の和を種集合に取り、同時細分で上界を構成する。
規約：同じ元の部分集合と実部分余錐条件を使う。使われ方：二辺を揃えた全三角形表示。

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
variable {μ : Cardinal.{u}} {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
  (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges)
  {T : SSet.{u + 1}} [Quasicategory T]
  (H₀ H₁ : T ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj C)
  {J : Type u} [PartialOrder J]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ T)

/-- 元の二つの像の実部分余極限が実像に属す、小さい filtered 部分集合の族。 -/
def TwoMappedPartialPieces :=
  {P : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J //
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HasPropertyPartialColimit (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (H₀.app _ t)) D P ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HasPropertyPartialColimit (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (H₁.app _ t)) D P}

instance twoMappedPartialPieces_partialOrder :
    PartialOrder (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwoMappedPartialPieces edges G H₀ H₁ D) := inferInstanceAs
  (PartialOrder {P : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J //
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HasPropertyPartialColimit (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (H₀.app _ t)) D P ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HasPropertyPartialColimit (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (H₁.app _ t)) D P})

/-- 元の同じ小部分集合への包含順射影。 -/
def twoMappedPartialPieceProjection : Monotone
    (Subtype.val : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwoMappedPartialPieces edges G H₀ H₁ D →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) := fun _ _ h ↦ h

variable [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
  (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
  (hcompact : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A ≫ G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion edges).app _ (ULift.up a)))
  (hcol : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageCategory edges G))
  (hpres : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageInclusion edges G))
  (hT : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits T)
  (hH₀ : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits H₀) (hH₁ : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits H₁)
  [IsCardinalFiltered J μ] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (nerve J)]
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (hD₀ : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((D ≫ H₀).app _ (ULift.up j)))
  (hD₁ : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((D ≫ H₁).app _ (ULift.up j)))
  (hf₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (H₀.app _ c.vertex))
  (hf₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (H₁.app _ c.vertex))
include hμ hC hG hcompact hcol hpres hT hH₀ hH₁ c hc hD₀ hD₁ hf₀ hf₁

/-- 任意の小部分表示は、同じ二条件を満たす部分表示へ実際に拡大できる。 -/
lemma exists_twoMappedPartialPiece_above (P : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) :
    ∃ Q : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwoMappedPartialPieces edges G H₀ H₁ D, P ≤ Q.val := by
  obtain ⟨Q, hPQ, hQ₀, hQ₁⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_twoMappedPartialConditions hμ edges hC G hG hcompact
    hcol hpres hT H₀ H₁ hH₀ hH₁ c hc hD₀ hD₁ hf₀ hf₁ P
  exact ⟨⟨Q, hQ₀, hQ₁⟩, hPQ⟩

/-- 二条件を満たす同じ部分集合族の包含順は μ-filtered。 -/
lemma twoMappedPartialPieces_isCardinalFiltered :
    IsCardinalFiltered (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwoMappedPartialPieces edges G H₀ H₁ D) μ := by
  apply isCardinalFiltered_preorder
  intro K f hK
  have hK' : HasCardinalLT K μ := (hasCardinalLT_iff_cardinal_mk_lt K μ).mpr hK
  have hU : HasCardinalLT (⋃ k, (f k).val.val) μ :=
    hasCardinalLT_iUnion _ hK' (fun k ↦ (f k).val.property.2)
  have : IsCardinalFiltered J Cardinal.aleph0.{u} := IsCardinalFiltered.of_le J hμ.le
  obtain ⟨P, hP⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_smallFilteredPiece_containing (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalChangeBound_aleph0 hμ) _ hU
  obtain ⟨Q, hPQ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_twoMappedPartialPiece_above edges G H₀ H₁ D hμ hC hG hcompact
    hcol hpres hT hH₀ hH₁ c hc hD₀ hD₁ hf₀ hf₁ P
  refine ⟨Q, fun k ↦ ?_⟩
  exact ((Set.subset_iUnion (fun k ↦ (f k).val.val) k).trans hP).trans hPQ

/-- 二条件を満たす同じ部分表示族の nerve は native に μ-filtered。 -/
lemma twoMappedPartialPieces_nerve_isKappaFiltered :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (nerve (TwoMappedPartialPieces edges G H₀ H₁ D)) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twoMappedPartialPieces_isCardinalFiltered edges G H₀ H₁ D hμ hC hG hcompact
    hcol hpres hT hH₀ hH₁ c hc hD₀ hD₁ hf₀ hf₁
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered _

/-- 元の二条件を満たす部分表示から全小部分表示族への射影は native に right cofinal。 -/
lemma twoMappedPartialPieceProjection_nerve_isRightCofinal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap (twoMappedPartialPieceProjection edges G H₀ H₁ D).functor) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twoMappedPartialPieces_isCardinalFiltered edges G H₀ H₁ D hμ hC hG hcompact
    hcol hpres hT hH₀ hH₁ c hc hD₀ hD₁ hf₀ hf₁
  have : IsFiltered (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwoMappedPartialPieces edges G H₀ H₁ D) :=
    isFiltered_of_isCardinalFiltered _ μ
  have := IsFiltered.isDirectedOrder (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwoMappedPartialPieces edges G H₀ H₁ D)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.monotone_nerveMap_isRightCofinal
    (P := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwoMappedPartialPieces edges G H₀ H₁ D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twoMappedPartialPieceProjection edges G H₀ H₁ D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_twoMappedPartialPiece_above edges G H₀ H₁ D hμ hC hG hcompact
      hcol hpres hT hH₀ hH₁ c hc hD₀ hD₁ hf₀ hf₁)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
