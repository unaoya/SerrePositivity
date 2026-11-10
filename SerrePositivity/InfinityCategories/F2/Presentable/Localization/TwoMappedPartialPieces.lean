module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.TwoMappedPartialConditions

/-!
概要：二つの像の所属条件を満たす小部分表示族は、μ-filtered かつ元の部分表示族に共終。
方針：小さい族の和を種集合に取り、同時細分で上界を構成する。
規約：同じ元の部分集合と実部分余錐条件を使う。使われ方：二辺を揃えた全三角形表示。
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
variable {μ : Cardinal.{u}} {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
  (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
  {T : SSet.{u + 1}} [Quasicategory T]
  (H₀ H₁ : T ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj C)
  {J : Type u} [PartialOrder J]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ T)

/-- 元の二つの像の実部分余極限が実像に属す、小さい filtered 部分集合の族。 -/
def TwoMappedPartialPieces :=
  {P : SmallFilteredPieces Cardinal.aleph0 μ J //
    HasPropertyPartialColimit (fun t ↦ IndArrowImageVertex edges G (H₀.app _ t)) D P ∧
    HasPropertyPartialColimit (fun t ↦ IndArrowImageVertex edges G (H₁.app _ t)) D P}

instance twoMappedPartialPieces_partialOrder :
    PartialOrder (TwoMappedPartialPieces edges G H₀ H₁ D) := inferInstanceAs
  (PartialOrder {P : SmallFilteredPieces Cardinal.aleph0 μ J //
    HasPropertyPartialColimit (fun t ↦ IndArrowImageVertex edges G (H₀.app _ t)) D P ∧
    HasPropertyPartialColimit (fun t ↦ IndArrowImageVertex edges G (H₁.app _ t)) D P})

/-- 元の同じ小部分集合への包含順射影。 -/
def twoMappedPartialPieceProjection : Monotone
    (Subtype.val : TwoMappedPartialPieces edges G H₀ H₁ D →
      SmallFilteredPieces Cardinal.aleph0 μ J) := fun _ _ h ↦ h

variable [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
  (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
  (hcompact : ∀ a : A _⦋0⦌, IsKappaCompact.{u, u + 1} μ
    ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
  (hcol : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (indArrowImageCategory edges G))
  (hpres : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (indArrowImageInclusion edges G))
  (hT : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits T)
  (hH₀ : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits H₀) (hH₁ : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits H₁)
  [IsCardinalFiltered J μ] [IsKappaFiltered μ (nerve J)]
  (c : JoinCocone D) (hc : IsColimitCone c)
  (hD₀ : ∀ j, IsKappaCompact.{u, u + 1} μ ((D ≫ H₀).app _ (ULift.up j)))
  (hD₁ : ∀ j, IsKappaCompact.{u, u + 1} μ ((D ≫ H₁).app _ (ULift.up j)))
  (hf₀ : IndArrowImageVertex edges G (H₀.app _ c.vertex))
  (hf₁ : IndArrowImageVertex edges G (H₁.app _ c.vertex))
include hμ hC hG hcompact hcol hpres hT hH₀ hH₁ c hc hD₀ hD₁ hf₀ hf₁

/-- 任意の小部分表示は、同じ二条件を満たす部分表示へ実際に拡大できる。 -/
lemma exists_twoMappedPartialPiece_above (P : SmallFilteredPieces Cardinal.aleph0 μ J) :
    ∃ Q : TwoMappedPartialPieces edges G H₀ H₁ D, P ≤ Q.val := by
  obtain ⟨Q, hPQ, hQ₀, hQ₁⟩ := exists_twoMappedPartialConditions hμ edges hC G hG hcompact
    hcol hpres hT H₀ H₁ hH₀ hH₁ c hc hD₀ hD₁ hf₀ hf₁ P
  exact ⟨⟨Q, hQ₀, hQ₁⟩, hPQ⟩

/-- 二条件を満たす同じ部分集合族の包含順は μ-filtered。 -/
lemma twoMappedPartialPieces_isCardinalFiltered :
    IsCardinalFiltered (TwoMappedPartialPieces edges G H₀ H₁ D) μ := by
  apply isCardinalFiltered_preorder
  intro K f hK
  have hK' : HasCardinalLT K μ := (hasCardinalLT_iff_cardinal_mk_lt K μ).mpr hK
  have hU : HasCardinalLT (⋃ k, (f k).val.val) μ :=
    hasCardinalLT_iUnion _ hK' (fun k ↦ (f k).val.property.2)
  have : IsCardinalFiltered J Cardinal.aleph0.{u} := IsCardinalFiltered.of_le J hμ.le
  obtain ⟨P, hP⟩ := exists_smallFilteredPiece_containing (cardinalChangeBound_aleph0 hμ) _ hU
  obtain ⟨Q, hPQ⟩ := exists_twoMappedPartialPiece_above edges G H₀ H₁ D hμ hC hG hcompact
    hcol hpres hT hH₀ hH₁ c hc hD₀ hD₁ hf₀ hf₁ P
  refine ⟨Q, fun k ↦ ?_⟩
  exact ((Set.subset_iUnion (fun k ↦ (f k).val.val) k).trans hP).trans hPQ

/-- 二条件を満たす同じ部分表示族の nerve は native に μ-filtered。 -/
lemma twoMappedPartialPieces_nerve_isKappaFiltered :
    IsKappaFiltered μ (nerve (TwoMappedPartialPieces edges G H₀ H₁ D)) := by
  have := twoMappedPartialPieces_isCardinalFiltered edges G H₀ H₁ D hμ hC hG hcompact
    hcol hpres hT hH₀ hH₁ c hc hD₀ hD₁ hf₀ hf₁
  exact Ind.isKappaFiltered_nerve_of_cardinalFiltered _

/-- 元の二条件を満たす部分表示から全小部分表示族への射影は native に right cofinal。 -/
lemma twoMappedPartialPieceProjection_nerve_isRightCofinal :
    IsRightCofinal (nerveMap (twoMappedPartialPieceProjection edges G H₀ H₁ D).functor) := by
  have := twoMappedPartialPieces_isCardinalFiltered edges G H₀ H₁ D hμ hC hG hcompact
    hcol hpres hT hH₀ hH₁ c hc hD₀ hD₁ hf₀ hf₁
  have : IsFiltered (TwoMappedPartialPieces edges G H₀ H₁ D) :=
    isFiltered_of_isCardinalFiltered _ μ
  have := IsFiltered.isDirectedOrder (TwoMappedPartialPieces edges G H₀ H₁ D)
  exact monotone_nerveMap_isRightCofinal
    (P := TwoMappedPartialPieces edges G H₀ H₁ D)
    (twoMappedPartialPieceProjection edges G H₀ H₁ D)
    (exists_twoMappedPartialPiece_above edges G H₀ H₁ D hμ hC hG hcompact
      hcol hpres hT hH₀ hH₁ c hc hD₀ hD₁ hf₀ hf₁)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
