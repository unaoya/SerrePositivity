module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.PartialColimitProperty
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageMappedRelativePiece

/-!
概要：実像への所属を課す部分余極限条件は増大可算和で閉じ、任意の種から拡大できる。
方針：保存関手で部分余錐を写し、実像の小余極限閉性と相対部分細分を使う。
規約：元の図式の実余錐を条件とする。使われ方：三角形の二辺の同時部分細分。
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
variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
  (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
  (hcol : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (indArrowImageCategory edges G))
  (hpres : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (indArrowImageInclusion edges G))
  {T : SSet.{u + 1}} [Quasicategory T] (hT : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits T)
  (H : T ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj C) (hH : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits H)
  {J : Type u} [PartialOrder J]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ T)

include hcol hpres hT hH

/-- 保存関手の像に実像所属を課した部分余極限条件は、増大列の和で閉じる。 -/
lemma mappedIndImagePartialCondition_sequenceUnion (hμ : Cardinal.aleph0 < μ)
    (P : ℕ → SmallFilteredPieces Cardinal.aleph0 μ J) (hP : Monotone P)
    (hmem : ∀ n, HasPropertyPartialColimit (fun t ↦ IndArrowImageVertex edges G (H.app _ t))
      D (P n)) :
    HasPropertyPartialColimit (fun t ↦ IndArrowImageVertex edges G (H.app _ t))
      D (filteredPieceSequenceUnionPiece hμ P hP) := by
  apply hasPropertyPartialColimit_sequenceUnion hμ _
    (fun e ↦ indArrowImageVertex_iff_vertexIso edges G (e.map H)) ?_ hT D P hP hmem
  intro K E hE a ha
  have hm := indArrowImage_ambientSmall_colimit_mem edges G hcol hpres K (E ≫ H) hE
    (mapJoinCocone H a) (hH K E a ha)
  rwa [Ind.mapJoinCocone_vertex] at hm

/-- 元の大域像が実像に属せば、任意の小部分表示をこの所属条件へ拡大できる。 -/
lemma exists_mappedIndImagePartialCondition_extension
    (hμ : Cardinal.aleph0 < μ) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, IsKappaCompact.{u, u + 1} μ
      ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
    [IsCardinalFiltered J μ] [IsKappaFiltered μ (nerve J)]
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hD : ∀ j, IsKappaCompact.{u, u + 1} μ ((D ≫ H).app _ (ULift.up j)))
    (hf : IndArrowImageVertex edges G (H.app _ c.vertex))
    (P : SmallFilteredPieces Cardinal.aleph0 μ J) :
    ∃ Q, P ≤ Q ∧ HasPropertyPartialColimit
      (fun t ↦ IndArrowImageVertex edges G (H.app _ t)) D Q := by
  obtain ⟨Q, hPQ, hsmall, hfiltered, a, ha, hm⟩ :=
    indArrowImage_exists_mappedSmallPartialPiece hμ edges hC G hG hcompact hcol hpres
      hT H hH c hc hD hf P.val P.property.2
  exact ⟨⟨Q, (isCardinalFiltered_aleph0_iff Q).mpr hfiltered, hsmall⟩,
    hPQ, a, ha, hm⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
