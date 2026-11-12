module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePieceColimitIso

/-!
概要：一方の表示の全段が閉じたクラスに属すれば、他方にも同じクラスの小部分余極限がある。
方針：指定種集合を含む比較対を構成し、実部分余極限の同型で所属を移す。
規約：同型閉性と小 poset 余極限閉性を明示する。使われ方：実像に属す三角形の一辺の細分。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativeSmallPresentationPiece

local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩

/-- 任意の小さい種集合を含む、指定した閉じたクラス内の実部分余極限が存在する。 -/
lemma exists_relativeSmallPresentationPiece
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C] {A₀ A₁ : Type u}
    [PartialOrder A₀] [PartialOrder A₁]
    [IsCardinalFiltered A₀ μ] [IsCardinalFiltered A₁ μ]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (nerve A₀)] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (nerve A₁)]
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₀) ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₁) ⟶ C}
    (c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀) (c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁) (hv : c₀.vertex = c₁.vertex)
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hc₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₀) (hc₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₁)
    (hD₀ : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
    (hD₁ : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
    (W : C _⦋0⦌ → Prop)
    (hiso : ∀ {x y}, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y → (W x ↔ W y))
    (hclosed : ∀ (J : Type u) [PartialOrder J]
      (E : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ C),
      (∀ k, W (E.app (Opposite.op ⦋0⦌) k)) →
      ∀ a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone E, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a → W a.vertex)
    (hW : ∀ k, W (D₁.app (Opposite.op ⦋0⦌) k))
    (seed : Set A₀) (hs : HasCardinalLT seed μ) :
    ∃ (P : Set A₀), seed ⊆ P ∧ HasCardinalLT P μ ∧ IsFiltered P ∧
      ∃ a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion P)) ≫ D₀), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a ∧ W a.vertex := by
  obtain ⟨P, hseed, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_compatiblePresentationPiece_containing μ c₀ c₁ hv hμ
    hC hc₀ hc₁ hD₀ hD₁ seed hs ∅ (hasCardinalLT_of_finite _ _ hμ.le)
  obtain ⟨a₀, ha₀⟩ := hC _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredPartialDiagram D₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePieceProjections.compatibleLeftPiece P))
  obtain ⟨a₁, ha₁⟩ := hC _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredPartialDiagram D₁ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePieceProjections.compatibleRightPiece P))
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePieceColimitIso.nonempty_compatiblePiece_colimitVertexIso hC P a₀ ha₀ a₁ ha₁
  have hm : W a₁.vertex := hclosed _ _ (fun k ↦
    hW (((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion P.val.2))).app _ k)) a₁ ha₁
  exact ⟨P.val.1, hseed, P.property.1, P.property.2.2.1,
    a₀, ha₀, (hiso e).mpr hm⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativeSmallPresentationPiece
