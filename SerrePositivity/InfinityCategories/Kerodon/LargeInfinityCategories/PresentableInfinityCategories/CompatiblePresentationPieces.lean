module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPresentationComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredPosetNerve

/-!
概要：共通大域頂点上で余極限が同型な、小部分表示の対の包含順を定める。
方針：任意の μ-small な両種集合を含む比較対を構成し、族の和を支配する。
規約：部分表示の実余錐と同型の存在を条件とする。使われ方：二表示の μ-filtered 同時細分。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable (μ : Cardinal.{u})
    {C : SSet.{u + 1}} [Quasicategory C] {A₀ A₁ : Type u}
    [Preorder A₀] [Preorder A₁]
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₀) ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₁) ⟶ C}
    (c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀) (c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁) (hv : c₀.vertex = c₁.vertex)

/-- 元の二つの小部分表示が、共通頂点の上で同型な余極限を持つ条件。 -/
def IsCompatiblePresentationPiece (P : Set A₀ × Set A₁) : Prop :=
  HasCardinalLT P.1 μ ∧ HasCardinalLT P.2 μ ∧ IsFiltered P.1 ∧ IsFiltered P.2 ∧
  ∃ a₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion P.1)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSliceDiagram c₀),
    ∃ a₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion P.2)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transportedCoconeSliceDiagram c₁ c₀.vertex hv.symm),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a₀ ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a₁ ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso a₀.vertex a₁.vertex)

/-- 比較可能な小部分表示の対。順序は元の両部分集合の包含順である。 -/
def CompatiblePresentationPieces :=
  {P : Set A₀ × Set A₁ // _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCompatiblePresentationPiece μ c₀ c₁ hv P}

instance compatiblePresentationPieces_preorder :
    Preorder (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePresentationPieces μ c₀ c₁ hv) := inferInstanceAs
  (Preorder {P : Set A₀ × Set A₁ // _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCompatiblePresentationPiece μ c₀ c₁ hv P})

/-- 指定した小部分表示比較は、同じ実部分集合の比較対を与える。 -/
def SmallPresentationComparison.toCompatiblePiece
    {seed₀ : Set A₀} {seed₁ : Set A₁}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPresentationComparison μ c₀ c₁ hv seed₀ seed₁) :
    CompatiblePresentationPieces μ c₀ c₁ hv :=
  ⟨(s.leftPiece, s.rightPiece), s.left_small, s.right_small, s.left_filtered,
    s.right_filtered, s.leftCocone, s.rightCocone, s.left_colimit, s.right_colimit,
    ⟨s.comparison⟩⟩

variable [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    [IsCardinalFiltered A₀ μ] [IsCardinalFiltered A₁ μ]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (nerve A₀)] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (nerve A₁)]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hc₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₀) (hc₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₁)
    (hD₀ : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
    (hD₁ : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))

include hμ hC hc₀ hc₁ hD₀ hD₁

/-- 両側の任意の小さい種集合を含む、比較可能な実部分表示の対が存在する。 -/
lemma exists_compatiblePresentationPiece_containing
    (seed₀ : Set A₀) (hs₀ : HasCardinalLT seed₀ μ)
    (seed₁ : Set A₁) (hs₁ : HasCardinalLT seed₁ μ) :
    ∃ P : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePresentationPieces μ c₀ c₁ hv,
      seed₀ ⊆ P.val.1 ∧ seed₁ ⊆ P.val.2 := by
  obtain ⟨s⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nonempty_smallPresentationComparison hμ D₀ D₁ c₀ c₁
    hC hc₀ hc₁ hD₀ hD₁ hv seed₀ hs₀ seed₁ hs₁
  exact ⟨s.toCompatiblePiece μ c₀ c₁ hv, s.left_seed, s.right_seed⟩

/-- 同じ共通頂点上で比較可能な小部分表示の対は μ-filtered な包含順をなす。 -/
lemma compatiblePresentationPieces_isCardinalFiltered :
    IsCardinalFiltered (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePresentationPieces μ c₀ c₁ hv) μ := by
  apply isCardinalFiltered_preorder
  intro K f hK
  have hK' : HasCardinalLT K μ := (hasCardinalLT_iff_cardinal_mk_lt K μ).mpr hK
  have h₀ : HasCardinalLT (⋃ k, (f k).val.1) μ :=
    hasCardinalLT_iUnion _ hK' (fun k ↦ (f k).property.1)
  have h₁ : HasCardinalLT (⋃ k, (f k).val.2) μ :=
    hasCardinalLT_iUnion _ hK' (fun k ↦ (f k).property.2.1)
  obtain ⟨P, hP₀, hP₁⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_compatiblePresentationPiece_containing μ c₀ c₁ hv
    hμ hC hc₀ hc₁ hD₀ hD₁ _ h₀ _ h₁
  exact ⟨P, fun k ↦ ⟨(Set.subset_iUnion _ k).trans hP₀,
    (Set.subset_iUnion _ k).trans hP₁⟩⟩

/-- 元の比較可能な対の nerve は全 μ-small 図式について μ-filtered。 -/
lemma compatiblePresentationPieces_nerve_isKappaFiltered :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (nerve (CompatiblePresentationPieces μ c₀ c₁ hv)) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compatiblePresentationPieces_isCardinalFiltered μ c₀ c₁ hv hμ hC hc₀ hc₁ hD₀ hD₁
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
