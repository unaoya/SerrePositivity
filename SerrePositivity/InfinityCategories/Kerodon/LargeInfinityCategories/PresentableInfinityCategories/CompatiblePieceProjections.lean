module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePresentationPieces
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.MonotoneNerveCofinality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces

/-!
概要：共通比較対から元の各小部分表示族への射影は right cofinal。
方針：指定部分集合を種として共通対を拡大し、directed poset の native 共終性を適用する。
規約：元の部分集合の包含関手を使う。使われ方：両余極限の同じ μ-filtered 添字での計算。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePieceProjections

variable {μ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {A₀ A₁ : Type u}
    [PartialOrder A₀] [PartialOrder A₁]
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₀) ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₁) ⟶ C}
    {c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀} {c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁} {hv : c₀.vertex = c₁.vertex}

local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩

/-- 同じ比較対の左側を、元の小さい filtered 部分集合として読む。 -/
def compatibleLeftPiece (P : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePresentationPieces μ c₀ c₁ hv) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ A₀ :=
  ⟨P.val.1, (isCardinalFiltered_aleph0_iff P.val.1).mpr P.property.2.2.1, P.property.1⟩

/-- 同じ比較対の右側を、元の小さい filtered 部分集合として読む。 -/
def compatibleRightPiece (P : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePresentationPieces μ c₀ c₁ hv) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ A₁ :=
  ⟨P.val.2, (isCardinalFiltered_aleph0_iff P.val.2).mpr P.property.2.2.2.1, P.property.2.1⟩

lemma compatibleLeftPiece_monotone : Monotone
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePieceProjections.compatibleLeftPiece (μ := μ) (c₀ := c₀) (c₁ := c₁) (hv := hv)) := fun _ _ h ↦ h.1

lemma compatibleRightPiece_monotone : Monotone
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePieceProjections.compatibleRightPiece (μ := μ) (c₀ := c₀) (c₁ := c₁) (hv := hv)) := fun _ _ h ↦ h.2

variable [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    [IsCardinalFiltered A₀ μ] [IsCardinalFiltered A₁ μ]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (nerve A₀)] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ (nerve A₁)]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hc₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₀) (hc₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₁)
    (hD₀ : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
    (hD₁ : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
include hμ hC hc₀ hc₁ hD₀ hD₁

/-- 左側の元の任意の小部分表示は、共通比較対の左側に含まれる。 -/
lemma compatibleLeftPiece_dominates (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ A₀) :
    ∃ P : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePresentationPieces μ c₀ c₁ hv, A ≤ compatibleLeftPiece P := by
  obtain ⟨P, hP, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_compatiblePresentationPiece_containing μ c₀ c₁ hv hμ
    hC hc₀ hc₁ hD₀ hD₁ A.val A.property.2 ∅
    (hasCardinalLT_of_finite _ _ hμ.le)
  exact ⟨P, hP⟩

/-- 右側の元の任意の小部分表示も、同じ比較対の右側に含まれる。 -/
lemma compatibleRightPiece_dominates (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ A₁) :
    ∃ P : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePresentationPieces μ c₀ c₁ hv, A ≤ compatibleRightPiece P := by
  obtain ⟨P, _, hP⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_compatiblePresentationPiece_containing μ c₀ c₁ hv hμ
    hC hc₀ hc₁ hD₀ hD₁ ∅ (hasCardinalLT_of_finite _ _ hμ.le) A.val A.property.2
  exact ⟨P, hP⟩

/-- 共通比較対から左側の小部分表示族への元の射影は native に right cofinal。 -/
lemma compatibleLeftPiece_nerve_isRightCofinal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePieceProjections.compatibleLeftPiece_monotone (μ := μ) (c₀ := c₀) (c₁ := c₁) (hv := hv)).functor) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compatiblePresentationPieces_isCardinalFiltered μ c₀ c₁ hv hμ hC hc₀ hc₁ hD₀ hD₁
  have : IsFiltered (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePresentationPieces μ c₀ c₁ hv) :=
    isFiltered_of_isCardinalFiltered _ μ
  have := IsFiltered.isDirectedOrder (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePresentationPieces μ c₀ c₁ hv)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.monotone_nerveMap_isRightCofinal compatibleLeftPiece_monotone
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePieceProjections.compatibleLeftPiece_dominates hμ hC hc₀ hc₁ hD₀ hD₁)

/-- 同じ共通比較対から右側の小部分表示族への元の射影も native に right cofinal。 -/
lemma compatibleRightPiece_nerve_isRightCofinal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePieceProjections.compatibleRightPiece_monotone (μ := μ) (c₀ := c₀) (c₁ := c₁) (hv := hv)).functor) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compatiblePresentationPieces_isCardinalFiltered μ c₀ c₁ hv hμ hC hc₀ hc₁ hD₀ hD₁
  have : IsFiltered (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePresentationPieces μ c₀ c₁ hv) :=
    isFiltered_of_isCardinalFiltered _ μ
  have := IsFiltered.isDirectedOrder (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePresentationPieces μ c₀ c₁ hv)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.monotone_nerveMap_isRightCofinal compatibleRightPiece_monotone
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePieceProjections.compatibleRightPiece_dominates hμ hC hc₀ hc₁ hD₀ hD₁)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompatiblePieceProjections
