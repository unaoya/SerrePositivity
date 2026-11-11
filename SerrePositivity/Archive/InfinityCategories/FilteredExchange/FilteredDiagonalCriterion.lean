module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.FilteredDiagonalCofinality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.WeakContractibilityNonempty

/-!
概要：filtered 性と κ-filtered 性を coslice の弱可縮性・対角関手の cofinality で特徴付ける。
方針：十分性には coslice の非空性から元の余錐を回収し、必要性には構成済みの弱可縮性を使う。
規約：一般の有限・κ-small な単体集合の図式を試験する。
使われ方：Kerodon 9.1.1.18（Tag 02PJ）、filtered 余極限の添字の変更。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：filtered 性は全ての有限図式の coslice の弱可縮性と同値。
方針：必要性は有限 coslice の filtered 性、十分性は弱可縮な coslice の頂点。
規約：Kan 性を coslice に要求しない。使われ方：filtered 性の空間的判定。 -/
lemma isFilteredInfinity_iff_weaklyContractible_coslices (C : SSet.{u}) [Quasicategory C] :
    IsFilteredInfinity C ↔ ∀ (K : SSet.{u}) [K.Finite] (p : K ⟶ C),
      IsWeaklyContractible (sliceUnder p) := by
  constructor
  · intro _ _ _ p
    exact isWeaklyContractible_sliceUnder_of_filtered p
  · intro h
    exact ⟨fun {K} _ p ↦ nonempty_of_isWeaklyContractible (h K p)⟩

/-- 概要：正則 κ の κ-filtered 性は κ-small な図式の coslice の弱可縮性と同値。
方針：κ 版 coslice の弱可縮性と頂点の存在を組み合わせる。
規約：κ の正則性を明示する。使われ方：Indκ の添字の判定。 -/
lemma isKappaFiltered_iff_weaklyContractible_coslices {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (C : SSet.{u}) [Quasicategory C] :
    IsKappaFiltered κ C ↔ ∀ (K : SSet.{u}), IsKappaSmall κ K →
      ∀ p : K ⟶ C, IsWeaklyContractible (sliceUnder p) := by
  constructor
  · intro _ _ hK p
    exact isWeaklyContractible_sliceUnder_of_kappaFiltered hκ hK p
  · intro h
    exact ⟨fun {K} hK p ↦ nonempty_of_isWeaklyContractible (h K hK p)⟩

/-- 概要：filtered ∞ 圏は有限形状への全ての対角関手が right cofinal なものに等しい。
方針：coslice の弱可縮性の判定を対角関手の標準 comma の判定と合成する。
規約：有限形状の quasicategory 性は不要。使われ方：Kerodon 9.1.1.18（Tag 02PJ）。 -/
lemma isFilteredInfinity_iff_constantDiagram_rightCofinal (C : SSet.{u}) [Quasicategory C] :
    IsFilteredInfinity C ↔ ∀ (K : SSet.{u}) [K.Finite],
      IsRightCofinal (constantDiagram K C) := by
  rw [isFilteredInfinity_iff_weaklyContractible_coslices]
  constructor
  · intro h K _
    exact (isRightCofinal_constantDiagram_iff K C).2 (h K)
  · intro h K _
    exact (isRightCofinal_constantDiagram_iff K C).1 (h K)

/-- 概要：κ-filtered 性は κ-small な全ての形状への対角関手の right cofinality と同値。
方針：κ-small な coslice の弱可縮性の判定に Quillen A を合成する。
規約：正則 κ に対する一般の coherent な図式。使われ方：κ 版の対角判定。 -/
lemma isKappaFiltered_iff_constantDiagram_rightCofinal {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (C : SSet.{u}) [Quasicategory C] :
    IsKappaFiltered κ C ↔ ∀ (K : SSet.{u}), IsKappaSmall κ K →
      IsRightCofinal (constantDiagram K C) := by
  rw [isKappaFiltered_iff_weaklyContractible_coslices hκ]
  constructor
  · intro h K hK
    exact (isRightCofinal_constantDiagram_iff K C).2 (h K hK)
  · intro h K hK
    exact (isRightCofinal_constantDiagram_iff K C).1 (h K hK)

end SerrePositivity.InfinityCategories.F2
