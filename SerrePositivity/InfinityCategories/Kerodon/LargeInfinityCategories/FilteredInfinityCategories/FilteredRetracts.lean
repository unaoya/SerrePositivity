module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallSimplicialShapes

/-!
概要：filtered 性は単体集合の厳密な retract と同型で保たれる。
方針：図式を包含側で送り、得た余錐を retraction で戻す。
規約：通常の圏の nerve に限定せず、全ての試験図式を保持する。
使われ方：filtered 添字の表示変更と後続の同値不変性の基礎。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：filtered な ∞ 圏の厳密な retract は filtered。
方針：包含後の図式の余錐を射影で戻し、厳密な retract の等式で制限を照合する。
規約：ホモトピー retract の主張とは区別する。
使われ方：同型な filtered 添字の変更。 -/
lemma isFilteredInfinity_of_retract {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C] (i : D ⟶ C) (r : C ⟶ D) (h : i ≫ r = 𝟙 D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity D where
  cocone_nonempty f := by
    obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity.cocone_nonempty (f ≫ i)
    exact ⟨⟨c.val ≫ r, by
      rw [← Category.assoc, c.property, Category.assoc, h, Category.comp_id]⟩⟩

/-- 概要：κ-filtered な ∞ 圏の厳密な retract は κ-filtered。
方針：元の κ-small な形状を保って余錐を送って戻す。
規約：濃度の正則性をこの輸送には使わない。
使われ方：κ-filtered 添字の同型不変性。 -/
lemma isKappaFiltered_of_retract {κ : Cardinal.{u}} {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C]
    (i : D ⟶ C) (r : C ⟶ D) (h : i ≫ r = 𝟙 D) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ D where
  cocone_nonempty hK f := by
    obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered.cocone_nonempty hK (f ≫ i)
    exact ⟨⟨c.val ≫ r, by
      rw [← Category.assoc, c.property, Category.assoc, h, Category.comp_id]⟩⟩

/-- 概要：同型な ∞ 圏は filtered 性を共有する。
方針：同型の両向きを厳密な retract として用いる。
規約：単体集合の同型についての主張。使われ方：添字の表示の変更。 -/
lemma isFilteredInfinity_iff_of_iso {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (e : C ≅ D) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity D := by
  constructor
  · intro h
    exact isFilteredInfinity_of_retract e.inv e.hom e.inv_hom_id
  · intro h
    exact isFilteredInfinity_of_retract e.hom e.inv e.hom_inv_id

/-- 概要：同型な ∞ 圏は κ-filtered 性を共有する。
方針：同型の両向きで retract による輸送を適用する。
規約：同じ κ と同じ宇宙で比較する。使われ方：κ-filtered 添字の表示の変更。 -/
lemma isKappaFiltered_iff_of_iso {κ : Cardinal.{u}} {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (e : C ≅ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ D := by
  constructor
  · intro h
    exact isKappaFiltered_of_retract e.inv e.hom e.inv_hom_id
  · intro h
    exact isKappaFiltered_of_retract e.hom e.inv e.hom_inv_id

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
