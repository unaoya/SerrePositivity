module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.KappaRelativeFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import Mathlib.AlgebraicTopology.Quasicategory.Basic

/-!
概要：通常の κ-filtered 図式の実際の単体集合余極限で、各段の κ-filtered 性を保つ。
方針：ホーンの有限表示性で quasicategory 性を示し、κ-small な図式を一段へ下ろして余錐を送る。
規約：通常の strict 余極限についての主張。coherent な前層余極限との比較は別工程。
使われ方：元の元の圏の κ-filtered 余極限閉性への入力。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 元の quasicategory の通常の filtered 余極限も quasicategory。 -/
lemma quasicategory_of_filtered_isColimit
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ SSet.{u}} [∀ i, Quasicategory (F.obj i)] {c : Cocone F}
    (hc : IsColimit c) : Quasicategory c.pt where
  hornFilling' {n i} a h₀ hlast := by
    obtain ⟨j, t, ht⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc a
    obtain ⟨g, hg⟩ := Quasicategory.hornFilling h₀ hlast t
    exact ⟨g ≫ c.ι.app j, ht.symm.trans (by rw [hg, Category.assoc])⟩

/-- 同じ通常の κ-filtered 余極限は、元の各段の κ-filtered 性を保つ。 -/
lemma isKappaFiltered_of_strict_isColimit
    {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {I : Type u} [SmallCategory I] [IsCardinalFiltered I κ]
    {F : I ⥤ SSet.{u}} [∀ i, Quasicategory (F.obj i)] [∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (F.obj i)]
    {c : Cocone F} [Quasicategory c.pt] (hc : IsColimit c) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ c.pt where
  cocone_nonempty hK f := by
    obtain ⟨j, g, hg⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.kappaSmall_factorization_of_isColimit hc hK f
    obtain ⟨d⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered.cocone_nonempty hK g
    refine ⟨⟨d.val ≫ c.ι.app j, ?_⟩⟩
    rw [← Category.assoc, d.property, hg]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
