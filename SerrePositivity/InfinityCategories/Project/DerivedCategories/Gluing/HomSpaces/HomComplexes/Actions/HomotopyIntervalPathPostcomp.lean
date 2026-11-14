module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomotopyIntervalPath
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! 全区間族から読んだホモトピーを再び curry すると、同じ後合成した全 path を回収する。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial

lemma dgGluingHomotopyIntervalPath_postcomp {K X Y : SSet.{u}}
    (p : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyIntervalPath
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalPathHomotopy p) q) =
      p ≫ (ihom (Δ[1] : SSet.{u})).map q := by
  apply uncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyIntervalPath_uncurry, uncurry_natural_right]
  change (β_ (Δ[1] : SSet.{u}) K).hom ≫
    ((β_ K (Δ[1] : SSet.{u})).hom ≫ uncurry p) ≫ q = _
  rw [← Category.assoc, SymmetricCategory.symmetry_assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
