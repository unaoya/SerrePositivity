module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilySquare

/-! 区間 Hom 族の同じ実ホモトピーを、全区間評価後も保持する。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

def dgGluingIntervalUncurryHomotopy {K X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y} (H : SSet.Homotopy f g) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry g) where
  h := (α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry H.h
  h₀ := by
    have hi : (SSet.ι₀ : (Δ[1] : SSet.{u}) ⊗ K ⟶ _) ≫
        (α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).hom =
      (Δ[1] : SSet.{u}) ◁ (SSet.ι₀ : K ⟶ _) := rfl
    rw [← Category.assoc, hi, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, H.h₀]
    rfl
  h₁ := by
    have hi : (SSet.ι₁ : (Δ[1] : SSet.{u}) ⊗ K ⟶ _) ≫
        (α_ (Δ[1] : SSet.{u}) K (Δ[1] : SSet.{u})).hom =
      (Δ[1] : SSet.{u}) ◁ (SSet.ι₁ : K ⟶ _) := rfl
    rw [← Category.assoc, hi, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, H.h₁]
    rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
