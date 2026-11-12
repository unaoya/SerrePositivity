module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle

/-! 指定した全三辺を持つ具体的な二単体族を、そのまま関手合成三角形に curry する。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
variable {K X : SSet.{u}} {a b c : K ⟶ X}
  (l : SSet.Homotopy a b) (r : SSet.Homotopy b c) (d : SSet.Homotopy a c)
  (V : (Δ[2] : SSet.{u}) ⊗ K ⟶ X)
  (h₀ : (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ V = (β_ (Δ[1] : SSet.{u}) K).hom ≫ r.h)
  (h₁ : (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ V = (β_ (Δ[1] : SSet.{u}) K).hom ≫ d.h)
  (h₂ : (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ V = (β_ (Δ[1] : SSet.{u}) K).hom ≫ l.h)

def dgGluingFunctorTriangleOfFamily : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d where
  diagram := curry ((β_ K (Δ[2] : SSet.{u})).hom ≫ V)
  face_zero := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry]
    have hn : (K ◁ stdSimplex.δ (0 : Fin 3)) ≫ (β_ K (Δ[2] : SSet.{u})).hom =
      (β_ K (Δ[1] : SSet.{u})).hom ≫ (stdSimplex.δ (0 : Fin 3) ▷ K) := rfl
    rw [← Category.assoc, hn, Category.assoc, h₀, SymmetricCategory.symmetry_assoc]
  face_one := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry]
    have hn : (K ◁ stdSimplex.δ (1 : Fin 3)) ≫ (β_ K (Δ[2] : SSet.{u})).hom =
      (β_ K (Δ[1] : SSet.{u})).hom ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) := rfl
    rw [← Category.assoc, hn, Category.assoc, h₁, SymmetricCategory.symmetry_assoc]
  face_two := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry]
    have hn : (K ◁ stdSimplex.δ (2 : Fin 3)) ≫ (β_ K (Δ[2] : SSet.{u})).hom =
      (β_ K (Δ[1] : SSet.{u})).hom ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) := rfl
    rw [← Category.assoc, hn, Category.assoc, h₂, SymmetricCategory.symmetry_assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
