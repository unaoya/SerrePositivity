module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.UniverseTransport.UniverseCubeFamilies

/-! pinched prism の区間評価を、二つの時間と全入力を保つ四角形として束ねる。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
variable {K L X : SSet.{u}}

def dgGluingPrismIntervalSquare (h : (Δ[1] : SSet.{u}) ⊗ K ⟶ L)
    (e : (Δ[1] : SSet.{u}) ⊗ L ⟶ X) :
    (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ K) ⟶ X :=
  (α_ (Δ[1] : SSet.{u}) Δ[1] K).inv ≫
    ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ▷ K) ≫
      (α_ (Δ[1] : SSet.{u}) Δ[1] K).hom ≫ (Δ[1] ◁ h) ≫ e

lemma dgGluingPrismIntervalSquare_precomp {P : SSet.{u}}
    (h : (Δ[1] : SSet.{u}) ⊗ K ⟶ L) (e : (Δ[1] : SSet.{u}) ⊗ L ⟶ X) (f : P ⟶ K) :
    (Δ[1] ◁ (Δ[1] ◁ f)) ≫ dgGluingPrismIntervalSquare h e =
      dgGluingPrismIntervalSquare ((Δ[1] ◁ f) ≫ h) e := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingPrismIntervalSquare_post {Y : SSet.{u}}
    (h : (Δ[1] : SSet.{u}) ⊗ K ⟶ L) (e : (Δ[1] : SSet.{u}) ⊗ L ⟶ X) (f : X ⟶ Y) :
    dgGluingPrismIntervalSquare h e ≫ f = dgGluingPrismIntervalSquare h (e ≫ f) := by
  simp only [dgGluingPrismIntervalSquare, Category.assoc]

lemma dgGluingUliftPrismIntervalSquare
    (h : (Δ[1] : SSet.{u}) ⊗ K ⟶ L) (e : (Δ[1] : SSet.{u}) ⊗ L ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSquareFamily.{u, v} (dgGluingPrismIntervalSquare h e) =
      dgGluingPrismIntervalSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{u, v} 1 h)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{u, v} 1 e) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
