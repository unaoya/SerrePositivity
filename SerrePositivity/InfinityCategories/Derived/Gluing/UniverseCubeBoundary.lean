module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseCubeFamilies

/-! 持ち上げた cube を別宇宙の元 Hom から制限しても、三方向の各面は同じ元の面の制限。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
variable {K X : SSet.{u}} {P : SSet.{max u v}}
  (h : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ K)) ⟶ X)
  (a : P ⟶ (SSet.uliftFunctor.{v, u}).obj K)

lemma dgGluingUliftCubeFamily_outer_precomp (i : Fin 2) :
    prismEndpoint i _ ≫ (Δ[1] ◁ (Δ[1] ◁ (Δ[1] ◁ a))) ≫
        dgGluingUliftCubeFamily.{u, v} h =
      (Δ[1] ◁ (Δ[1] ◁ a)) ≫
        dgGluingUliftSquareFamily.{u, v} (prismEndpoint i _ ≫ h) := by
  have he : prismEndpoint i _ ≫ (Δ[1] ◁ (Δ[1] ◁ (Δ[1] ◁ a))) =
      (Δ[1] ◁ (Δ[1] ◁ a)) ≫ prismEndpoint i _ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  rw [← Category.assoc, he, Category.assoc, dgGluingUliftCubeFamily_outer]

lemma dgGluingUliftCubeFamily_middle_precomp (i : Fin 2) :
    (Δ[1] ◁ prismEndpoint i _) ≫ (Δ[1] ◁ (Δ[1] ◁ (Δ[1] ◁ a))) ≫
        dgGluingUliftCubeFamily.{u, v} h =
      (Δ[1] ◁ (Δ[1] ◁ a)) ≫
        dgGluingUliftSquareFamily.{u, v} ((Δ[1] ◁ prismEndpoint i _) ≫ h) := by
  have he : (Δ[1] ◁ prismEndpoint i _) ≫ (Δ[1] ◁ (Δ[1] ◁ (Δ[1] ◁ a))) =
      (Δ[1] ◁ (Δ[1] ◁ a)) ≫ (Δ[1] ◁ prismEndpoint i _) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  rw [← Category.assoc, he, Category.assoc, dgGluingUliftCubeFamily_middle]

lemma dgGluingUliftCubeFamily_inner_precomp (i : Fin 2) :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint i _)) ≫ (Δ[1] ◁ (Δ[1] ◁ (Δ[1] ◁ a))) ≫
        dgGluingUliftCubeFamily.{u, v} h =
      (Δ[1] ◁ (Δ[1] ◁ a)) ≫
        dgGluingUliftSquareFamily.{u, v} ((Δ[1] ◁ (Δ[1] ◁ prismEndpoint i _)) ≫ h) := by
  have he : (Δ[1] ◁ (Δ[1] ◁ prismEndpoint i _)) ≫ (Δ[1] ◁ (Δ[1] ◁ (Δ[1] ◁ a))) =
      (Δ[1] ◁ (Δ[1] ◁ a)) ≫ (Δ[1] ◁ (Δ[1] ◁ prismEndpoint i _)) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  rw [← Category.assoc, he, Category.assoc, dgGluingUliftCubeFamily_inner]

end SerrePositivity.InfinityCategories
