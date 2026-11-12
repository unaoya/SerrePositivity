module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseCubeFamilies

/-! 持ち上げた cube を別宇宙の元 Hom から制限しても、三方向の各面は同じ元の面の制限。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
variable {K X : SSet.{u}} {P : SSet.{max u v}}
  (h : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ K)) ⟶ X)
  (a : P ⟶ (SSet.uliftFunctor.{v, u}).obj K)

lemma dgGluingUliftCubeFamily_outer_precomp (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _ ≫ (Δ[1] ◁ (Δ[1] ◁ (Δ[1] ◁ a))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftCubeFamily.{u, v} h =
      (Δ[1] ◁ (Δ[1] ◁ a)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSquareFamily.{u, v} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _ ≫ h) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _ ≫ (Δ[1] ◁ (Δ[1] ◁ (Δ[1] ◁ a))) =
      (Δ[1] ◁ (Δ[1] ◁ a)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  rw [← Category.assoc, he, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftCubeFamily_outer]

lemma dgGluingUliftCubeFamily_middle_precomp (i : Fin 2) :
    (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _) ≫ (Δ[1] ◁ (Δ[1] ◁ (Δ[1] ◁ a))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftCubeFamily.{u, v} h =
      (Δ[1] ◁ (Δ[1] ◁ a)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSquareFamily.{u, v} ((Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _) ≫ h) := by
  have he : (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _) ≫ (Δ[1] ◁ (Δ[1] ◁ (Δ[1] ◁ a))) =
      (Δ[1] ◁ (Δ[1] ◁ a)) ≫ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  rw [← Category.assoc, he, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftCubeFamily_middle]

lemma dgGluingUliftCubeFamily_inner_precomp (i : Fin 2) :
    (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _)) ≫ (Δ[1] ◁ (Δ[1] ◁ (Δ[1] ◁ a))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftCubeFamily.{u, v} h =
      (Δ[1] ◁ (Δ[1] ◁ a)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSquareFamily.{u, v} ((Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _)) ≫ h) := by
  have he : (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _)) ≫ (Δ[1] ◁ (Δ[1] ◁ (Δ[1] ◁ a))) =
      (Δ[1] ◁ (Δ[1] ◁ a)) ≫ (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _)) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  rw [← Category.assoc, he, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftCubeFamily_inner]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
