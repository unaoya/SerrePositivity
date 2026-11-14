module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.UniverseTransport.UniverseCubeFamilies

/-! 二重区間の全族のパラメータ制限を持ち上げ、異なる模型からの同じ実入力を保持する。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

lemma dgGluingUliftSquareFamily_precomp {K L X : SSet.{u}}
    (V : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ L) ⟶ X) (f : K ⟶ L) :
    (Δ[1] ◁ (Δ[1] ◁ (SSet.uliftFunctor.{v, u}).map f)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSquareFamily.{u, v} V =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSquareFamily.{u, v} ((Δ[1] ◁ (Δ[1] ◁ f)) ≫ V) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingUliftSquareFamily_reindex_eq {K N L X : SSet.{u}} {P : SSet.{max u v}}
    (V : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ L) ⟶ X) (c : K ⟶ L) (d : N ⟶ L)
    (e : P ⟶ (SSet.uliftFunctor.{v, u}).obj K)
    (t : P ⟶ (SSet.uliftFunctor.{v, u}).obj N)
    (he : e ≫ (SSet.uliftFunctor.{v, u}).map c = t ≫ (SSet.uliftFunctor.{v, u}).map d) :
    (Δ[1] ◁ (Δ[1] ◁ e)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSquareFamily.{u, v} ((Δ[1] ◁ (Δ[1] ◁ c)) ≫ V) =
      (Δ[1] ◁ (Δ[1] ◁ t)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSquareFamily.{u, v} ((Δ[1] ◁ (Δ[1] ◁ d)) ≫ V) := by
  rw [← dgGluingUliftSquareFamily_precomp, ← dgGluingUliftSquareFamily_precomp]
  have hh := congrArg (fun z : P ⟶ (SSet.uliftFunctor.{v, u}).obj L =>
    (Δ[1] ◁ (Δ[1] ◁ z)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSquareFamily.{u, v} V) he
  simpa only [whiskerLeft_comp, Category.assoc] using hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
