module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseCubeFamilies

/-! 二重区間族の宇宙移送は、内側区間の評価と外側 prism の実合成を保つ。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

lemma dgGluingUliftSquareFamily_comp {K L X : SSet.{u}}
    (p : (Δ[1] : SSet.{u}) ⊗ K ⟶ L) (V : (Δ[1] : SSet.{u}) ⊗ L ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSquareFamily.{u, v} ((Δ[1] ◁ p) ≫ V) =
      (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{u, v} 1 p) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{u, v} 1 V := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingUliftSquareFamily_post {K X Y : SSet.{u}}
    (V : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ K) ⟶ X) (q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSquareFamily.{u, v} V ≫ (SSet.uliftFunctor.{v, u}).map q =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSquareFamily.{u, v} (V ≫ q) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
