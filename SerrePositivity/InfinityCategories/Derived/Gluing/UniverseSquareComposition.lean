module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseCubeFamilies

/-! 二重区間族の宇宙移送は、内側区間の評価と外側 prism の実合成を保つ。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

lemma dgGluingUliftSquareFamily_comp {K L X : SSet.{u}}
    (p : (Δ[1] : SSet.{u}) ⊗ K ⟶ L) (V : (Δ[1] : SSet.{u}) ⊗ L ⟶ X) :
    dgGluingUliftSquareFamily.{u, v} ((Δ[1] ◁ p) ≫ V) =
      (Δ[1] ◁ dgGluingUliftSimplexFamily.{u, v} 1 p) ≫
        dgGluingUliftSimplexFamily.{u, v} 1 V := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingUliftSquareFamily_post {K X Y : SSet.{u}}
    (V : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ K) ⟶ X) (q : X ⟶ Y) :
    dgGluingUliftSquareFamily.{u, v} V ≫ (SSet.uliftFunctor.{v, u}).map q =
      dgGluingUliftSquareFamily.{u, v} (V ≫ q) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end SerrePositivity.InfinityCategories
