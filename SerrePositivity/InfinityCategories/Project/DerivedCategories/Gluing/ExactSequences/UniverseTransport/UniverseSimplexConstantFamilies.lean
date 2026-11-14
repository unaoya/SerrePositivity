module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.UniverseTransport.UniverseSimplexFamilies

/-! パラメーターに定値な標準単体族の宇宙移送は、同じ単体の持ち上げそのもの。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

lemma dgGluingUliftSimplexFamily_constant {K X : SSet.{u}} {n : ℕ} (s : X _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{u, v} n
        (fst (Δ[n] : SSet.{u}) K ≫ SSet.yonedaEquiv.symm s) =
      fst (Δ[n] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K) ≫
        SSet.yonedaEquiv.symm (ULift.up s) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
