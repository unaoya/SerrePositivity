module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaObject

/-! 恒等 comma の実 augmentation を元対象宇宙で評価し、全単体を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)

def dgGluingIdentityCommaAugmentationPrism :
    (Δ[1] : SSet.{max u v}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R Q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E where
  app _ := ↾fun a => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
    a.2 (stdSimplex.objEquiv a.1).toOrderHom
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro a
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex_pullback R E E (DGFunctor.id E) a.2
      α.unop.toOrderHom (stdSimplex.objEquiv a.1).toOrderHom)

lemma dgGluingIdentityCommaAugmentationPrism_evaluate {n : ℕ}
    (β : (Δ[1] : SSet.{max u v}) _⦋n⦌) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R Q n) :
    (dgGluingIdentityCommaAugmentationPrism R E).app (Opposite.op ⦋n⦌) (β, s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) s
        (stdSimplex.objEquiv β).toOrderHom := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
