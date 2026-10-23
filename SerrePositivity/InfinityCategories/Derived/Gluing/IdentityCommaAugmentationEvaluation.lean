module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaObject

/-! 恒等 comma の実 augmentation を元対象宇宙で評価し、全単体を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)

def dgGluingIdentityCommaAugmentationPrism :
    (Δ[1] : SSet.{max u v}) ⊗ dgNerve R Q ⟶ dgNerve R E where
  app _ := ↾fun a => dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
    a.2 (stdSimplex.objEquiv a.1).toOrderHom
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro a
    exact (dgCommaAugmentationPrismSimplex_pullback R E E (DGFunctor.id E) a.2
      α.unop.toOrderHom (stdSimplex.objEquiv a.1).toOrderHom)

lemma dgGluingIdentityCommaAugmentationPrism_evaluate {n : ℕ}
    (β : (Δ[1] : SSet.{max u v}) _⦋n⦌) (s : Simplex R Q n) :
    (dgGluingIdentityCommaAugmentationPrism R E).app (Opposite.op ⦋n⦌) (β, s) =
      dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) s
        (stdSimplex.objEquiv β).toOrderHom := rfl

end SerrePositivity.InfinityCategories
