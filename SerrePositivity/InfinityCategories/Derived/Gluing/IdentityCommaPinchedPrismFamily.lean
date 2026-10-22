module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPinchedPrism

/-! 同じ実 augmentation の全 pinched Hom prism を面・退化に自然な区間族へ束ねる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]

def dgGluingIdentityCommaPinchedPrism (x y : E) :
    (Δ[1] : SSet.{max u v}) ⊗ DGNerve.pinchedHom R
        (DGFunctorCommaObject R E E (DGFunctor.id E))
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) ⟶
      DGNerve.pinchedHom R E x y where
  app d := ↾fun a => dgGluingIdentityCommaPinchedPrismSimplex R E a.2
    (stdSimplex.objEquiv a.1).toOrderHom
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro a
    exact (dgGluingIdentityCommaPinchedPrismSimplex_naturality R E a.2 α.unop
      (stdSimplex.objEquiv a.1).toOrderHom).symm

lemma dgGluingIdentityCommaPinchedPrism_one_val {x y : E} {n : ℕ}
    (s : (DGNerve.pinchedHom R (DGFunctorCommaObject R E E (DGFunctor.id E))
      (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y)) _⦋n⦌) :
    ((prismEndpoint 1 _ ≫ dgGluingIdentityCommaPinchedPrism R E x y).app
      (Opposite.op ⦋n⦌) s).val =
        s.val.map (dgCommaAugmentationTarget R E E (DGFunctor.id E)) := by
  change dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) s.val
    (pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (1 : Fin 2))) = _
  rw [pinchedPrismPhase_one, dgCommaAugmentationPrismSimplex_one]

end SerrePositivity.InfinityCategories
