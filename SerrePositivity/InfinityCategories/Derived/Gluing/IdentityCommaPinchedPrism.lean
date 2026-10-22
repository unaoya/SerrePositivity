module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaObject
public import SerrePositivity.InfinityCategories.Derived.PinchedPrismPhase
public import SerrePositivity.InfinityCategories.DGNerve.PinchedComponents

/-! 恒等 augmentation の二対象間では、元の全 prism 自身が固定二端の pinched Hom に入る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom SSet MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  {x y : E} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGFunctorCommaObject R E E (DGFunctor.id E))
    (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y)) _⦋n⦌)

def dgGluingIdentityCommaPinchedPrismSimplex (β : Fin (n + 1) →o Fin 2) :
    (DGNerve.pinchedHom R E x y) _⦋n⦌ where
  val := dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) s.val (pinchedPrismPhase β)
  source := by
    change (dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) s.val
      (pinchedPrismPhase β)).pullback Fin.castSuccOrderEmb.toOrderHom = _
    have h := dgCommaAugmentationPrismSimplex_pullback R E E (DGFunctor.id E) s.val
      Fin.castSuccOrderEmb.toOrderHom (pinchedPrismPhase β)
    rw [pinchedPrismPhase_front] at h
    have hs : s.val.pullback Fin.castSuccOrderEmb.toOrderHom =
        InfinityCategories.PinchedHom.constant
          (X := dgNerve R (DGFunctorCommaObject R E E (DGFunctor.id E)))
          (Simplex.vertex (dgGluingIdentityCommaObject R E x)) n := s.source
    exact h.symm.trans ((congrArg (fun t =>
      dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) t β) hs).trans
      (dgGluingIdentityCommaPrism_constant R E x β))
  target := by
    apply (Simplex.vertexEquiv (A := R) (D := E)).injective
    change StrictNatTrans.phaseObj (dgCommaAugmentationSource R E E (DGFunctor.id E))
      (dgCommaAugmentationTarget R E E (DGFunctor.id E))
      (pinchedPrismPhase β (Fin.last (n + 1))) (s.val.obj (Fin.last (n + 1))) = y
    rw [pinchedPrismPhase_last, target_obj s]
    rfl

lemma dgGluingIdentityCommaPinchedPrismSimplex_naturality {m : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (β : Fin (n + 1) →o Fin 2) :
    (dgGluingIdentityCommaPinchedPrismSimplex R E s β).pullback α =
      dgGluingIdentityCommaPinchedPrismSimplex R E (s.pullback α) (β.comp α.toOrderHom) := by
  apply InfinityCategories.PinchedHom.Simplex.ext
  change (dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) s.val
      (pinchedPrismPhase β)).pullback (InfinityCategories.PinchedHom.extendOrderHom α.toOrderHom) =
    dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      (s.val.pullback (InfinityCategories.PinchedHom.extendOrderHom α.toOrderHom))
      (pinchedPrismPhase (β.comp α.toOrderHom))
  rw [pinchedPrismPhase_comp, dgCommaAugmentationPrismSimplex_pullback]

end SerrePositivity.InfinityCategories
