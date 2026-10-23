module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaTerminalPhase
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPinchedPrismFamily

/-! 恒等 comma の pinched prism の全切断評価は、元の全 augmentation 四角形と一致する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]

lemma dgGluingIdentityCommaPrismInterval_cut {x y : E} {n : ℕ}
    (s : (DGNerve.pinchedHom R (DGFunctorCommaObject R E E (DGFunctor.id E))
      (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y)) _⦋n⦌)
    (β t : Fin (n + 1) →o Fin 2) :
    (dgGluingIdentityCommaPinchedPrismSimplex R E s β).val.pullback (coherentPrismCut t) =
      dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
        (s.val.pullback (coherentPrismCut t)) β := by
  change (dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      s.val (pinchedPrismPhase β)).pullback (coherentPrismCut t) = _
  rw [← dgCommaAugmentationPrismSimplex_pullback, dgGluingPinchedPrismPhase_cut]
  apply Simplex.ext
  exact dgGluingIdentityCommaTerminalPhase_data R E s.val.toSimplexData y (target_obj s) β t

end SerrePositivity.InfinityCategories
