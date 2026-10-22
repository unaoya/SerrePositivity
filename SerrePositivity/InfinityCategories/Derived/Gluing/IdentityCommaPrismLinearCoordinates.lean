module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPinchedPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismZeroCoefficient
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorPinchedSimplex
public import SerrePositivity.InfinityCategories.DGNerve.HomHEqAlgebra

/-! 明示 prism の全線形成分を、同じ二射影と元の混合係数へ戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  {x y : E} {n : ℕ}
  (s : (DGNerve.pinchedHom R (DGFunctorCommaObject R E E (DGFunctor.id E))
    (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y)) _⦋n⦌)
  (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))

lemma dgGluingIdentityCommaPrism_component_one
    (β : Fin (n + 1) →o Fin 2) (hβ : β (J.min' hJ) = 1) :
    (toLinearData (dgGluingIdentityCommaPinchedPrismSimplex R E s β)).component J k hJ hk =
      ((dgCommaAugmentationTarget R E E (DGFunctor.id E)).map
          (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y)).f k
        ((toLinearData s).component J k hJ hk) := by
  apply eq_of_heq
  have ho := toLinearData_component_heq (dgGluingIdentityCommaPinchedPrismSimplex R E s β)
    J k hJ hk
  have hp := dgCommaAugmentationPrismData_hom_one R E E (DGFunctor.id E) s.val.toSimplexData
    (pinchedPrismPhase β) (withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
    (two_withLast hJ) (min_withLast hJ _) (max_withLast J _)
    (by rw [card_withLast]; omega) ((pinchedPrismPhase_castSucc β _).trans hβ)
    (pinchedPrismPhase_last β)
  exact ho.trans (hp.trans (dgGluingFunctor_map_component_heq
    (dgCommaAugmentationTarget R E E (DGFunctor.id E)) (source_obj s (J.min' hJ))
    (target_obj s) k (toLinearData_component_heq s J k hJ hk).symm))

lemma dgGluingIdentityCommaPrism_main_component :
    HEq (dgGluingCommaPrismMainCoefficient R E E (DGFunctor.id E) s.val.toSimplexData
        (withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
        (two_withLast hJ) (min_withLast hJ _) (max_withLast J _) (by rw [card_withLast]; omega))
      (((dgCommaAugmentationSource R E E (DGFunctor.id E)).map
          (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y)).f k
        ((toLinearData s).component J k hJ hk)) := by
  exact (dgGluingIdentityCommaPrismMain_target R E s.val.toSimplexData (withLast J)
    (J.min' hJ).castSucc (Fin.last (n + 1)) k (two_withLast hJ) (min_withLast hJ _)
    (max_withLast J _) (by rw [card_withLast]; omega) y (target_obj s)).trans
      (dgGluingFunctor_map_component_heq (dgCommaAugmentationSource R E E (DGFunctor.id E))
        (source_obj s (J.min' hJ)) (target_obj s) k
        (toLinearData_component_heq s J k hJ hk).symm)

lemma dgGluingIdentityCommaPrism_component_mixed
    (β : Fin (n + 1) →o Fin 2) (hβ : β (J.min' hJ) = 0) :
    HEq ((toLinearData (dgGluingIdentityCommaPinchedPrismSimplex R E s β)).component J k hJ hk)
      (dgCommaAugmentationPrismMixedHom R E E (DGFunctor.id E) s.val.toSimplexData
        (pinchedPrismPhase β) (withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
        (two_withLast hJ) (min_withLast hJ _) (max_withLast J _)
        (by rw [card_withLast]; omega)) := by
  exact (toLinearData_component_heq (dgGluingIdentityCommaPinchedPrismSimplex R E s β)
    J k hJ hk).trans (dgCommaAugmentationPrismData_hom_mixed R E E (DGFunctor.id E)
      s.val.toSimplexData (pinchedPrismPhase β) (withLast J) (J.min' hJ).castSucc
      (Fin.last (n + 1)) k (two_withLast hJ) (min_withLast hJ _) (max_withLast J _)
      (by rw [card_withLast]; omega) ((pinchedPrismPhase_castSucc β _).trans hβ)
      (pinchedPrismPhase_last β))

end SerrePositivity.InfinityCategories
