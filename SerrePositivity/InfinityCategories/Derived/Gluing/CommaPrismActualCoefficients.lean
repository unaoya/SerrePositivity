module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPrismCorrectionEdge
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugPrismSimplex

/-! 同じ実 prism 単体の混合相係数を、主項と全補正和へ厳密に回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {n : ℕ} (s : Simplex R (DGFunctorCommaObject R C E F) n)

lemma dgGluingCommaPrismActual_mixed (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1) :
    HEq ((dgCommaAugmentationPrismSimplex R C E F s β).hom I a b k hI ha hb hk)
      (dgGluingCommaPrismMainCoefficient R C E F s.toSimplexData I a b k hI ha hb hk +
        dgGluingCommaPrismCorrectionSum R C E F s.toSimplexData β I a b k hI ha hb hk) := by
  exact (dgCommaAugmentationPrismData_hom_mixed R C E F s.toSimplexData β
    I a b k hI ha hb hk hpa hpb).trans
      (heq_of_eq (dgGluingCommaPrismMixedCoefficient_eq R C E F s.toSimplexData β
        I a b k hI ha hb hk))

lemma dgGluingCommaPrismActual_mixed_card_two (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1) (hc : I.card = 2) :
    HEq ((dgCommaAugmentationPrismSimplex R C E F s β).hom I a b k hI ha hb hk)
      (dgGluingCommaPrismMainCoefficient R C E F s.toSimplexData I a b k hI ha hb hk) := by
  exact (dgCommaAugmentationPrismData_hom_mixed R C E F s.toSimplexData β
    I a b k hI ha hb hk hpa hpb).trans
      (heq_of_eq (dgGluingCommaPrismMixedCoefficient_card_two R C E F s.toSimplexData β
        I a b k hI ha hb hk hc))

end SerrePositivity.InfinityCategories
